import Leancremental
import Tests.Util

/-! Correctness tests for parallel stabilization (`parallel := true`). -/

namespace Leancremental
namespace Tests
namespace Parallel

-- Fan-out: one input, N map nodes at height 1.  All N are independent same-height
-- nodes and should be scheduled as a parallel batch.
def testFanOut : IO Unit := do
  let state ← State.create
  let x ← Var.create state 1
  let pairs ← (Array.range 8).mapM (fun i => do
    let node ← map (Var.watch x) (fun n => n + i)
    let obs ← observe node
    pure (i, obs))
  State.stabilize state true
  for (i, obs) in pairs do
    assertEq s!"fanout initial {i}" (← Observer.value! obs) (1 + i)
  Var.set x 10
  State.stabilize state true
  for (i, obs) in pairs do
    assertEq s!"fanout updated {i}" (← Observer.value! obs) (10 + i)

-- Diamond DAG: x → (a, b) → c.  With parallel := true, a and b (same height)
-- run in parallel; c runs after the barrier.
def testDiamond : IO Unit := do
  let state ← State.create
  let x ← Var.create state 3
  let a ← map (Var.watch x) (fun n => n + 1)
  let b ← map (Var.watch x) (fun n => n * 2)
  let c ← map2 a b (fun a b => a + b)
  let obs ← observe c
  State.stabilize state true
  assertEq "diamond initial" (← Observer.value! obs) 10  -- (3+1) + (3*2)
  Var.set x 5
  State.stabilize state true
  assertEq "diamond updated" (← Observer.value! obs) 16  -- (5+1) + (5*2)

-- Bind still works correctly when parallel stabilize is used.
def testParallelWithBind : IO Unit := do
  let state ← State.create
  let cond ← Var.create state true
  let left ← Var.create state 42
  let right ← Var.create state 99
  let leftMapped ← map (Var.watch left) (fun n => n * 2)
  let rightMapped ← map (Var.watch right) (fun n => n * 3)
  let selected ← ifThenElse (Var.watch cond) leftMapped rightMapped
  let obs ← observe selected
  State.stabilize state true
  assertEq "parallel bind initial (left)" (← Observer.value! obs) 84
  Var.set cond false
  State.stabilize state true
  assertEq "parallel bind switched (right)" (← Observer.value! obs) 297
  Var.set right 10
  State.stabilize state true
  assertEq "parallel bind right changed" (← Observer.value! obs) 30

-- Sequential and parallel stabilize agree on the same graph.
def testMatchesSequential : IO Unit := do
  let mkGraph : IO (State × Array (Observer Nat)) := do
    let state ← State.create
    let x ← Var.create state 7
    let obs ← (Array.range 6).mapM (fun i => do
      let node ← map2 (Var.watch x) (Var.watch x) (fun a b => a * i + b)
      observe node)
    pure (state, obs)
  let (seqState, seqObs) ← mkGraph
  let (parState, parObs) ← mkGraph
  State.stabilize seqState false
  State.stabilize parState true
  let pairs := seqObs.zip parObs
  for (i, (sObs, pObs)) in (Array.range pairs.size).zip pairs do
    let sv ← Observer.value! sObs
    let pv ← Observer.value! pObs
    assertEq s!"match {i}" sv pv

-- Parallel stabilize handles a wide tree (multiple levels of fan-out).
def testWideTree : IO Unit := do
  let state ← State.create
  let x ← Var.create state 2
  -- Level 0 (height 1): 4 map nodes watching x.
  let l0_0 ← map (Var.watch x) (fun n => n)
  let l0_1 ← map (Var.watch x) (fun n => n + 1)
  let l0_2 ← map (Var.watch x) (fun n => n + 2)
  let l0_3 ← map (Var.watch x) (fun n => n + 3)
  -- Level 1 (height 2): 4 pairwise sums.
  let l1_0 ← map2 l0_0 l0_1 (fun a b => a + b)
  let l1_1 ← map2 l0_1 l0_2 (fun a b => a + b)
  let l1_2 ← map2 l0_2 l0_3 (fun a b => a + b)
  let l1_3 ← map2 l0_3 l0_0 (fun a b => a + b)
  -- Sum all (height 3).
  let sumNode ← arrayFold state #[l1_0, l1_1, l1_2, l1_3] 0 (fun acc v => acc + v)
  let obs ← observe sumNode
  State.stabilize state true
  -- x=2: l0=[2,3,4,5]; l1=[5,7,9,7]; sum=28
  assertEq "wide tree initial" (← Observer.value! obs) 28
  Var.set x 1
  State.stabilize state true
  -- x=1: l0=[1,2,3,4]; l1=[3,5,7,5]; sum=20
  assertEq "wide tree updated" (← Observer.value! obs) 20

-- Sequential (parallel := false) and parallel (parallel := true) agree on a graph
-- that includes freeze and map nodes.
def testMixedKindsMatch : IO Unit := do
  let mkMixed : IO (State × Observer Nat) := do
    let state ← State.create
    let x ← Var.create state 5
    let doubled ← map (Var.watch x) (fun n => n * 2)
    let tripled ← map (Var.watch x) (fun n => n * 3)
    let combined ← map2 doubled tripled (fun a b => a + b)
    let frozen ← freeze combined
    let obs ← observe frozen
    pure (state, obs)
  let (s1, obs1) ← mkMixed
  let (s2, obs2) ← mkMixed
  State.stabilize s1 false
  State.stabilize s2 true
  assertEq "mixed kinds match" (← Observer.value! obs1) (← Observer.value! obs2)

-- Stress: 500 same-height map nodes with non-trivial compute, seq vs parallel,
-- repeated 10 times.  The per-node lambda does real arithmetic work so that
-- tasks cannot complete before the next one is even scheduled.
def testStress : IO Unit := do
  let n := 500
  let rounds := 10
  for round in [:rounds] do
    let (seqState, seqObs) ← mkStressGraph n (round + 1)
    let (parState, parObs) ← mkStressGraph n (round + 1)
    State.stabilize seqState false
    State.stabilize parState true
    for (sObs, pObs) in seqObs.zip parObs do
      let sv ← Observer.value! sObs
      let pv ← Observer.value! pObs
      if sv != pv then
        throw (IO.userError s!"stress round {round}: seq={sv} par={pv}")
where
  mkStressGraph (n : Nat) (seed : Nat) :
      IO (State × Array (Observer Nat)) := do
    let state ← State.create
    let x ← Var.create state seed
    let obs ← (Array.range n).mapM (fun i => do
      let node ← map (Var.watch x) (fun v =>
        -- non-trivial: compute v * i using repeated addition in a loop
        Id.run do
          let mut acc := 0
          for _ in [:i % 64 + 1] do
            acc := acc + v
          acc)
      observe node)
    pure (state, obs)

def runAll : IO Unit := do
  testFanOut
  testDiamond
  testParallelWithBind
  testMatchesSequential
  testWideTree
  testMixedKindsMatch
  testStress

end Parallel
end Tests
end Leancremental
