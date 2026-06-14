import Leancremental
import Tests.Util

/-! Executable examples for CONCURRENCY.md.

  Each function corresponds to a code snippet in that doc.  Running `runAll`
  through the test executable verifies that every snippet compiles and produces
  the expected result.
-/

namespace Leancremental
namespace Tests
namespace ConcurrencyExamples

-- Snippet: basic parallel stabilize call.
-- Two independent map nodes sit at the same height; parallel := true
-- schedules them as a concurrent batch.
def exBasicParallelStabilize : IO Unit := do
  let state ← State.create
  let x ← Var.create state 3
  let doubled ← map (Var.watch x) (fun n => n * 2)
  let tripled ← map (Var.watch x) (fun n => n * 3)
  let obs1 ← observe doubled
  let obs2 ← observe tripled
  State.stabilize state true
  assertEq "basic parallel doubled initial" (← Observer.value! obs1) 6
  assertEq "basic parallel tripled initial" (← Observer.value! obs2) 9
  Var.set x 5
  State.stabilize state true
  assertEq "basic parallel doubled updated" (← Observer.value! obs1) 10
  assertEq "basic parallel tripled updated" (← Observer.value! obs2) 15

-- Snippet: pure-function closures are safe by construction.
-- map / map2 / map3 / map4 / map5 take pure (α → β) closures, so they
-- cannot access shared IO state at all — no race is possible.
def exSafeClosures : IO Unit := do
  let state ← State.create
  let x ← Var.create state 7
  let even   ← map (Var.watch x) (fun n => n % 2 == 0)
  let square ← map (Var.watch x) (fun n => n * n)
  let cube   ← map (Var.watch x) (fun n => n * n * n)
  let obsEven   ← observe even
  let obsSquare ← observe square
  let obsCube   ← observe cube
  State.stabilize state true
  assertEq "safe closures even"   (← Observer.value! obsEven)   false
  assertEq "safe closures square" (← Observer.value! obsSquare) 49
  assertEq "safe closures cube"   (← Observer.value! obsCube)   343

-- Fills the map3/map4/map5 parallel-safe gap: all three are in isParallelSafe
-- but were not previously exercised in the parallel path.
def exMapN : IO Unit := do
  let state ← State.create
  let a ← Var.create state 1
  let b ← Var.create state 2
  let c ← Var.create state 3
  let d ← Var.create state 4
  let e ← Var.create state 5
  -- All nodes below sit at height 1 — same-height → parallel batch
  let sum3 ← map3 (Var.watch a) (Var.watch b) (Var.watch c)
    (fun a b c => a + b + c)
  let sum4 ← map4 (Var.watch a) (Var.watch b) (Var.watch c) (Var.watch d)
    (fun a b c d => a + b + c + d)
  let sum5 ← map5 (Var.watch a) (Var.watch b) (Var.watch c) (Var.watch d) (Var.watch e)
    (fun a b c d e => a + b + c + d + e)
  let obs3 ← observe sum3
  let obs4 ← observe sum4
  let obs5 ← observe sum5
  State.stabilize state true
  assertEq "mapN parallel sum3" (← Observer.value! obs3) 6
  assertEq "mapN parallel sum4" (← Observer.value! obs4) 10
  assertEq "mapN parallel sum5" (← Observer.value! obs5) 15
  Var.set a 10
  State.stabilize state true
  assertEq "mapN parallel sum3 updated" (← Observer.value! obs3) 15
  assertEq "mapN parallel sum4 updated" (← Observer.value! obs4) 19
  assertEq "mapN parallel sum5 updated" (← Observer.value! obs5) 24

-- stabilizeWithStats accepts the same parallel parameter as stabilize.
def exStabilizeWithStats : IO Unit := do
  let state ← State.create
  let x ← Var.create state 10
  let a ← map (Var.watch x) (fun n => n + 1)
  let b ← map (Var.watch x) (fun n => n + 2)
  let _ ← observe a
  let _ ← observe b
  let stats ← State.stabilizeWithStats state true
  assertEq "stabilizeWithStats parallel nodes visited" stats.nodesVisited 2

def runAll : IO Unit := do
  exBasicParallelStabilize
  exSafeClosures
  exMapN
  exStabilizeWithStats

end ConcurrencyExamples
end Tests
end Leancremental
