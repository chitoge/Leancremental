import Leancremental

/-!
Differential property harness for FR-8.

Generates ≥1,000 seeded random operation traces over Var/map graphs and
verifies after every stabilize that:
  (a) every observer's runtime value equals the pure reference interpreter's
      value for that node;
  (b) `checkInvariants` and `checkStableInvariants` raise no violations;
  (c) a second immediate stabilize visits 0 nodes (idempotence).

Deterministic seeds (splitmix64).  On failure the offending seed and the
failing step are printed before the test aborts.
-/

namespace Leancremental
namespace Tests
namespace PropHarness

/- ------------------------------------------------------------------ -/
/-  Splitmix64 PRNG                                                     -/
/- ------------------------------------------------------------------ -/

def smNext (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (s, z ^^^ (z >>> 31))

-- Generate a value in [0, n)  (n=0 → 0)
def smRange (s : UInt64) (n : UInt64) : UInt64 × UInt64 :=
  let (s', v) := smNext s
  (s', if n == 0 then 0 else v % n)

/- ------------------------------------------------------------------ -/
/-  Reference model (pure from-scratch evaluator)                       -/
/- ------------------------------------------------------------------ -/

inductive RefKind where
  | rVar  (value : Int)
  | rMap1 (dep : Nat) (fn : Int → Int)
  | rMap2 (dep1 dep2 : Nat) (fn : Int → Int → Int)

structure RefModel where
  nodes    : Array RefKind
  observed : Array Nat   -- indices of observed nodes

-- Evaluate node `idx` with explicit fuel.
def refEval (m : RefModel) (fuel : Nat) (idx : Nat) : Option Int :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match m.nodes[idx]? with
      | none              => none
      | some (.rVar v)    => some v
      | some (.rMap1 dep f)      => (refEval m fuel dep).map f
      | some (.rMap2 d1 d2 f)    =>
          match refEval m fuel d1, refEval m fuel d2 with
          | some v1, some v2 => some (f v1 v2)
          | _, _             => none

/- ------------------------------------------------------------------ -/
/-  Map function table (small, deterministic)                            -/
/- ------------------------------------------------------------------ -/

def applyFn1 (tag : UInt64) (v : Int) : Int :=
  match tag % 4 with
  | 0 => v * 2
  | 1 => v + 1
  | 2 => v - 3
  | _ => v * v % 1000

def applyFn2 (tag : UInt64) (a b : Int) : Int :=
  match tag % 3 with
  | 0 => a + b
  | 1 => a - b
  | _ => a * b % 1000

/- ------------------------------------------------------------------ -/
/-  Harness state                                                        -/
/- ------------------------------------------------------------------ -/

inductive NodeHandle where
  | incr (n : Incr Int)
  | hVar  (v : Var Int) (n : Incr Int)

def nodeIncr : NodeHandle → Incr Int
  | .incr n     => n
  | .hVar _ n   => n

-- Collect indices of var handles.
def varIndices (handles : Array NodeHandle) : Array Nat :=
  Id.run do
    let mut out : Array Nat := #[]
    for i in [:handles.size] do
      match handles[i]? with
      | some (.hVar _ _) => out := out.push i
      | _                => pure ()
    return out

structure HarnessState where
  rtState  : State
  refModel : RefModel
  handles  : Array NodeHandle
  observed : Array (Observer Int)

/- ------------------------------------------------------------------ -/
/-  Step operations                                                      -/
/- ------------------------------------------------------------------ -/

def opCreateVar (hs : HarnessState) (value : Int) : IO HarnessState := do
  let v <- Var.create hs.rtState value
  let n := Var.watch v
  pure { hs with
    refModel := { hs.refModel with nodes := hs.refModel.nodes.push (.rVar value) },
    handles  := hs.handles.push (.hVar v n) }

def opCreateMap1 (hs : HarnessState) (r0 r1 : UInt64) : IO HarnessState := do
  if hs.handles.isEmpty then return hs
  let srcIdx := (r0 % hs.handles.size.toUInt64).toNat
  match hs.handles[srcIdx]? with
  | none => return hs
  | some srcH =>
      let n <- map (nodeIncr srcH) (applyFn1 r1)
      return { hs with
        refModel := { hs.refModel with nodes := hs.refModel.nodes.push (.rMap1 srcIdx (applyFn1 r1)) },
        handles  := hs.handles.push (.incr n) }

def opCreateMap2 (hs : HarnessState) (r0 r1 r2 : UInt64) : IO HarnessState := do
  if hs.handles.size < 2 then return hs
  let sz   := hs.handles.size.toUInt64
  let idx1 := (r0 % sz).toNat
  let idx2 := (r1 % sz).toNat
  match hs.handles[idx1]?, hs.handles[idx2]? with
  | some h1, some h2 =>
      let n <- map2 (nodeIncr h1) (nodeIncr h2) (applyFn2 r2)
      return { hs with
        refModel := { hs.refModel with nodes := hs.refModel.nodes.push (.rMap2 idx1 idx2 (applyFn2 r2)) },
        handles  := hs.handles.push (.incr n) }
  | _, _ => return hs

def opSetVar (hs : HarnessState) (r0 : UInt64) (value : Int) : IO HarnessState := do
  let vars := varIndices hs.handles
  if vars.isEmpty then return hs
  let slot := (r0 % vars.size.toUInt64).toNat
  let some nodeIdx := vars[slot]? | return hs
  match hs.handles[nodeIdx]? with
  | some (NodeHandle.hVar v _) =>
      Var.set v value
      let nodes' := hs.refModel.nodes.set! nodeIdx (.rVar value)
      return { hs with refModel := { hs.refModel with nodes := nodes' } }
  | _ => return hs

def opObserve (hs : HarnessState) (r0 : UInt64) : IO HarnessState := do
  if hs.handles.isEmpty then return hs
  let nodeIdx := (r0 % hs.handles.size.toUInt64).toNat
  if hs.refModel.observed.contains nodeIdx then return hs
  match hs.handles[nodeIdx]? with
  | none => return hs
  | some h =>
      let obs <- Observer.observe (nodeIncr h)
      return { hs with
        refModel := { hs.refModel with observed := hs.refModel.observed.push nodeIdx },
        observed := hs.observed.push obs }

def opMarkStale (hs : HarnessState) (r0 : UInt64) : IO HarnessState := do
  if hs.handles.isEmpty then return hs
  let idx := (r0 % hs.handles.size.toUInt64).toNat
  match hs.handles[idx]? with
  | some h => Incr.markStale (nodeIncr h)
  | none   => pure ()
  return hs

-- Stabilize and check all properties.
def opStabilize (hs : HarnessState) (seed : UInt64) (step : Nat) : IO HarnessState := do
  State.stabilize hs.rtState
  -- (b) invariant checks
  State.checkInvariants hs.rtState
  State.checkStableInvariants hs.rtState
  -- (a) value agreement for all observers
  for i in [:hs.refModel.observed.size] do
    let some nodeIdx := hs.refModel.observed[i]? | pure ()
    let refVal       := refEval hs.refModel hs.refModel.nodes.size nodeIdx
    let some obs     := hs.observed[i]? | pure ()
    let rtVal        <- Observer.value? obs
    unless rtVal == refVal do
      throw (IO.userError
        s!"FAIL seed={seed} step={step}: observer {i} (node {nodeIdx}): rt={repr rtVal} ref={repr refVal}")
  -- (c) second stabilize is a no-op (idempotence)
  let stats <- State.stabilizeWithStats hs.rtState
  unless stats.nodesVisited == 0 do
    throw (IO.userError
      s!"FAIL seed={seed} step={step}: idempotence: second stabilize visited {stats.nodesVisited} nodes")
  return hs

/- ------------------------------------------------------------------ -/
/-  Trace execution                                                      -/
/- ------------------------------------------------------------------ -/

def runTrace (seed : UInt64) (steps : Nat) : IO Unit := do
  let state <- State.create
  let v0 <- Var.create state (0 : Int)
  let v1 <- Var.create state (1 : Int)
  let hs0 : HarnessState := {
    rtState  := state,
    refModel := { nodes := #[.rVar 0, .rVar 1], observed := #[] },
    handles  := #[.hVar v0 (Var.watch v0), .hVar v1 (Var.watch v1)],
    observed := #[]
  }
  let mut hs := hs0
  let mut s  := seed
  for step in [:steps] do
    let (s', op) := smRange s 8;  s := s'
    let (s', r0) := smNext s;     s := s'
    let (s', r1) := smNext s;     s := s'
    let (s', r2) := smNext s;     s := s'
    match op with
    | 0 => hs <- opCreateVar hs ((r0 % 100).toNat : Int)
    | 1 => hs <- opCreateMap1 hs r0 r1
    | 2 => hs <- opCreateMap2 hs r0 r1 r2
    | 3 => hs <- opSetVar hs r0 ((r1 % 100).toNat : Int)
    | 4 => hs <- opObserve hs r0
    | 5 => hs <- opStabilize hs seed step
    | 6 =>
        -- Reclaim cached values (safe: does not invalidate node handles).
        let _ <- State.reclaimUnreachableCachedValues hs.rtState
    | _ => hs <- opMarkStale hs r0
  let _ <- opStabilize hs seed steps
  -- Test reclaimUnreachableNodes: disallow all observers, stabilize, reclaim.
  for obs in hs.observed do
    Observer.disallowFutureUse obs
  State.stabilize state
  let _ <- State.reclaimUnreachableNodes state
  State.checkInvariants state

/- ------------------------------------------------------------------ -/
/-  Main                                                                 -/
/- ------------------------------------------------------------------ -/

def runPropTests (numTraces stepsPerTrace : Nat) : IO Unit := do
  IO.println s!"Running {numTraces} property traces ({stepsPerTrace} steps each)..."
  for i in [:numTraces] do
    let seed := i.toUInt64 * 6364136223846793005 + 1442695040888963407
    runTrace seed stepsPerTrace
  IO.println "All property traces passed."

end PropHarness
end Tests
end Leancremental

def main : IO Unit :=
  Leancremental.Tests.PropHarness.runPropTests 1000 30
