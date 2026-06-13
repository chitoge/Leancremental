import Leancremental

open Leancremental

def measureMicros (action : IO α) : IO (Nat × α) := do
  let start <- IO.monoNanosNow
  let r <- action
  let stop <- IO.monoNanosNow
  pure ((stop - start) / 1000, r)

/--
Build `n` independent (var -> map -> observer) triples, then measure the cost
of stabilizing with exactly ONE dirty var, and of a no-op stabilize. If
stabilization cost were proportional to the dirty set, both should be flat in
`n`; full-graph passes in `startOrResumeStabilization` predict growth instead.
-/
def benchSize (n : Nat) : IO Unit := do
  let state <- State.create
  let mut vars : Array (Var Nat) := #[]
  for _ in [:n] do
    let v <- Var.create state (0 : Nat)
    let m <- map (Var.watch v) (fun x => x + 1)
    let _o <- observe m
    vars := vars.push v
  State.stabilize state
  let some v0 := vars[0]? | throw (IO.userError "no vars")
  let mut oneDirtyBest := 1000000000
  let mut noopBest := 1000000000
  for round in [:5] do
    let (t1, _) <- measureMicros do
      Var.set v0 (round + 1)
      State.stabilize state
    let (t2, _) <- measureMicros do
      State.stabilize state
    oneDirtyBest := min oneDirtyBest t1
    noopBest := min noopBest t2
  IO.println s!"n={n} oneDirtyStabilize={oneDirtyBest}us noopStabilize={noopBest}us"

def main : IO Unit := do
  for n in [100, 200, 400, 800, 1600, 3200] do
    benchSize n
