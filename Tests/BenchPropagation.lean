import Leancremental

open Leancremental

def measureMicros (action : IO α) : IO (Nat × α) := do
  let start <- IO.monoNanosNow
  let r <- action
  let stop <- IO.monoNanosNow
  pure ((stop - start) / 1000, r)

/-- Chain: var -> map -> map -> ... (depth n), one observer at the end.
Setting the var stales the whole chain: k = n recomputes in one pass. -/
def benchChain (n : Nat) : IO Unit := do
  let state <- State.create
  let v <- Var.create state (0 : Nat)
  let mut node := Var.watch v
  for _ in [:n] do
    node <- map node (fun x => x + 1)
  let _o <- observe node
  State.stabilize state
  let mut best := 1000000000
  for round in [:3] do
    let (t, _) <- measureMicros do
      Var.set v (round + 1)
      State.stabilize state
    best := min best t
  IO.println s!"chain n={n} fullWaveStabilize={best}us"

/-- Width: n independent var -> map -> observer triples, ALL vars dirtied
before one stabilize: k = n pending-dirty records + n recomputes. -/
def benchAllDirty (n : Nat) : IO Unit := do
  let state <- State.create
  let mut vars : Array (Var Nat) := #[]
  for _ in [:n] do
    let v <- Var.create state (0 : Nat)
    let m <- map (Var.watch v) (fun x => x + 1)
    let _o <- observe m
    vars := vars.push v
  State.stabilize state
  let mut best := 1000000000
  for round in [:3] do
    let (t, _) <- measureMicros do
      for v in vars do
        Var.set v (round + 1)
      State.stabilize state
    best := min best t
  IO.println s!"allDirty n={n} stabilize={best}us"

def main : IO Unit := do
  for n in [100, 200, 400, 800, 1600] do
    benchChain n
  for n in [100, 200, 400, 800, 1600] do
    benchAllDirty n
