import Leancremental

open Leancremental

def measureMicros (action : IO α) : IO (Nat × α) := do
  let start <- IO.monoNanosNow
  let r <- action
  let stop <- IO.monoNanosNow
  pure ((stop - start) / 1000, r)

/-- n entries in an AssocIndexedAggregate; update ONE entry's var and
stabilize. R3 acceptance: cost should be O(log n), not O(n). -/
def benchAggregate (n : Nat) : IO Unit := do
  let state <- State.create
  let aggregate <- AssocIndexedAggregate.create (κ := Nat) state 0 (fun _ value => value) (· + ·)
  let mut vars : Array (Var Nat) := #[]
  for i in [:n] do
    let v <- Var.create state (1 : Nat)
    AssocIndexedAggregate.insertOrReplace aggregate i (Var.watch v)
    vars := vars.push v
  let observer <- observe (AssocIndexedAggregate.watch aggregate)
  State.stabilize state
  let some v0 := vars[0]? | throw (IO.userError "no vars")
  let mut best := 1000000000
  let mut stabilized := 0
  for round in [:5] do
    -- Time only the engine work; stats collection is O(all nodes) by design
    -- and is gathered outside the measured region.
    let (t, _) <- measureMicros do
      Var.set v0 (round + 2)
      State.stabilize state
    let stabilization <- State.currentStabilization state
    let stats <- State.stabilizationStats state stabilization
    best := min best t
    stabilized := stats.nodesStabilized
  let stabilization <- State.currentStabilization state
  let finalStats <- State.stabilizationStats state stabilization
  let total <- Observer.value! observer
  IO.println s!"aggregate n={n} oneEntryUpdate={best}us nodesStabilized={stabilized} nodesVisited={finalStats.nodesVisited} (total={total})"

def main : IO Unit := do
  for n in [100, 400, 1600, 6400] do
    benchAggregate n
