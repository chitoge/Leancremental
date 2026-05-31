import Leancremental.Core.Internal

/-! Public state operations and graph diagnostics. -/

namespace Leancremental
namespace State

/-- Lightweight telemetry from one completed stabilization. -/
structure StabilizeStats where
  /-- Stabilization number assigned to the completed pass. -/
  stabilization : Nat
  /-- Number of node metadata records touched during this stabilization. -/
  nodesStabilized : Nat
  /-- Number of nodes whose value changed during this stabilization. -/
  nodesChanged : Nat
  /-- Number of active observers refreshed after this stabilization. -/
  activeObservers : Nat
  /-- Remaining recompute-heap entries; normally zero after a full stabilization. -/
  remainingRecomputeEntries : Nat
deriving Repr, BEq

/-- Result of a budgeted stabilization slice. -/
structure StabilizeBudgetResult where
  /-- Telemetry for the stabilization epoch touched by this slice. -/
  stats : StabilizeStats
  /-- Whether no recompute work remains and observers were refreshed. -/
  completed : Bool
  /-- Number of recompute-heap roots consumed by this slice. -/
  rootsProcessed : Nat
deriving Repr, BEq

/-- Create a fresh independent incremental graph state. -/
def create : IO State := do
  let nodes <- IO.mkRef #[]
  let observers <- IO.mkRef #[]
  let recomputeEntries <- IO.mkRef #[]
  let visitStack <- IO.mkRef #[]
  let stabilizationNum <- IO.mkRef 0
  let partialStabilization <- IO.mkRef none
  let stabilizing <- IO.mkRef false
  pure {
    nodes := nodes,
    observers := observers,
    recomputeHeap := { entries := recomputeEntries },
    visitStack := visitStack,
    stabilizationNum := stabilizationNum,
    partialStabilization := partialStabilization,
    stabilizing := stabilizing
  }

/-- Return whether this state is currently inside `stabilize`. -/
def amStabilizing (state : State) : IO Bool :=
  state.stabilizing.get

/-- Return the most recent completed stabilization number. -/
def currentStabilization (state : State) : IO Nat :=
  state.stabilizationNum.get

/-- Return whether a budgeted stabilization has remaining work. -/
def hasPartialStabilization (state : State) : IO Bool := do
  pure (Option.isSome (← state.partialStabilization.get))

/-- Return the number of queued recompute roots. -/
def recomputeHeapSize (state : State) : IO Nat := do
  pure (← state.recomputeHeap.entries.get).size

/-- Return the number of nodes allocated in this state. -/
def numNodes (state : State) : IO Nat := do
  let nodes <- state.nodes.get
  pure nodes.size

/-- Return the number of active observers in this state. -/
def numObservers (state : State) : IO Nat := do
  let observers <- state.observers.get
  let mut count := 0
  for observer in observers do
    if <- observer.isActive then
      count := count + 1
  pure count

/-- Read diagnostic metadata for a node by id. -/
def nodeInfo (state : State) (id : Nat) : IO NodeInfo :=
  Internal.State.getInfo state id

/-- Worker for `detectCycle`, exposed for advanced graph traversals. -/
partial def detectCycleFrom
    (state : State)
    (visitedRef : IO.Ref (Array Nat))
    (foundRef : IO.Ref (Option (List Nat)))
    (stack : Array Nat)
    (id : Nat) : IO Unit := do
  match <- foundRef.get with
  | some _ => pure ()
  | none =>
      if Internal.containsNat stack id then
        foundRef.set (some (Internal.closeCyclePath id stack))
      else
        let visited <- visitedRef.get
        if Internal.containsNat visited id then
          pure ()
        else
          visitedRef.set (visited.push id)
          let info <- Internal.State.getInfo state id
          let nextStack := stack.push id
          for child in info.children do
            detectCycleFrom state visitedRef foundRef nextStack child

/-- Detect a cycle in the current graph, returning a closed path of node ids if present. -/
def detectCycle (state : State) : IO (Option (List Nat)) := do
  let visitedRef <- IO.mkRef #[]
  let foundRef <- IO.mkRef none
  let nodes <- state.nodes.get
  for index in [:nodes.size] do
    detectCycleFrom state visitedRef foundRef #[] index
  foundRef.get

/-- Raise an `IO.userError` if the current graph contains a cycle. -/
def checkAcyclic (state : State) : IO Unit := do
  match <- detectCycle state with
  | none => pure ()
  | some cycle => Internal.throwUser (Internal.formatCycle cycle)

/-- Format a cycle path as a human-readable diagnostic. -/
def formatCycle (cycle : List Nat) : String :=
  Internal.formatCycle cycle

/-- Export the current graph in Graphviz DOT format. -/
def toDot (state : State) : IO String := do
  let nodes <- state.nodes.get
  let mut lines := #["digraph Leancremental {"]
  for index in [:nodes.size] do
    let info <- Internal.State.getInfo state index
    let label := s!"{info.id} {info.kind.name} h={info.height} necessary={info.necessary} stale={info.stale}"
    lines := lines.push s!"  n{info.id} [label=\"{label}\"];"
  for index in [:nodes.size] do
    let info <- Internal.State.getInfo state index
    for child in info.children do
      lines := lines.push s!"  n{child} -> n{info.id};"
  lines := lines.push "}"
  pure (Internal.joinWith "\n" lines.toList)

/-- Write `toDot state` to a file. -/
def saveDotToFile (state : State) (path : System.FilePath) : IO Unit := do
  IO.FS.writeFile path (← toDot state)

def startOrResumeStabilization (state : State) : IO Nat := do
  match <- state.partialStabilization.get with
  | some stabilization => pure stabilization
  | none =>
      let stabilization := (← state.stabilizationNum.get) + 1
      state.stabilizationNum.set stabilization
      state.partialStabilization.set (some stabilization)
      Internal.State.clearRecomputeHeap state
      Internal.State.recomputeNecessary state
      Internal.State.enqueueInitialRecomputes state
      pure stabilization

def refreshObservers (state : State) : IO Unit := do
  let observers <- state.observers.get
  for observer in observers do
    observer.refresh

/--
Bring all active observers up to date by recomputing necessary stale nodes.

Variable changes and clock advances become visible to observers only after this
function completes successfully.
-/
def stabilize (state : State) : IO Unit := do
  if <- state.stabilizing.get then
    Internal.throwUser "nested stabilization is not supported"
  state.stabilizing.set true
  try
    let stabilization <- startOrResumeStabilization state
    Internal.State.drainRecomputeHeap state stabilization
    refreshObservers state
    state.partialStabilization.set none
    state.stabilizing.set false
  catch error =>
    state.stabilizing.set false
    throw error

/-- Return stabilization telemetry for the current metadata state. -/
def stabilizationStats (state : State) (stabilization : Nat) : IO StabilizeStats := do
  let nodes <- state.nodes.get
  let mut nodesStabilized := 0
  let mut nodesChanged := 0
  for index in [:nodes.size] do
    let info <- Internal.State.getInfo state index
    if info.computedAt == some stabilization then
      nodesStabilized := nodesStabilized + 1
    if info.changedAt == some stabilization then
      nodesChanged := nodesChanged + 1
  let activeObservers <- numObservers state
  let heapEntries <- state.recomputeHeap.entries.get
  pure {
    stabilization := stabilization,
    nodesStabilized := nodesStabilized,
    nodesChanged := nodesChanged,
    activeObservers := activeObservers,
    remainingRecomputeEntries := heapEntries.size
  }

/-- Stabilize the graph and return lightweight telemetry for the completed pass. -/
def stabilizeWithStats (state : State) : IO StabilizeStats := do
  stabilize state
  let stabilization <- currentStabilization state
  stabilizationStats state stabilization

/--
Run at most `maxRoots` recompute-heap roots from the current stabilization.

Each root is processed atomically by the same dependency-first machinery as full
stabilization. If the result is incomplete, observers are not refreshed and a
later call resumes the same stabilization number. Call `cancelStabilization`
before applying new edits that should abandon an incomplete pass.
-/
def stabilizeWithBudget (state : State) (maxRoots : Nat) : IO StabilizeBudgetResult := do
  if <- state.stabilizing.get then
    Internal.throwUser "nested stabilization is not supported"
  state.stabilizing.set true
  try
    let stabilization <- startOrResumeStabilization state
    let rootsProcessed <- Internal.State.drainRecomputeHeapWithBudget state stabilization maxRoots
    let remaining <- recomputeHeapSize state
    let completed := remaining == 0
    if completed then
      refreshObservers state
      state.partialStabilization.set none
    let stats <- stabilizationStats state stabilization
    state.stabilizing.set false
    pure { stats := stats, completed := completed, rootsProcessed := rootsProcessed }
  catch error =>
    state.stabilizing.set false
    throw error

/-- Abort an incomplete budgeted stabilization. The next stabilization starts a fresh epoch. -/
def cancelStabilization (state : State) : IO Unit := do
  if <- state.stabilizing.get then
    Internal.throwUser "cannot cancel stabilization while a stabilization call is running"
  state.partialStabilization.set none
  Internal.State.clearRecomputeHeap state
  state.visitStack.set #[]

end State
end Leancremental
