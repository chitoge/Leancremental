import Leancremental.Core.Internal
import Lean.Data.Json

/-!
Public `State` operations, stabilization entry points, and graph diagnostics.
-/

namespace Leancremental
namespace State

/-- Lightweight telemetry from one completed stabilization. -/
structure StabilizeStats where
  /-- Stabilization number assigned to the completed pass. -/
  stabilization : StabilizationId
  /-- Number of node metadata records touched during this stabilization. -/
  nodesStabilized : Nat
  /-- Number of nodes whose value changed during this stabilization. -/
  nodesChanged : Nat
  /-- Number of active observers refreshed after this stabilization. -/
  activeObservers : Nat
  /-- Remaining recompute-heap entries; normally zero after a full stabilization. -/
  remainingRecomputeEntries : Nat
  /-- Number of `stabilizeOne` entries during this pass (O(1) counter). -/
  nodesVisited : Nat
  /-- Number of observers refreshed during this pass (O(1) counter). -/
  observersRefreshed : Nat
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

private initialize stateIdCounter : IO.Ref Nat ← IO.mkRef 0

/-- Create a fresh independent incremental graph state with timestamp type `T`.
    Use `State.create` for the default `T = Nat` case. -/
def createWith [Timestamp T] : IO (State T) := do
  let stateId ← stateIdCounter.modifyGet (fun n => (n, n + 1))
  let nodes <- IO.mkRef #[]
  let nodeGenerations <- IO.mkRef #[]
  let recycledNodeIdsRef <- IO.mkRef #[]
  let necessaryRefCounts <- IO.mkRef #[]
  let staleNecessaryIdsRef <-
    IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
  let observers <- IO.mkRef #[]
  let tagIndexRef <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap String (Array Nat))
  let dependencyChangeHandlers <- IO.mkRef #[]
  let recomputeBuckets <- IO.mkRef #[]
  let recomputeMembers <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
  let recomputeNextHeight <- IO.mkRef 0
  let recomputeSizeRef <- IO.mkRef 0
  let pendingDirtyRef <-
    IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
  let traceModeRef <- IO.mkRef TraceMode.off
  let traceEventsRef <- IO.mkRef #[]
  let traceEventsStartRef <- IO.mkRef 0
  let deferredMutationsRef <- IO.mkRef #[]
  let visitStack <- IO.mkRef #[]
  let frontierRef <- IO.mkRef (Frontier.advance { elements := #[] } Timestamp.zero)
  let stabilizationNum <- IO.mkRef (Timestamp.zero)
  let partialStabilization <- IO.mkRef none
  let stabilizing <- IO.mkRef false
  let handlerFailureModeRef <- IO.mkRef HandlerFailureMode.traceOnly
  let nodesVisitedRef <- IO.mkRef 0
  let observersRefreshedRef <- IO.mkRef 0
  let observersByNode <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Nat (Array Nat))
  let changedNodeIdsRef <- IO.mkRef #[]
  let newObserverIdsRef <- IO.mkRef #[]
  let pinnedIdsRef <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Nat)
  let timingModeRef <- IO.mkRef false
  let lastPassTimingsRef <- IO.mkRef (Array.empty : Array (Nat × Nat))
  let stateLock <- Std.BaseSharedMutex.new
  pure {
    stateId := stateId,
    nodes := nodes,
    nodeGenerations := nodeGenerations,
    recycledNodeIdsRef := recycledNodeIdsRef,
    necessaryRefCounts := necessaryRefCounts,
    staleNecessaryIdsRef := staleNecessaryIdsRef,
    observers := observers,
    tagIndexRef := tagIndexRef,
    dependencyChangeHandlers := dependencyChangeHandlers,
    recomputeHeap := {
      buckets := recomputeBuckets,
      members := recomputeMembers,
      nextHeight := recomputeNextHeight,
      sizeRef := recomputeSizeRef
    },
    pendingDirtyRef := pendingDirtyRef,
    traceModeRef := traceModeRef,
    traceEventsRef := traceEventsRef,
    traceEventsStartRef := traceEventsStartRef,
    deferredMutationsRef := deferredMutationsRef,
    visitStack := visitStack,
    frontierRef := frontierRef,
    stabilizationNum := stabilizationNum,
    partialStabilization := partialStabilization,
    stabilizing := stabilizing,
    handlerFailureModeRef := handlerFailureModeRef,
    nodesVisitedRef := nodesVisitedRef,
    observersRefreshedRef := observersRefreshedRef,
    observersByNode := observersByNode,
    changedNodeIdsRef := changedNodeIdsRef,
    newObserverIdsRef := newObserverIdsRef,
    pinnedIdsRef := pinnedIdsRef,
    timingModeRef := timingModeRef,
    lastPassTimingsRef := lastPassTimingsRef,
    stateLock := stateLock
  }

/-- Create a fresh independent incremental graph state with the default `Nat` timestamp. -/
def create : IO State := createWith

/-- Return scheduler-facing trace events emitted so far. -/
def traceEvents (state : State) : IO (Array StateTraceEvent) :=
  Internal.State.orderedTraceEvents state

/-- Return the current scheduler trace retention mode. -/
def getTraceMode (state : State) : IO TraceMode :=
  state.traceModeRef.get

/-- Set the scheduler trace retention mode. -/
def setTraceMode (state : State) (mode : TraceMode) : IO Unit := do
  match mode with
  | .bounded _ =>
      pure ()
  | .off | .unbounded =>
      let ordered <- Internal.State.orderedTraceEvents state
      state.traceEventsRef.set ordered
      state.traceEventsStartRef.set 0
  state.traceModeRef.set mode

/-- Clear all currently buffered scheduler-facing trace events. -/
def clearTraceEvents (state : State) : IO Unit := do
  state.traceEventsRef.set #[]
  state.traceEventsStartRef.set 0

/--
Register a callback for node dependency rewrites.

Handlers run when an existing node's child list changes, for example through
dynamic `bind` rewiring or lifecycle combinators such as `freeze`.
-/
def onDependenciesChanged
    (state : State)
    (handler : Nat -> Array Nat -> Array Nat -> IO Unit) : IO Unit :=
  state.dependencyChangeHandlers.modify (fun handlers => handlers.push handler)

/-- Return whether this state is currently inside `stabilize`. -/
def amStabilizing (state : State) : IO Bool :=
  state.stabilizing.get

/-- Enable or disable per-recompute timing. -/
def setTimingEnabled (state : State) (enabled : Bool) : IO Unit :=
  state.timingModeRef.set enabled

/-- Return whether per-recompute timing is enabled. -/
def timingEnabled (state : State) : IO Bool :=
  state.timingModeRef.get

/-- Return per-recompute timings recorded during the last completed pass. -/
def lastPassTimings (state : State) : IO (Array (Nat × Nat)) :=
  state.lastPassTimingsRef.get

/-- Return the most recent completed stabilization number. -/
def currentStabilization (state : State) : IO StabilizationId :=
  state.stabilizationNum.get

/-- Return whether a budgeted stabilization has remaining work. -/
def hasPartialStabilization (state : State) : IO Bool := do
  pure (Option.isSome (← state.partialStabilization.get))

/-- Return the number of queued recompute roots. -/
def recomputeHeapSize (state : State) : IO Nat := do
  state.recomputeHeap.sizeRef.get

/--
Return all node ids currently indexed under `tag`, in ascending id order.

`tagIndexRef` is written by node registration and by tag operations
(`Incr.addTag`, `Incr.removeTag`), but all writers are blocked during
stabilize, so concurrent calls with a running stabilize are safe in practice.
However, graph construction itself is not thread-safe; call this only after
all nodes and tags are registered.

Cost: O(k) in the number of node ids currently stored for `tag`.
-/
def nodesWithTag (state : State) (tag : String) : IO (Array Nat) := do
  pure ((← state.tagIndexRef.get).getD tag #[])

/--
Return the currently stale necessary node ids, in ascending id order.

**Concurrency note**: `staleNecessaryIdsRef` is mutated during stabilize.
Calling `staleNecessaryIds` concurrently with a running `stabilize` will
observe a mid-stabilize snapshot; do not rely on the result being stable.
Typical use calls this *between* stabilizations, where the result is
consistent.

Cost: O(s log s) in the number of stale necessary nodes because the set is
materialized and sorted for the public result.
-/
def staleNecessaryIds (state : State) : IO (Array Nat) := do
  let staleNecessarySet <- state.staleNecessaryIdsRef.get
  pure (Internal.sortedIdsFromNatSet staleNecessarySet)

/--
Increment the pin refcount for node `id`, preventing GC reclamation.

Thread-safety: serialized through the state's write lock.
Cost: expected O(1).
-/
def pinNode (state : State) (id : Nat) : IO Unit := do
  state.stateLock.write
  try
    if <- amStabilizing state then
      Internal.throwUser "cannot pin a node while stabilization is running"
    if <- hasPartialStabilization state then
      Internal.throwUser "cannot pin a node while a budgeted stabilization is incomplete"
    state.pinnedIdsRef.modify (fun m => m.insert id ((m.getD id 0) + 1))
  finally
    state.stateLock.unlockWrite

/--
Decrement the pin refcount for node `id`; erases the entry when it reaches zero.

Thread-safety: serialized through the state's write lock.
Cost: expected O(1).
-/
def unpinNode (state : State) (id : Nat) : IO Unit := do
  state.stateLock.write
  try
    if <- amStabilizing state then
      Internal.throwUser "cannot unpin a node while stabilization is running"
    if <- hasPartialStabilization state then
      Internal.throwUser "cannot unpin a node while a budgeted stabilization is incomplete"
    state.pinnedIdsRef.modify (fun m =>
      let count := m.getD id 0
      if count <= 1 then m.erase id else m.insert id (count - 1))
  finally
    state.stateLock.unlockWrite

def ensureCanReclaimCachedValues (state : State) : IO Unit := do
  if <- amStabilizing state then
    Internal.throwUser "cannot reclaim cached values while stabilization is running"
  if <- hasPartialStabilization state then
    Internal.throwUser "cannot reclaim cached values while a budgeted stabilization is incomplete"

/--
Clear cached values on unreachable nodes that can safely recompute later.

Returns the number of node caches that were actually cleared. Nodes still
reachable from active observers, and nodes whose kind cannot safely regenerate
their cache after clearing, are left untouched.

Thread-safety: serialized through the state's write lock.
Cost: O(all nodes).
-/
def reclaimUnreachableCachedValues (state : State) : IO Nat := do
  state.stateLock.write
  try
    ensureCanReclaimCachedValues state
    let nodes <- state.nodes.get
    let mut cleared := 0
    for nodeId in [:nodes.size] do
      let info <- Internal.State.getInfo state nodeId
      if info.necessary then
        pure ()
      else
        let node <- Internal.State.getNode state nodeId
        if node.canRecomputeAfterClear then
          if <- node.clearValue then
            cleared := cleared + 1
    pure cleared
  finally
    state.stateLock.unlockWrite

/--
Reclaim unreachable orphaned nodes and recycle their storage slots.

This operation is guarded like stabilization-sensitive mutations and is intended
for long-running hosts that want to cap node growth from dynamic rewiring.
Reclaimed slots bump an internal generation counter; stale `Incr` handles that
still point at reclaimed slots will fail with a user error when used.

Returns the number of nodes reclaimed in this pass.

Thread-safety: serialized through the state's write lock.
Cost: O(all nodes) in the current implementation.
-/
def reclaimUnreachableNodes (state : State) : IO Nat := do
  state.stateLock.write
  try
    ensureCanReclaimCachedValues state
    let nodes <- state.nodes.get
    let visitedRef <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
    let recycledNodeIds <- state.recycledNodeIdsRef.get
    let recycledSet := recycledNodeIds.foldl (fun s id => s.insert id ()) (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
    let recycledSetRef <- IO.mkRef recycledSet
    let mut reclaimed := 0
    for nodeId in [:nodes.size] do
      reclaimed := reclaimed + (← Internal.State.reclaimOrphanedNode state visitedRef recycledSetRef nodeId)
    pure reclaimed
  finally
    state.stateLock.unlockWrite

def queueNodeMarkStale (state : State) (nodeId : Nat) (reason : Option String) : IO Unit := do
  let stabilization <-
    if <- state.stabilizing.get then
      state.partialStabilization.get
    else
      pure none
  state.deferredMutationsRef.modify (fun ops => ops.push (.markStale nodeId reason stabilization))

def queueNodeInvalidate (state : State) (nodeId : Nat) (reason : Option String) : IO Unit := do
  let stabilization <-
    if <- state.stabilizing.get then
      state.partialStabilization.get
    else
      pure none
  state.deferredMutationsRef.modify (fun ops => ops.push (.invalidate nodeId reason stabilization))

/-- Return the number of nodes allocated in this state. Cost: O(1). -/
def numNodes (state : State) : IO Nat := do
  let nodes <- state.nodes.get
  pure nodes.size

/-- Return `(totalSlots, freeListSize)` for live-node accounting. Cost: O(1). -/
def nodeSlotStats (state : State) : IO (Nat × Nat) := do
  let nodes <- state.nodes.get
  let recycled <- state.recycledNodeIdsRef.get
  pure (nodes.size, recycled.size)

/-- Return the number of active observers in this state. Cost: O(all observers). -/
def numObservers (state : State) : IO Nat := do
  let observers <- state.observers.get
  let mut count := 0
  for observer in observers do
    if <- observer.isActive then
      count := count + 1
  pure count

/-- Return whether the current graph is made only of node kinds that participate
    in parallel stabilization.

    This is a pre-flight check for `parallel := true`. If it returns `false`,
    the graph still works, but some nodes will run sequentially.

    Non-parallel-safe kinds: `bind`, `freeze`, `expert`, `join`, `branch`.
    Cost: O(all nodes). -/
def graphParallelSafe (state : State) : IO Bool := do
  let nodes ← state.nodes.get
  for index in [:nodes.size] do
    let info ← Internal.State.getInfo state index
    if !info.kind.isParallelSafe then
      return false
  return true

def reachableNodeIds (state : State) : IO (Array Nat) :=
  Internal.State.collectNecessary state

/-- Read diagnostic metadata for a node by id. Cost: O(1). -/
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

/-- Detect a cycle in the current graph, returning a closed path of node ids if present. Cost: O(all nodes + all edges). -/
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

/-- Export the current graph in Graphviz DOT format. Cost: O(all nodes + all edges). -/
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
      state.nodesVisitedRef.set 0
      state.observersRefreshedRef.set 0
      state.changedNodeIdsRef.set #[]
      state.lastPassTimingsRef.set #[]
      Internal.State.clearRecomputeHeap state
      Internal.State.drainPendingDirty state
      pure stabilization

-- Write lastValues for changed observers and collect user callbacks. Must be called under the write lock.
-- Callbacks are returned so the caller can fire them after releasing the lock.
private def refreshObserversLocked (state : State) : IO (Array (IO Unit)) := do
  let changedNodes <- state.changedNodeIdsRef.get
  let newObserverIds <- state.newObserverIdsRef.get
  let observersByNode <- state.observersByNode.get
  let observers <- state.observers.get
  let mut toRefresh : Std.HashMap Nat Unit := .emptyWithCapacity
  for idx in newObserverIds do
    toRefresh := toRefresh.insert idx ()
  for nodeId in changedNodes do
    for idx in observersByNode.getD nodeId #[] do
      toRefresh := toRefresh.insert idx ()
  let mut pendingCallbacks : Array (IO Unit) := #[]
  for (idx, _) in toRefresh do
    if let some observer := observers[idx]? then
      if <- observer.isActive then
        let callbacks <- observer.refreshAndCollect
        pendingCallbacks := pendingCallbacks ++ callbacks
        state.observersRefreshedRef.modify (· + 1)
      else
        state.observersByNode.modify (fun m =>
          let existing := m.getD observer.nodeId #[]
          m.insert observer.nodeId (existing.filter (· != idx)))
  state.newObserverIdsRef.set #[]
  pure pendingCallbacks

-- Inner stabilization logic. Caller must hold the write lock.
-- `parallel`: when true, uses the barrier-per-height parallel drain instead of the
-- sequential drain.  The global write lock is still held for the full duration.
-- Returns the completed stabilization epoch together with the observer callbacks.
private def stabilizeLocked (state : State) (parallel : Bool) :
    IO (StabilizationId × Array (IO Unit)) := do
  if <- state.stabilizing.get then
    Internal.throwUser "nested stabilization is not supported"
  state.stabilizing.set true
  try
    let stabilization <- startOrResumeStabilization state
    if parallel then
      Internal.State.drainRecomputeHeapParallel state stabilization
    else
      Internal.State.drainRecomputeHeap state stabilization
    -- Deferred mutations are applied before observer refresh so that observers
    -- see the final graph state (including any staleness set by deferred ops).
    state.stabilizing.set false
    Internal.State.applyDeferredMutations state stabilization
    -- Advance the frontier to the completed stabilization epoch.
    let oldFrontier <- state.frontierRef.get
    state.frontierRef.set (Frontier.advance oldFrontier stabilization)
    let callbacks <- refreshObserversLocked state
    state.partialStabilization.set none
    pure (stabilization, callbacks)
  catch error =>
    state.stabilizing.set false
    throw error

-- Acquire the write lock, run stabilization, release the lock, fire callbacks.
-- Returns the epoch that was captured inside the lock — before any concurrent
-- `stabilize` call on the same state could increment it.
private def stabilizeInner (state : State) (parallel : Bool) : IO StabilizationId := do
  state.stateLock.write
  let (stabilization, pendingCallbacks) ←
    try stabilizeLocked state parallel finally state.stateLock.unlockWrite
  for callback in pendingCallbacks do
    callback
  pure stabilization

/--
Bring all active observers up to date by recomputing necessary stale nodes.

Variable changes and clock advances become visible to observers only after this
function completes successfully.

When `parallel := true`, nodes at the same height level are recomputed concurrently
using `IO.asTask`.  Only `const`, `var`, `map`, `map2`, `map3`, `map4`, `map5`,
and `fold` nodes participate in parallel execution; `bind`, `freeze`, and `expert`
nodes always run sequentially.

For ordinary use, this mainly means that pure `map`-style computations can run
in parallel. `Expert.Node` remains sequential. If you build custom runtime
behavior around shared mutable state, that state still needs the usual explicit
synchronization.

Thread-safety: `stabilize` itself is serialized through the state's write lock;
nested stabilization is rejected.

Cost: depends on how many necessary stale nodes must be recomputed and how many
can be parallelized.

Call `State.graphParallelSafe` before passing `parallel := true` to confirm
that no node in the graph will fall back to sequential execution.
-/
def stabilize (state : State) (parallel : Bool := false) : IO Unit := do
  let _ ← stabilizeInner state parallel

/-- Return stabilization telemetry for the current metadata state. Cost: O(all nodes + all observers). -/
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
  let remainingRecomputeEntries <- recomputeHeapSize state
  let nodesVisited <- state.nodesVisitedRef.get
  let observersRefreshed <- state.observersRefreshedRef.get
  pure {
    stabilization := stabilization,
    nodesStabilized := nodesStabilized,
    nodesChanged := nodesChanged,
    activeObservers := activeObservers,
    remainingRecomputeEntries := remainingRecomputeEntries,
    nodesVisited := nodesVisited,
    observersRefreshed := observersRefreshed
  }

/--
Return `(nodesVisited, observersRefreshed)` from the last completed stabilization pass.

O(1) — reads two `IO.Ref Nat` counters that are reset at the start of every pass
and incremented during it. Use this inside hot assertion paths (e.g. locality tests)
instead of `stabilizationStats`, which is O(all nodes).
-/
def lastPassCounters (state : State) : IO (Nat × Nat) := do
  let nv <- state.nodesVisitedRef.get
  let or <- state.observersRefreshedRef.get
  pure (nv, or)

/--
Stabilize the graph and return lightweight telemetry for the completed pass.

Accepts the same `parallel` parameter as `stabilize`.

Cost: stabilization cost plus `stabilizationStats`, which scans current state.
-/
def stabilizeWithStats (state : State) (parallel : Bool := false) : IO StabilizeStats := do
  -- Use stabilizeInner to get the epoch captured inside the write lock, avoiding
  -- the race where a concurrent stabilize could increment the counter before
  -- currentStabilization reads it.
  let stabilization ← stabilizeInner state parallel
  stabilizationStats state stabilization

-- Inner budget stabilization logic. Caller must hold the write lock.
private def stabilizeWithBudgetLocked
    (state : State) (maxRoots : Nat) : IO ((Array (IO Unit)) × StabilizeBudgetResult) := do
  if <- state.stabilizing.get then
    Internal.throwUser "nested stabilization is not supported"
  state.stabilizing.set true
  try
    let stabilization <- startOrResumeStabilization state
    let rootsProcessed <- Internal.State.drainRecomputeHeapWithBudget state stabilization maxRoots
    let remaining <- recomputeHeapSize state
    let completed := remaining == 0
    if completed then
      -- Deferred mutations are applied before observer refresh so that observers
      -- see the final graph state after the completed stabilization pass.
      state.stabilizing.set false
      Internal.State.applyDeferredMutations state stabilization
      let oldFrontier <- state.frontierRef.get
      state.frontierRef.set (Frontier.advance oldFrontier stabilization)
      let callbacks <- refreshObserversLocked state
      state.partialStabilization.set none
      let stats <- stabilizationStats state stabilization
      pure (callbacks, { stats := stats, completed := completed, rootsProcessed := rootsProcessed })
    else
      let stats <- stabilizationStats state stabilization
      state.stabilizing.set false
      pure (#[], { stats := stats, completed := completed, rootsProcessed := rootsProcessed })
  catch error =>
    state.stabilizing.set false
    throw error

/--
Run at most `maxRoots` recompute-heap roots from the current stabilization.

Each root is processed atomically by the same dependency-first machinery as full
stabilization. If the result is incomplete, observers are not refreshed and a
later call resumes the same stabilization number. Call `cancelStabilization`
before applying new edits that should abandon an incomplete pass.

Thread-safety: serialized through the state's write lock.
Cost: proportional to the work needed for up to `maxRoots` recompute roots in
the current pass.
-/
def stabilizeWithBudget (state : State) (maxRoots : Nat) : IO StabilizeBudgetResult := do
  state.stateLock.write
  let outcome <- try stabilizeWithBudgetLocked state maxRoots finally state.stateLock.unlockWrite
  for callback in outcome.1 do
    callback
  pure outcome.2

/--
Abort an incomplete budgeted stabilization. The next stabilization starts a fresh epoch.

Thread-safety: serialized through the state's write lock.
Cost: proportional to the amount of queued budgeted work being restored or cleared.
-/
def cancelStabilization (state : State) : IO Unit := do
  state.stateLock.write
  try
    if <- state.stabilizing.get then
      Internal.throwUser "cannot cancel stabilization while a stabilization call is running"
    state.partialStabilization.set none
    -- Clear deferred mutations so stale-epoch entries cannot be applied in a later epoch.
    state.deferredMutationsRef.set #[]
    Internal.State.restoreRecomputeHeapToPendingDirty state
    Internal.State.clearRecomputeHeap state
    state.visitStack.set #[]
  finally
    state.stateLock.unlockWrite

/-- Return the number of deferred mutations currently queued. -/
def deferredMutationCount (state : State) : IO Nat := do
  pure (← state.deferredMutationsRef.get).size

/-- Return whether any deferred mutations are currently queued. -/
def hasDeferredMutations (state : State) : IO Bool := do
  pure (!(← state.deferredMutationsRef.get).isEmpty)

/-- Return the current handler failure mode. -/
def getHandlerFailureMode (state : State) : IO HandlerFailureMode :=
  state.handlerFailureModeRef.get

/--
Set the handler failure mode.

`HandlerFailureMode.traceOnly` (default): callback exceptions are recorded as
trace events and stabilization continues.

`HandlerFailureMode.failFast`: callback exceptions are recorded as trace events
and then re-thrown, aborting stabilization.
-/
def setHandlerFailureMode (state : State) (mode : HandlerFailureMode) : IO Unit :=
  state.handlerFailureModeRef.set mode

-- ---------------------------------------------------------------------------
-- Persistence-support primitives (metadata snapshot only)
-- ---------------------------------------------------------------------------

/--
Export scheduler-relevant metadata for every node as a compact JSON array.

Each element has the fields `id`, `lastAccessedAt`, `externalDirtyReason`,
and `tags`. Graph topology and computed values are not included.
-/
def exportNodeInfosJson (state : State) : IO String := do
  let nodes <- state.nodes.get
  let mut entries : Array Lean.Json := #[]
  for index in [:nodes.size] do
    let info <- Internal.State.getInfo state index
    let entry := Lean.Json.mkObj [
      ("id",                  Lean.toJson info.id),
      ("lastAccessedAt",      Lean.toJson info.lastAccessedAt),
      ("externalDirtyReason", Lean.toJson info.externalDirtyReason),
      ("tags",                Lean.toJson info.tags)
    ]
    entries := entries.push entry
  pure (Lean.Json.compress (.arr entries))

/--
Import mutable scheduler metadata (lastAccessedAt, externalDirtyReason, tags)
onto nodes matched by id. Unknown ids are silently ignored. Graph topology and
computed values are not modified.

The `json` parameter must be a JSON array produced by `State.exportNodeInfosJson`
or a compatible format.
-/
def importNodeMetadataJson (state : State) (json : String) : IO Unit := do
  let root <- match Lean.Json.parse json with
    | .error e => throw (IO.userError s!"importNodeMetadataJson: parse error: {e}")
    | .ok v => pure v
  let arr <- match root.getArr? with
    | .error _ => throw (IO.userError "importNodeMetadataJson: expected JSON array at top level")
    | .ok a => pure a
  let nodes <- state.nodes.get
  for item in arr do
    -- Require a valid numeric "id" field; skip items that lack one.
    let idResult : Except String Nat :=
      (item.getObjVal? "id").bind (fun v => Lean.fromJson? v)
    match idResult with
    | .error _ => pure ()
    | .ok nodeId =>
        if nodeId >= nodes.size then
          pure ()  -- ignore unknown ids
        else
          let info <- Internal.State.getInfo state nodeId
          let newLastAccessed : Option Nat :=
            match (item.getObjVal? "lastAccessedAt").bind (fun v => Lean.fromJson? v) with
            | .ok n => n
            | .error _ => info.lastAccessedAt
          let newDirtyReason : Option String :=
            match (item.getObjVal? "externalDirtyReason").bind (fun v => Lean.fromJson? v) with
            | .ok s => s
            | .error _ => info.externalDirtyReason
          let newTags : Array String :=
            match (item.getObjVal? "tags").bind (fun v => Lean.fromJson? v) with
            | .ok tags => tags
            | .error _ => info.tags
          Internal.State.setInfo state nodeId { info with
            lastAccessedAt := newLastAccessed,
            externalDirtyReason := newDirtyReason,
            tags := newTags
          }
  Internal.State.rebuildTagIndex state

end State
end Leancremental
