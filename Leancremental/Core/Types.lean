import Std.Data.HashMap
import Std.Sync.SharedMutex

/-!
Shared types used by Leancremental's executable runtime.

This module includes both public data structures, such as `NodeInfo`, and
lower-level runtime types that are mainly useful for generated docs and
implementers.
-/

namespace Leancremental

/-- The implementation kind of an incremental node, used for diagnostics and DOT output. -/
inductive NodeKind where
  | const
  | var
  | map
  | map2
  | map3
  | map4
  | map5
  | bind
  | join
  | branch
  | fold
  | freeze
  | expert
deriving Repr, BEq

namespace NodeKind

/-- Stable display name for a node kind. -/
def name : NodeKind -> String
  | .const => "const"
  | .var => "var"
  | .map => "map"
  | .map2 => "map2"
  | .map3 => "map3"
  | .map4 => "map4"
  | .map5 => "map5"
  | .bind => "bind"
  | .join => "join"
  | .branch => "branch"
  | .fold => "fold"
  | .freeze => "freeze"
  | .expert => "expert"

end NodeKind

/--
A cutoff decides whether a recomputed value should be treated as unchanged.

If `shouldCutoff old new` returns `true`, the node keeps `old` and does not
propagate a change to its parents.
-/
structure Cutoff (α : Type) where
  /-- Return `true` when propagation should stop between the old and new values. -/
  shouldCutoff : α -> α -> Bool
  /--
  When set, `writeValue` uses a cached-digest fast path: hash the new value
  once, compare against the stored digest, and skip the equality check on a
  digest mismatch.  The stored digest is updated whenever a new value is
  written, so `shouldCutoff` is used as the collision-guard fallback.
  -/
  hashValue : Option (α -> UInt64) := none

namespace Cutoff

/-- Never cut off propagation; every recomputation is considered a change. -/
def never : Cutoff α where
  shouldCutoff := fun _ _ => false

/-- Always cut off propagation; recomputed values never propagate. -/
def always : Cutoff α where
  shouldCutoff := fun _ _ => true

/-- Cut off when `BEq.beq` reports that the old and new values are equal. -/
def ofEq [BEq α] : Cutoff α where
  shouldCutoff := fun oldValue newValue => oldValue == newValue

/-- Cut off when decidable equality proves that the old and new values are equal. -/
def ofDecidableEq [DecidableEq α] : Cutoff α where
  shouldCutoff := fun oldValue newValue => decide (oldValue = newValue)

/--
Cut off when hash equality passes a cheap precheck and `BEq` confirms equality.

This preserves the fast mismatch path while preventing collision-induced false cutoffs.
-/
def ofHash [Hashable α] [BEq α] : Cutoff α where
  shouldCutoff := fun oldValue newValue =>
    (hash oldValue == hash newValue) && (oldValue == newValue)

/--
Unchecked hash-only cutoff.

This may suppress real changes when distinct values collide under `Hashable.hash`.
-/
def ofHashUnchecked [Hashable α] : Cutoff α where
  shouldCutoff := fun oldValue newValue => hash oldValue == hash newValue

/--
Cached-digest cutoff.

Stores the digest of the previously written value in the node's `digestRef`.
On each recompute, exactly one hash of the new value is computed and compared
with the stored digest on the fast path.  `BEq` is used as a collision guard
when digests match.
-/
def ofCachedDigest [Hashable α] [BEq α] : Cutoff α where
  shouldCutoff := fun oldValue newValue => oldValue == newValue
  hashValue := some hash

/-- Return `true` when a recomputed value should propagate. -/
def shouldPropagate (cutoff : Cutoff α) (oldValue newValue : α) : Bool :=
  !cutoff.shouldCutoff oldValue newValue

end Cutoff

/--
Public metadata for one graph node.

This is mainly useful for debugging, graph export, and external scheduling
logic. Ordinary library users usually work with `Incr`, `Var`, `Observer`, and
`State` instead.
-/
structure NodeInfo where
  /-- Stable numeric node identifier inside its `State`. -/
  id : Nat
  /-- Implementation kind for this node. -/
  kind : NodeKind
  /-- Height used by the recompute queue; children have smaller heights. -/
  height : Nat
  /-- Nodes this node reads from. -/
  children : Array Nat
  /-- Nodes that directly depend on this node. -/
  parents : Array Nat
  /-- Whether this node is on a path to an active observer. -/
  necessary : Bool
  /-- Whether this node needs recomputation before its value is stable. -/
  stale : Bool
  /-- Whether this node is currently valid. -/
  valid : Bool
  /-- Stabilization number in which this node was last recomputed. -/
  computedAt : Option Nat
  /-- Stabilization number in which this node's value last changed. -/
  changedAt : Option Nat
  /-- Stabilization number currently visiting this node, if any. -/
  visitingAt : Option Nat
  /-- Most recent stabilization epoch where this node was explicitly touched by external code. -/
  lastAccessedAt : Option Nat
  /-- Optional external dirtying reason recorded for scheduler integration. -/
  externalDirtyReason : Option String
  /-- Free-form scheduler tags associated with this node. -/
  tags : Array String
deriving Repr

/-- Controls what happens when a registered callback handler throws an exception. -/
inductive HandlerFailureMode where
  /-- Record the failure as a trace event and continue stabilization (default). -/
  | traceOnly
  /-- Record the failure as a trace event and then re-throw, aborting stabilization. -/
  | failFast
deriving Repr, BEq

/-- Structured trace payload for scheduler-facing state transitions. -/
inductive StateTraceEventKind where
  /-- A node was marked stale, optionally carrying an external reason. -/
  | markedStale : Option String -> StateTraceEventKind
  /-- A node was explicitly invalidated. -/
  | invalidated : StateTraceEventKind
  /-- A node finished recomputation; `true` means the value changed. -/
  | recomputed : Bool -> StateTraceEventKind
  /-- A node rewrote its dependency list. -/
  | dependencyRewrite : Array Nat -> Array Nat -> StateTraceEventKind
  /-- A registered callback threw and was isolated from stabilization. -/
  | handlerFailed : String -> String -> StateTraceEventKind
  /-- A deferred mutation was dropped because its queued epoch no longer matches
      the epoch being applied; the `stabilization` field of the enclosing event
      carries the stale epoch that was stored in the mutation. -/
  | deferredDropped : StateTraceEventKind
deriving Repr, BEq

/-- Deferred mutation requested while stabilization is running. -/
inductive DeferredMutation where
  /-- Mark one node stale; optional reason overrides node metadata reason. -/
  | markStale : Nat -> Option String -> Option Nat -> DeferredMutation
  /-- Invalidate one node; optional reason is used for the paired stale trace event. -/
  | invalidate : Nat -> Option String -> Option Nat -> DeferredMutation
deriving Repr, BEq

/-- One scheduler-facing trace record emitted by runtime graph transitions. -/
structure StateTraceEvent where
  /-- Node affected by this event. -/
  nodeId : Nat
  /-- Stabilization epoch associated with the event, if any. -/
  stabilization : Option Nat
  /-- Event payload. -/
  kind : StateTraceEventKind
deriving Repr, BEq

/-- Controls how many scheduler trace events are retained in `State`. -/
inductive TraceMode where
  /-- Do not retain scheduler trace events. -/
  | off
  /-- Retain at most the most recent `n` scheduler trace events. -/
  | bounded : Nat -> TraceMode
  /-- Retain every scheduler trace event until explicitly cleared. -/
  | unbounded
deriving Repr, BEq

/-- Type-erased node data stored inside `State`. Internal runtime detail. -/
structure PackedNode where
  /-- Mutable diagnostic metadata for this node. -/
  infoRef : IO.Ref NodeInfo
  /-- Registered necessary/unnecessary transition callbacks. -/
  observabilityHandlers : IO.Ref (Array (Bool -> IO Unit))
  /-- Return whether this node currently has a cached value. -/
  hasValue : IO Bool
  /-- Clear this node's cached value, returning `true` iff one was cleared. -/
  clearValue : IO Bool
  /-- Whether this node can safely recompute after its cache is cleared. -/
  canRecomputeAfterClear : Bool
  /-- Recompute this node for the supplied stabilization number. -/
  recompute : Nat -> IO Bool

/-- Type-erased observer data stored inside `State`. Internal runtime detail. -/
structure PackedObserver where
  /-- Id of the observed node. -/
  nodeId : Nat
  /-- Return whether the observer is still active. -/
  isActive : IO Bool
  /-- Return whether the observer has published an initial value. -/
  isInitialized : IO Bool
  /-- Write `lastValue` and collect pending user callbacks; fire the returned actions after releasing the write lock. -/
  refreshAndCollect : IO (Array (IO Unit))

/-- Internal height-ordered recompute queue storage. -/
structure RecomputeHeap where
  /-- Height-indexed node ids waiting to be recomputed. -/
  buckets : IO.Ref (Array (Array Nat))
  /-- Membership table used to suppress duplicate enqueues. -/
  members : IO.Ref (Std.HashMap Nat Unit)
  /-- Lowest bucket index that may still contain pending work. -/
  nextHeight : IO.Ref Nat
  /-- Number of queued recompute roots. -/
  sizeRef : IO.Ref Nat

/--
Mutable state for one independent incremental world.

Most users create a `State` and then interact with it through helper functions
such as `State.stabilize`, `Var.create`, and `observe`, rather than reading or
writing these fields directly.
-/
structure State where
  /-- All allocated nodes in this incremental world. -/
  nodes : IO.Ref (Array PackedNode)
  /-- Generation number for each node slot; increments every time a slot is reclaimed. -/
  nodeGenerations : IO.Ref (Array Nat)
  /-- Recycled node-slot ids available for reuse by future allocations. -/
  recycledNodeIdsRef : IO.Ref (Array Nat)
  /-- Internal necessity refcounts; positive counts imply `NodeInfo.necessary = true`. -/
  necessaryRefCounts : IO.Ref (Array Nat)
  /-- Necessary nodes that are currently stale (set-backed for O(1) membership updates). -/
  staleNecessaryIdsRef : IO.Ref (Std.HashMap Nat Unit)
  /-- All observers registered in this incremental world. -/
  observers : IO.Ref (Array PackedObserver)
  /-- Scheduler tag index, mapping each tag to ascending node ids. -/
  tagIndexRef : IO.Ref (Std.HashMap String (Array Nat))
  /-- Callbacks for dependency rewrites on existing nodes. -/
  dependencyChangeHandlers : IO.Ref (Array (Nat -> Array Nat -> Array Nat -> IO Unit))
  /-- Queue of necessary stale nodes. -/
  recomputeHeap : RecomputeHeap
  /-- Necessary stale or valueless nodes pending enqueue before fresh stabilization (set-backed). -/
  pendingDirtyRef : IO.Ref (Std.HashMap Nat Unit)
  /-- Controls whether scheduler trace events are retained and how many are buffered. -/
  traceModeRef : IO.Ref TraceMode
  /-- Scheduler trace events (ring-backed when bounded mode is full). -/
  traceEventsRef : IO.Ref (Array StateTraceEvent)
  /-- Logical index of the oldest retained trace event in `traceEventsRef`. -/
  traceEventsStartRef : IO.Ref Nat
  /-- Deferred node mutations queued during stabilization. -/
  deferredMutationsRef : IO.Ref (Array DeferredMutation)
  /-- Current recursion stack used for cycle diagnostics. -/
  visitStack : IO.Ref (Array Nat)
  /-- Monotone stabilization counter. -/
  stabilizationNum : IO.Ref Nat
  /-- Stabilization number for an incomplete budgeted stabilization, if any. -/
  partialStabilization : IO.Ref (Option Nat)
  /-- Whether `State.stabilize` is currently running. -/
  stabilizing : IO.Ref Bool
  /-- Controls how handler (callback) exceptions are handled during stabilization. -/
  handlerFailureModeRef : IO.Ref HandlerFailureMode
  /-- Count of `stabilizeOne` entries in the current pass; reset at fresh pass start. -/
  nodesVisitedRef : IO.Ref Nat
  /-- Count of observer refreshes in the current pass; reset at fresh pass start. -/
  observersRefreshedRef : IO.Ref Nat
  /-- Map from node id to the indices (in `observers`) of observers watching that node. -/
  observersByNode : IO.Ref (Std.HashMap Nat (Array Nat))
  /-- Node ids whose value changed during the current pass (per-pass; cleared after refresh). -/
  changedNodeIdsRef : IO.Ref (Array Nat)
  /-- Indices of newly created observers pending their first refresh. -/
  newObserverIdsRef : IO.Ref (Array Nat)
  /-- Pin refcounts: node id → count of active pins; pinned nodes are not reclaimed by GC. -/
  pinnedIdsRef : IO.Ref (Std.HashMap Nat Nat)
  /-- Whether per-recompute timing is enabled. -/
  timingModeRef : IO.Ref Bool
  /-- Per-pass timing records: (node id, nanoseconds). Reset at fresh pass start. -/
  lastPassTimingsRef : IO.Ref (Array (Nat × Nat))
  /-- Reader-writer lock: stabilize/Var.set hold the write side; Observer.value holds the read side. -/
  stateLock : Std.BaseSharedMutex

/-- An incremental value of type `α` that belongs to a `State`. -/
structure Incr (α : Type) where
  /-- The state that owns this node. -/
  state : State
  /-- Node id inside `state`. -/
  id : Nat
  /-- Generation captured when this handle was created. -/
  generation : Nat
  /-- Cached stable value, if available. -/
  valueRef : IO.Ref (Option α)
  /-- Cutoff used after recomputation. -/
  cutoffRef : IO.Ref (Cutoff α)
  /-- Cached hash digest of the last written value (used by `Cutoff.ofCachedDigest`). -/
  digestRef : IO.Ref (Option UInt64)

/-- A mutable input variable whose watched incremental tracks the latest set value. -/
structure Var (α : Type) where
  /-- The state that owns this variable. -/
  state : State
  /-- Latest value assigned by user code. -/
  current : IO.Ref α
  /-- Incremental node that tracks this variable. -/
  watch : Incr α

/-- Updates delivered to observer callbacks after stabilization. -/
inductive ObserverUpdate (α : Type) where
  /-- The observer received its first stable value. -/
  | initialized : α -> ObserverUpdate α
  /-- The observer changed from the old value to the new value. -/
  | changed : α -> α -> ObserverUpdate α
  /-- The observed node was invalidated. -/
  | invalidated : ObserverUpdate α
deriving Repr

/-- An active observation of an incremental value. -/
structure Observer (α : Type) where
  /-- The state that owns this observer. -/
  state : State
  /-- Observed incremental node. -/
  node : Incr α
  /-- Whether this observer can still be used. -/
  active : IO.Ref Bool
  /-- Last value published to the observer after stabilization. -/
  lastValue : IO.Ref (Option α)
  /-- Registered update callbacks. -/
  handlers : IO.Ref (Array (ObserverUpdate α -> IO Unit))
  /-- Index of this observer in `state.observers` (used for eager cleanup). -/
  indexInState : Nat

/-- Whether a clock is before or after a requested time boundary. -/
inductive BeforeOrAfter where
  /-- The clock time is still before the boundary. -/
  | before
  /-- The clock time has reached or passed the boundary. -/
  | after
deriving Repr, BEq

/-- A deterministic `Nat`-time clock backed by an incremental variable. -/
structure Clock where
  /-- The state that owns this clock. -/
  state : State
  /-- Mutable clock time variable. -/
  nowVar : Var Nat

end Leancremental
