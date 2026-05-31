/-!
Shared public and implementation types for Leancremental's executable core.
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

/-- Return `true` when a recomputed value should propagate. -/
def shouldPropagate (cutoff : Cutoff α) (oldValue newValue : α) : Bool :=
  !cutoff.shouldCutoff oldValue newValue

end Cutoff

/-- Public diagnostic metadata for a node in the incremental graph. -/
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
deriving Repr

/-- Type-erased node data stored inside `State`. Mostly useful for implementers. -/
structure PackedNode where
  /-- Mutable diagnostic metadata for this node. -/
  infoRef : IO.Ref NodeInfo
  /-- Registered necessary/unnecessary transition callbacks. -/
  observabilityHandlers : IO.Ref (Array (Bool -> IO Unit))
  /-- Return whether this node currently has a cached value. -/
  hasValue : IO Bool
  /-- Recompute this node for the supplied stabilization number. -/
  recompute : Nat -> IO Bool

/-- Type-erased observer action stored inside `State`. Mostly useful for implementers. -/
structure PackedObserver where
  /-- Id of the observed node. -/
  nodeId : Nat
  /-- Return whether the observer is still active. -/
  isActive : IO Bool
  /-- Refresh the observer after stabilization. -/
  refresh : IO Unit

/-- Internal height-ordered recompute queue storage. -/
structure RecomputeHeap where
  /-- Node ids waiting to be recomputed; the dequeue operation chooses minimum height. -/
  entries : IO.Ref (Array Nat)

/-- Mutable graph state for an independent Leancremental world. -/
structure State where
  /-- All allocated nodes in this incremental world. -/
  nodes : IO.Ref (Array PackedNode)
  /-- All observers registered in this incremental world. -/
  observers : IO.Ref (Array PackedObserver)
  /-- Queue of necessary stale nodes. -/
  recomputeHeap : RecomputeHeap
  /-- Current recursion stack used for cycle diagnostics. -/
  visitStack : IO.Ref (Array Nat)
  /-- Monotone stabilization counter. -/
  stabilizationNum : IO.Ref Nat
  /-- Stabilization number for an incomplete budgeted stabilization, if any. -/
  partialStabilization : IO.Ref (Option Nat)
  /-- Whether `State.stabilize` is currently running. -/
  stabilizing : IO.Ref Bool

/-- An incremental value of type `α` that belongs to a `State`. -/
structure Incr (α : Type) where
  /-- The state that owns this node. -/
  state : State
  /-- Node id inside `state`. -/
  id : Nat
  /-- Cached stable value, if available. -/
  valueRef : IO.Ref (Option α)
  /-- Cutoff used after recomputation. -/
  cutoffRef : IO.Ref (Cutoff α)

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
