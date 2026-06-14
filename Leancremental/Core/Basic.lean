import Leancremental.Core.State

/-!
Core incremental values, variables, and graph-building combinators.
-/

namespace Leancremental

namespace Incr

def ensureCurrent (node : Incr α) : IO Unit := do
  let generation <- Internal.State.nodeGeneration node.state node.id
  if generation != node.generation then
    Internal.throwUser s!"incremental node {node.id} handle is stale after node reclamation"

def ensureCanMutateNode (node : Incr α) : IO Unit := do
  ensureCurrent node
  if <- State.amStabilizing node.state then
    Internal.throwUser "cannot mutate an incremental node while stabilization is running"
  if <- State.hasPartialStabilization node.state then
    Internal.throwUser "cannot mutate an incremental node while a budgeted stabilization is incomplete"

def clearValueRef (valueRef : IO.Ref (Option α)) : IO Bool := do
  match <- valueRef.get with
  | none => pure false
  | some _ =>
      valueRef.set none
      pure true

/--
Return `some v` only if this node has a computed, non-stale value; return `none`
if the node has never been computed or if it is currently stale (i.e., a
`Var.set` on an ancestor has not yet been stabilized).

To read the last cached value regardless of staleness — for example, to show a
previous result while a new stabilization is pending — use `staleValue?`.
-/
def value? (node : Incr α) : IO (Option α) := do
  ensureCurrent node
  let info ← Internal.State.getInfo node.state node.id
  if info.stale then pure none
  else node.valueRef.get

/--
Return the last cached value for this node even if it is currently stale.

Returns `none` only if the node has never been computed. Use this when you
intentionally want the previous result while a newer stabilization is pending
(e.g., latency-sensitive UI that shows stale-while-revalidating fallbacks).
For a guarantee that the value is fresh, use `value?` or call `State.stabilize`
first.
-/
def staleValue? (node : Incr α) : IO (Option α) := do
  ensureCurrent node
  node.valueRef.get

/-- Return the currently cached value or an explanatory error string. -/
def value (node : Incr α) : IO (Except String α) := do
  ensureCurrent node
  match <- node.valueRef.get with
  | some value => pure (.ok value)
  | none => pure (.error s!"incremental node {node.id} has no stable value")

/-- Return the currently cached value, raising `IO.userError` if none is available. -/
def value! (node : Incr α) : IO α := do
  ensureCurrent node
  Internal.readValue node

/-- Set the cutoff used to decide whether recomputed values propagate. -/
def setCutoff (node : Incr α) (cutoff : Cutoff α) : IO Unit := do
  ensureCurrent node
  node.cutoffRef.set cutoff

/-- Read the node's current cutoff. -/
def getCutoff (node : Incr α) : IO (Cutoff α) := do
  ensureCurrent node
  node.cutoffRef.get

/-- Return whether this node is currently necessary for an active observer. -/
def isNecessary (node : Incr α) : IO Bool := do
  ensureCurrent node
  let info <- Internal.State.getInfo node.state node.id
  pure info.necessary

/-- Return whether this node is currently marked stale. -/
def isStale (node : Incr α) : IO Bool := do
  ensureCurrent node
  let info <- Internal.State.getInfo node.state node.id
  pure info.stale

/-- Return this node's current graph height. -/
def height (node : Incr α) : IO Nat := do
  ensureCurrent node
  let info <- Internal.State.getInfo node.state node.id
  pure info.height

/--
Register a callback for transitions into and out of the necessary set.

The callback receives `true` when the node becomes necessary and `false` when it
becomes unnecessary.
-/
def onObservabilityChange (node : Incr α) (handler : Bool -> IO Unit) : IO Unit := do
  ensureCurrent node
  let packed <- Internal.State.getNode node.state node.id
  packed.observabilityHandlers.modify (fun handlers => handlers.push handler)

/-- Mark a node and its parents stale so they will recompute on the next stabilization. -/
def markStale (node : Incr α) : IO Unit := do
  ensureCurrent node
  if <- State.amStabilizing node.state then
    State.queueNodeMarkStale node.state node.id none
  else
    ensureCanMutateNode node
    Internal.State.markNodeStale node.state node.id
    Internal.State.markParentsStale node.state node.id

/-- Record an explicit external access at the current stabilization epoch. -/
def touch (node : Incr α) : IO Unit := do
  ensureCanMutateNode node
  let stabilization <- State.currentStabilization node.state
  Internal.State.modifyInfo node.state node.id (fun info => { info with lastAccessedAt := some stabilization })

/-- Attach an external dirty reason for scheduler integration. -/
def setExternalDirtyReason (node : Incr α) (reason : String) : IO Unit := do
  ensureCanMutateNode node
  Internal.State.modifyInfo node.state node.id (fun info => { info with externalDirtyReason := some reason })

/-- Clear the externally attached dirty reason. -/
def clearExternalDirtyReason (node : Incr α) : IO Unit := do
  ensureCanMutateNode node
  Internal.State.modifyInfo node.state node.id (fun info => { info with externalDirtyReason := none })

/-- Add a scheduler tag unless it is already present. -/
def addTag (node : Incr α) (tag : String) : IO Unit := do
  ensureCanMutateNode node
  let info <- Internal.State.getInfo node.state node.id
  if info.tags.any (fun existing => existing == tag) then
    pure ()
  else
    Internal.State.setInfo node.state node.id { info with tags := info.tags.push tag }
    Internal.State.addNodeTagIndex node.state node.id tag

/-- Remove all occurrences of a scheduler tag from this node. -/
def removeTag (node : Incr α) (tag : String) : IO Unit := do
  ensureCanMutateNode node
  let info <- Internal.State.getInfo node.state node.id
  if info.tags.any (fun existing => existing == tag) then
    Internal.State.setInfo node.state node.id {
      info with tags := info.tags.filter (fun existing => existing != tag)
    }
    Internal.State.removeNodeTagIndex node.state node.id tag
  else
    pure ()

/-- Return scheduler tags attached to this node. -/
def tags (node : Incr α) : IO (Array String) := do
  ensureCurrent node
  let info <- Internal.State.getInfo node.state node.id
  pure info.tags

/-- Return whether this node is reachable from active observers through graph edges. -/
def isReachableFromActiveObservers (node : Incr α) : IO Bool := do
  ensureCurrent node
  pure (Internal.containsNat (← State.reachableNodeIds node.state) node.id)

/-- Drop a node's cached value and mark it stale so it recomputes on the next stabilization. -/
def invalidate (node : Incr α) : IO Unit := do
  ensureCurrent node
  if <- State.amStabilizing node.state then
    State.queueNodeInvalidate node.state node.id none
  else
    ensureCanMutateNode node
    node.valueRef.set none
    Internal.State.invalidateNodeWith node.state node.id
    Internal.State.markParentsStale node.state node.id

end Incr

/--
Create an incremental constant whose value never changes.

**Cutoff default**: the `cutoff` parameter defaults to `Cutoff.never`, which
propagates on every recompute even when the value is unchanged. For a true
constant this rarely matters, but the parameter is available for consistency
with the other node constructors.
-/
def const (state : State) (value : α) (cutoff : Cutoff α := Cutoff.never) : IO (Incr α) := do
  let valueRef <- IO.mkRef (some value)
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => pure false
  let id <- Internal.State.registerNode state NodeKind.const #[] recompute hasValue (pure false) false false
  let generation <- Internal.State.nodeGeneration state id
  pure { state := state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/-- Alias for `const`, named to avoid Lean's `return` syntax keyword. -/
def ret (state : State) (value : α) (cutoff : Cutoff α := Cutoff.never) : IO (Incr α) :=
  const state value cutoff

namespace Var

/--
Create a mutable input variable in `state`.

**Cutoff default**: the `cutoff` parameter defaults to `Cutoff.never`, which
propagates downstream on every stabilization after `Var.set`, even when the new
value equals the old one. Pass `Cutoff.ofEq` or `Cutoff.ofHash` to stop
unnecessary downstream recomputation when inputs are set to the same value.

Cost: O(1) allocation plus node registration.

Thread-safety: intended for ordinary setup code. Graph construction is not
documented as generally thread-safe across threads.
-/
def create (state : State) (initial : α) (cutoff : Cutoff α := Cutoff.never) : IO (Var α) := do
  let current <- IO.mkRef initial
  let valueRef <- IO.mkRef (some initial)
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let value <- current.get
    Internal.writeValue valueRef cutoffRef digestRef value
  let id <- Internal.State.registerNode state NodeKind.var #[] recompute hasValue (Incr.clearValueRef valueRef) true false
  let generation <- Internal.State.nodeGeneration state id
  pure {
    state := state,
    current := current,
    watch := { state := state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }
  }

private def setLocked (var : Var α) (value : α) : IO Unit := do
  Incr.ensureCurrent var.watch
  var.current.set value
  Internal.State.markNodeStale var.state var.watch.id

/--
Set the variable's latest value and mark its watch node stale.

Thread-safety: serialized through the state's write lock.
Cost: expected O(1) aside from the cost of the stored value and downstream
recomputation, which happens later during stabilization.
-/
def set (var : Var α) (value : α) : IO Unit := do
  var.state.stateLock.write
  try
    setLocked var value
  finally
    var.state.stateLock.unlockWrite

/--
Replace the variable's latest value by applying a function to it.

Thread-safety: serialized through the state's write lock.
Cost: expected O(1) plus the cost of `f`, aside from downstream recomputation
which happens later during stabilization.
-/
def replace (var : Var α) (f : α -> α) : IO Unit := do
  var.state.stateLock.write
  try
    let value <- var.current.get
    setLocked var (f value)
  finally
    var.state.stateLock.unlockWrite

/--
Return the latest value written to this variable.

**Clock difference**: this reads the write-side input, not the stabilized graph
value. After `Var.set x v` but before `State.stabilize`, `Var.value x` returns
`v` while any observer downstream of `x` still shows the previous stabilized
value. Read through an observer to get a value consistent with the last
completed `State.stabilize`.

This call intentionally does not take the state's read lock, because that would
deadlock inside some expert-node recomputations.
-/
def value (var : Var α) : IO α :=
  var.current.get

end Var

/--
Build a derived node by applying `f` to one incremental input.

Cost: O(1) node allocation. Recompute cost is the cost of reading the input and
running `f`.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. Pass `Cutoff.ofEq` for types with `BEq`, or
`Cutoff.ofHash` for larger types, to stop unnecessary downstream work.
-/
def map (node : Incr α) (f : α -> β) (cutoff : Cutoff β := Cutoff.never) : IO (Incr β) := do
  Incr.ensureCurrent node
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let value <- Incr.value! node
    Internal.writeValue valueRef cutoffRef digestRef (f value)
  let id <- Internal.State.registerNode node.state NodeKind.map #[node.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  let generation <- Internal.State.nodeGeneration node.state id
  pure { state := node.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/--
Build a derived node by applying `f` to two incremental inputs.

All inputs must belong to the same `State`; mixing nodes from different states
is detected at construction time and raises `IO.userError`.

Cost: O(1) node allocation. Recompute cost is the cost of reading both inputs
and running `f`.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. See `map` for details.
-/
def map2 (left : Incr α) (right : Incr β) (f : α -> β -> γ) (cutoff : Cutoff γ := Cutoff.never) : IO (Incr γ) := do
  Incr.ensureCurrent left
  Incr.ensureCurrent right
  Internal.State.requireSameState left.state right.state "map2"
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let leftValue <- Incr.value! left
    let rightValue <- Incr.value! right
    Internal.writeValue valueRef cutoffRef digestRef (f leftValue rightValue)
  let id <- Internal.State.registerNode left.state NodeKind.map2 #[left.id, right.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  let generation <- Internal.State.nodeGeneration left.state id
  pure { state := left.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/--
Build a derived node by applying `f` to three incremental inputs.

All inputs must belong to the same `State`; mixing nodes from different states
is detected at construction time and raises `IO.userError`.

Cost: O(1) node allocation. Recompute cost is the cost of reading the inputs
and running `f`.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. See `map` for details.
-/
def map3 (first : Incr α) (second : Incr β) (third : Incr γ) (f : α -> β -> γ -> δ) (cutoff : Cutoff δ := Cutoff.never) : IO (Incr δ) := do
  Incr.ensureCurrent first
  Incr.ensureCurrent second
  Incr.ensureCurrent third
  Internal.State.requireSameState first.state second.state "map3"
  Internal.State.requireSameState first.state third.state "map3"
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let firstValue <- Incr.value! first
    let secondValue <- Incr.value! second
    let thirdValue <- Incr.value! third
    Internal.writeValue valueRef cutoffRef digestRef (f firstValue secondValue thirdValue)
  let id <- Internal.State.registerNode first.state NodeKind.map3 #[first.id, second.id, third.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  let generation <- Internal.State.nodeGeneration first.state id
  pure { state := first.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/--
Build a derived node by applying `f` to four incremental inputs.

All inputs must belong to the same `State`; mixing nodes from different states
is detected at construction time and raises `IO.userError`.

Cost: O(1) node allocation. Recompute cost is the cost of reading the inputs
and running `f`.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. See `map` for details.
-/
def map4
    (first : Incr α)
    (second : Incr β)
    (third : Incr γ)
    (fourth : Incr δ)
    (f : α -> β -> γ -> δ -> ε)
    (cutoff : Cutoff ε := Cutoff.never) : IO (Incr ε) := do
  Incr.ensureCurrent first
  Incr.ensureCurrent second
  Incr.ensureCurrent third
  Incr.ensureCurrent fourth
  Internal.State.requireSameState first.state second.state "map4"
  Internal.State.requireSameState first.state third.state "map4"
  Internal.State.requireSameState first.state fourth.state "map4"
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let firstValue <- Incr.value! first
    let secondValue <- Incr.value! second
    let thirdValue <- Incr.value! third
    let fourthValue <- Incr.value! fourth
    Internal.writeValue valueRef cutoffRef digestRef (f firstValue secondValue thirdValue fourthValue)
  let id <- Internal.State.registerNode first.state NodeKind.map4 #[first.id, second.id, third.id, fourth.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  let generation <- Internal.State.nodeGeneration first.state id
  pure { state := first.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/--
Build a derived node by applying `f` to five incremental inputs.

All inputs must belong to the same `State`; mixing nodes from different states
is detected at construction time and raises `IO.userError`.

Cost: O(1) node allocation. Recompute cost is the cost of reading the inputs
and running `f`.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. See `map` for details.
-/
def map5
    (first : Incr α)
    (second : Incr β)
    (third : Incr γ)
    (fourth : Incr δ)
    (fifth : Incr ε)
    (f : α -> β -> γ -> δ -> ε -> ζ)
    (cutoff : Cutoff ζ := Cutoff.never) : IO (Incr ζ) := do
  Incr.ensureCurrent first
  Incr.ensureCurrent second
  Incr.ensureCurrent third
  Incr.ensureCurrent fourth
  Incr.ensureCurrent fifth
  Internal.State.requireSameState first.state second.state "map5"
  Internal.State.requireSameState first.state third.state "map5"
  Internal.State.requireSameState first.state fourth.state "map5"
  Internal.State.requireSameState first.state fifth.state "map5"
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let firstValue <- Incr.value! first
    let secondValue <- Incr.value! second
    let thirdValue <- Incr.value! third
    let fourthValue <- Incr.value! fourth
    let fifthValue <- Incr.value! fifth
    Internal.writeValue valueRef cutoffRef digestRef (f firstValue secondValue thirdValue fourthValue fifthValue)
  let id <- Internal.State.registerNode first.state NodeKind.map5 #[first.id, second.id, third.id, fourth.id, fifth.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  let generation <- Internal.State.nodeGeneration first.state id
  pure { state := first.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/-- Pair the current values of two incremental nodes. -/
def both (left : Incr α) (right : Incr β) : IO (Incr (α × β)) :=
  map2 left right (fun leftValue rightValue => (leftValue, rightValue))

/--
Return `node`'s value while also keeping `dependency` alive whenever the result
is observed.

Use this when the output should depend on `dependency` for scheduling or
liveness reasons even though its value is not used directly.

**Cross-state**: `node` and `dependency` must belong to the same `State`.
Passing nodes from different states raises `IO.userError` at construction time.
-/
def dependOn (node : Incr α) (dependency : Incr β) : IO (Incr α) := do
  Incr.ensureCurrent node
  Incr.ensureCurrent dependency
  Internal.State.requireSameState node.state dependency.state "dependOn"
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let _dependencyValue <- Incr.value! dependency
    let value <- Incr.value! node
    Internal.writeValue valueRef cutoffRef digestRef value
  let id <- Internal.State.registerNode node.state NodeKind.map2 #[node.id, dependency.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  let generation <- Internal.State.nodeGeneration node.state id
  pure { state := node.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/--
Fold an array of incremental inputs into one incremental result.

This is a simple full recompute fold: if any input changes, the whole fold is
recomputed on the next stabilization.

All nodes must belong to `state`; mixing nodes from different states is detected
at construction time and raises `IO.userError`.

Cost: O(n) in the number of input nodes for each recomputation.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. See `map` for details.
-/
def arrayFold (state : State) (nodes : Array (Incr α)) (init : β) (f : β -> α -> β) : IO (Incr β) := do
  for node in nodes do
    Incr.ensureCurrent node
    Internal.State.requireSameState state node.state "arrayFold"
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let mut acc := init
    for node in nodes do
      let value <- Incr.value! node
      acc := f acc value
    Internal.writeValue valueRef cutoffRef digestRef acc
  let childIds := nodes.map (fun node => node.id)
  let id <- Internal.State.registerNode state NodeKind.fold childIds recompute hasValue (Incr.clearValueRef valueRef) true true
  let generation <- Internal.State.nodeGeneration state id
  pure { state := state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/-- Collect the values of an array of incrementals into an incremental array. -/
def all (state : State) (nodes : Array (Incr α)) : IO (Incr (Array α)) :=
  arrayFold state nodes #[] (fun acc value => acc.push value)

/-- Return an incremental that is true iff all input booleans are true. -/
def forAll (state : State) (nodes : Array (Incr Bool)) : IO (Incr Bool) :=
  arrayFold state nodes true (fun acc value => acc && value)

/-- Return an incremental that is true iff any input boolean is true. -/
def existsAny (state : State) (nodes : Array (Incr Bool)) : IO (Incr Bool) :=
  arrayFold state nodes false (fun acc value => acc || value)

/-- Sum an array of `Nat` incrementals. -/
def sumNat (state : State) (nodes : Array (Incr Nat)) : IO (Incr Nat) :=
  arrayFold state nodes 0 (fun acc value => acc + value)

/-- Sum an array of incrementals for any type with `0` and `+`. -/
def sum [OfNat α 0] [Add α] (state : State) (nodes : Array (Incr α)) : IO (Incr α) :=
  arrayFold state nodes 0 (fun acc value => acc + value)

/-- Sum an array of `Float` incrementals. -/
def sumFloat (state : State) (nodes : Array (Incr Float)) : IO (Incr Float) :=
  sum state nodes

/--
Capture the first computed value of `node` and then stop following later
changes.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. See `map` for details.
-/
def freeze (node : Incr α) (cutoff : Cutoff α := Cutoff.never) : IO (Incr α) := do
  Incr.ensureCurrent node
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let frozenRef <- IO.mkRef false
  let idRef <- IO.mkRef (none : Option Nat)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    if <- frozenRef.get then
      pure false
    else
      let selfId <- match <- idRef.get with
        | some id => pure id
        | none => Internal.throwUser "freeze node was recomputed before registration completed"
      let value <- Incr.value! node
      let changed <- Internal.writeValue valueRef cutoffRef digestRef value
      frozenRef.set true
      Internal.State.setChildren node.state selfId #[]
      pure changed
  let id <- Internal.State.registerNode node.state NodeKind.freeze #[node.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  idRef.set (some id)
  let generation <- Internal.State.nodeGeneration node.state id
  pure { state := node.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/--
Follow `node` until `trigger` becomes true, then keep the value seen at that
stabilization.

`node` and `trigger` must belong to the same `State`; mixing nodes from
different states is detected at construction time and raises `IO.userError`.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. See `map` for details.
-/
def freezeWhen (node : Incr α) (trigger : Incr Bool) (cutoff : Cutoff α := Cutoff.never) : IO (Incr α) := do
  Incr.ensureCurrent node
  Incr.ensureCurrent trigger
  Internal.State.requireSameState node.state trigger.state "freezeWhen"
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let frozenRef <- IO.mkRef false
  let idRef <- IO.mkRef (none : Option Nat)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    if <- frozenRef.get then
      pure false
    else
      let selfId <- match <- idRef.get with
        | some id => pure id
        | none => Internal.throwUser "freezeWhen node was recomputed before registration completed"
      let shouldFreeze <- Incr.value! trigger
      let value <- Incr.value! node
      let changed <- Internal.writeValue valueRef cutoffRef digestRef value
      if shouldFreeze then
        frozenRef.set true
        Internal.State.setChildren node.state selfId #[]
      pure changed
  let id <- Internal.State.registerNode node.state NodeKind.freeze #[node.id, trigger.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  idRef.set (some id)
  let generation <- Internal.State.nodeGeneration node.state id
  pure { state := node.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/--
Create an incremental whose dependency graph is selected by the current value of
another incremental.

When the input changes, `f` is run again and the bind node switches to the newly
returned child graph.

This is the main combinator for dynamic graph structure.

**Node accumulation**: each rewire calls `f` and creates a new child subgraph.
The previous child nodes are abandoned but not freed automatically. Call
`State.reclaimUnreachableNodes` periodically in long-running programs that
rewire `bind` frequently to prevent unbounded node growth.

**Cross-state**: `f` must return a node from the same `State` as `node`. A
cross-state return is detected at recompute time and raises `IO.userError`.

Cost: O(1) node allocation up front. During stabilization it may trigger extra
work to rewire dependencies before the final value is refreshed.

**Cutoff default**: `Cutoff.never` propagates on every recompute even when the
output value is unchanged. See `map` for details.
-/
def bind (node : Incr α) (f : α -> IO (Incr β)) (cutoff : Cutoff β := Cutoff.never) : IO (Incr β) := do
  Incr.ensureCurrent node
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef cutoff
  let digestRef <- IO.mkRef (none : Option UInt64)
  let currentChild <- IO.mkRef (none : Option (Incr β))
  let pendingRewireRef <- IO.mkRef false
  let rewiredAtRef <- IO.mkRef (none : Option Nat)
  let idRef <- IO.mkRef (none : Option Nat)
  let hasValue := do
    if <- pendingRewireRef.get then
      pure false
    else
      pure ((<- valueRef.get).isSome)
  let recompute := fun stabilization => do
    let selfId <- match <- idRef.get with
      | some id => pure id
      | none => Internal.throwUser "bind node was recomputed before registration completed"
    let lhsChanged <- Internal.State.nodeChangedAt node.state node.id stabilization
    let existingChild <- currentChild.get
    let rewiredAt <- rewiredAtRef.get
    let shouldRewire := existingChild.isNone || (lhsChanged && rewiredAt != some stabilization)
    if shouldRewire then
      -- Two-phase bind: first rewrite dependencies, then let bottom-up heap
      -- order stabilize the selected child before this bind finalizes output.
      let value <- Incr.value! node
      let newChild <- f value
      Incr.ensureCurrent newChild
      Internal.State.requireSameState node.state newChild.state "bind"
      currentChild.set (some newChild)
      rewiredAtRef.set (some stabilization)
      pendingRewireRef.set true
      Internal.State.setChildren node.state selfId #[node.id, newChild.id]
      -- Keep the previous output cached; `hasValue` reports missing while
      -- rewiring so this node finalizes on a second pass.
      pure false
    else
      let child <-
        match existingChild with
        | some child => pure child
        | none => Internal.throwUser "unreachable bind child state"
      let childValue <- Incr.value! child
      let changed <- Internal.writeValue valueRef cutoffRef digestRef childValue
      pendingRewireRef.set false
      pure changed
  let id <- Internal.State.registerNode node.state NodeKind.bind #[node.id] recompute hasValue (Incr.clearValueRef valueRef) true true
  idRef.set (some id)
  let generation <- Internal.State.nodeGeneration node.state id
  pure { state := node.state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }

/-- Flatten an incremental that currently contains another incremental node. -/
def join (node : Incr (Incr α)) (cutoff : Cutoff α := Cutoff.never) : IO (Incr α) :=
  bind node (fun child => pure child) cutoff

/--
Select one of two branches dynamically.

Only the selected branch is necessary, so changes in the inactive branch do not
propagate until the condition switches.
-/
def ifThenElse
    (condition : Incr Bool)
    (thenNode elseNode : Incr α)
    (cutoff : Cutoff α := Cutoff.never) : IO (Incr α) :=
  bind condition (fun conditionValue => pure (if conditionValue then thenNode else elseNode)) cutoff

end Leancremental
