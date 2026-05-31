import Leancremental.Core.State

/-! Core incremental values, variables, and combinators. -/

namespace Leancremental

namespace Incr

/-- Return the currently cached value, if this node has one. -/
def value? (node : Incr α) : IO (Option α) :=
  node.valueRef.get

/--
Return the cached value even if the node is currently marked stale.

This is an explicit alias for latency-sensitive clients, such as editor tooling,
that want to show a last-known value while a newer stabilization is pending.
-/
def staleValue? (node : Incr α) : IO (Option α) :=
  node.valueRef.get

/-- Return the currently cached value or an explanatory error string. -/
def value (node : Incr α) : IO (Except String α) := do
  match <- node.valueRef.get with
  | some value => pure (.ok value)
  | none => pure (.error s!"incremental node {node.id} has no stable value")

/-- Return the currently cached value, raising `IO.userError` if none is available. -/
def value! (node : Incr α) : IO α :=
  Internal.readValue node

/-- Set the cutoff used to decide whether recomputed values propagate. -/
def setCutoff (node : Incr α) (cutoff : Cutoff α) : IO Unit :=
  node.cutoffRef.set cutoff

/-- Read the node's current cutoff. -/
def getCutoff (node : Incr α) : IO (Cutoff α) :=
  node.cutoffRef.get

/-- Return whether this node is currently necessary for an active observer. -/
def isNecessary (node : Incr α) : IO Bool := do
  let info <- Internal.State.getInfo node.state node.id
  pure info.necessary

/-- Return whether this node is currently marked stale. -/
def isStale (node : Incr α) : IO Bool := do
  let info <- Internal.State.getInfo node.state node.id
  pure info.stale

/-- Return this node's current graph height. -/
def height (node : Incr α) : IO Nat := do
  let info <- Internal.State.getInfo node.state node.id
  pure info.height

/--
Register a callback for transitions into and out of the necessary set.

The callback receives `true` when the node becomes necessary and `false` when it
becomes unnecessary.
-/
def onObservabilityChange (node : Incr α) (handler : Bool -> IO Unit) : IO Unit := do
  let packed <- Internal.State.getNode node.state node.id
  packed.observabilityHandlers.modify (fun handlers => handlers.push handler)

end Incr

/-- Create an incremental constant whose value never changes. -/
def const (state : State) (value : α) : IO (Incr α) := do
  let valueRef <- IO.mkRef (some value)
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => pure false
  let id <- Internal.State.registerNode state NodeKind.const #[] recompute hasValue false
  pure { state := state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Alias for `const`, named to avoid Lean's `return` syntax keyword. -/
def ret (state : State) (value : α) : IO (Incr α) :=
  const state value

namespace Var

/-- Create a mutable input variable in `state`. -/
def create (state : State) (initial : α) : IO (Var α) := do
  let current <- IO.mkRef initial
  let valueRef <- IO.mkRef (some initial)
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let value <- current.get
    Internal.writeValue valueRef cutoffRef value
  let id <- Internal.State.registerNode state NodeKind.var #[] recompute hasValue false
  pure { state := state, current := current, watch := { state := state, id := id, valueRef := valueRef, cutoffRef := cutoffRef } }

/-- Set the variable's latest value and mark its watch node stale. -/
def set (var : Var α) (value : α) : IO Unit := do
  var.current.set value
  Internal.State.markNodeStale var.state var.watch.id

/-- Replace the variable's latest value by applying a function to it. -/
def replace (var : Var α) (f : α -> α) : IO Unit := do
  let value <- var.current.get
  set var (f value)

/-- Return the latest value set on the variable. -/
def value (var : Var α) : IO α :=
  var.current.get

end Var

/-- Map a pure function over an incremental value. -/
def map (node : Incr α) (f : α -> β) : IO (Incr β) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let value <- Incr.value! node
    Internal.writeValue valueRef cutoffRef (f value)
  let id <- Internal.State.registerNode node.state NodeKind.map #[node.id] recompute hasValue true
  pure { state := node.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Map a binary pure function over two incremental values. -/
def map2 (left : Incr α) (right : Incr β) (f : α -> β -> γ) : IO (Incr γ) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let leftValue <- Incr.value! left
    let rightValue <- Incr.value! right
    Internal.writeValue valueRef cutoffRef (f leftValue rightValue)
  let id <- Internal.State.registerNode left.state NodeKind.map2 #[left.id, right.id] recompute hasValue true
  pure { state := left.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Map a ternary pure function over three incremental values. -/
def map3 (first : Incr α) (second : Incr β) (third : Incr γ) (f : α -> β -> γ -> δ) : IO (Incr δ) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let firstValue <- Incr.value! first
    let secondValue <- Incr.value! second
    let thirdValue <- Incr.value! third
    Internal.writeValue valueRef cutoffRef (f firstValue secondValue thirdValue)
  let id <- Internal.State.registerNode first.state NodeKind.map3 #[first.id, second.id, third.id] recompute hasValue true
  pure { state := first.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Map a four-argument pure function over four incremental values. -/
def map4
    (first : Incr α)
    (second : Incr β)
    (third : Incr γ)
    (fourth : Incr δ)
    (f : α -> β -> γ -> δ -> ε) : IO (Incr ε) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let firstValue <- Incr.value! first
    let secondValue <- Incr.value! second
    let thirdValue <- Incr.value! third
    let fourthValue <- Incr.value! fourth
    Internal.writeValue valueRef cutoffRef (f firstValue secondValue thirdValue fourthValue)
  let id <- Internal.State.registerNode first.state NodeKind.map4 #[first.id, second.id, third.id, fourth.id] recompute hasValue true
  pure { state := first.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Map a five-argument pure function over five incremental values. -/
def map5
    (first : Incr α)
    (second : Incr β)
    (third : Incr γ)
    (fourth : Incr δ)
    (fifth : Incr ε)
    (f : α -> β -> γ -> δ -> ε -> ζ) : IO (Incr ζ) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let firstValue <- Incr.value! first
    let secondValue <- Incr.value! second
    let thirdValue <- Incr.value! third
    let fourthValue <- Incr.value! fourth
    let fifthValue <- Incr.value! fifth
    Internal.writeValue valueRef cutoffRef (f firstValue secondValue thirdValue fourthValue fifthValue)
  let id <- Internal.State.registerNode first.state NodeKind.map5 #[first.id, second.id, third.id, fourth.id, fifth.id] recompute hasValue true
  pure { state := first.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Pair two incremental values. -/
def both (left : Incr α) (right : Incr β) : IO (Incr (α × β)) :=
  map2 left right (fun leftValue rightValue => (leftValue, rightValue))

/-- Return `node`'s value while also making `dependency` necessary whenever the result is necessary. -/
def dependOn (node : Incr α) (dependency : Incr β) : IO (Incr α) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let _dependencyValue <- Incr.value! dependency
    let value <- Incr.value! node
    Internal.writeValue valueRef cutoffRef value
  let id <- Internal.State.registerNode node.state NodeKind.map2 #[node.id, dependency.id] recompute hasValue true
  pure { state := node.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Fold an array of incremental inputs, recomputing the whole fold when needed. -/
def arrayFold (state : State) (nodes : Array (Incr α)) (init : β) (f : β -> α -> β) : IO (Incr β) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let mut acc := init
    for node in nodes do
      let value <- Incr.value! node
      acc := f acc value
    Internal.writeValue valueRef cutoffRef acc
  let childIds := nodes.map (fun node => node.id)
  let id <- Internal.State.registerNode state NodeKind.fold childIds recompute hasValue true
  pure { state := state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

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

/-- Freeze an incremental at the first stabilization that computes the result. -/
def freeze (node : Incr α) : IO (Incr α) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
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
      let changed <- Internal.writeValue valueRef cutoffRef value
      frozenRef.set true
      Internal.State.setChildren node.state selfId #[]
      pure changed
  let id <- Internal.State.registerNode node.state NodeKind.freeze #[node.id] recompute hasValue true
  idRef.set (some id)
  pure { state := node.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Follow `node` until `trigger` is true, then freeze at the current value. -/
def freezeWhen (node : Incr α) (trigger : Incr Bool) : IO (Incr α) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
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
      let changed <- Internal.writeValue valueRef cutoffRef value
      if shouldFreeze then
        frozenRef.set true
        Internal.State.setChildren node.state selfId #[]
      pure changed
  let id <- Internal.State.registerNode node.state NodeKind.freeze #[node.id, trigger.id] recompute hasValue true
  idRef.set (some id)
  pure { state := node.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/--
Create an incremental whose dependency graph is selected by the current value of
another incremental.

When the left-hand side changes, the function is run again and the bind node is
rewired to the newly returned child.
-/
def bind (node : Incr α) (f : α -> IO (Incr β)) : IO (Incr β) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let currentChild <- IO.mkRef (none : Option (Incr β))
  let idRef <- IO.mkRef (none : Option Nat)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun stabilization => do
    let selfId <- match <- idRef.get with
      | some id => pure id
      | none => Internal.throwUser "bind node was recomputed before registration completed"
    Internal.State.stabilizeOne node.state stabilization node.id
    let lhsChanged <- Internal.State.nodeChangedAt node.state node.id stabilization
    let existingChild <- currentChild.get
    let child <-
      if lhsChanged || existingChild.isNone then
        let value <- Incr.value! node
        let newChild <- f value
        currentChild.set (some newChild)
        Internal.State.setChildren node.state selfId #[node.id, newChild.id]
        pure newChild
      else
        match existingChild with
        | some child => pure child
        | none => Internal.throwUser "unreachable bind child state"
    Internal.State.stabilizeOne node.state stabilization child.id
    let childValue <- Incr.value! child
    Internal.writeValue valueRef cutoffRef childValue
  let id <- Internal.State.registerNode node.state NodeKind.bind #[node.id] recompute hasValue true
  idRef.set (some id)
  pure { state := node.state, id := id, valueRef := valueRef, cutoffRef := cutoffRef }

/-- Flatten an incremental that currently contains another incremental. -/
def join (node : Incr (Incr α)) : IO (Incr α) :=
  bind node (fun child => pure child)

/-- Select one of two branches dynamically; only the selected branch is necessary. -/
def ifThenElse (condition : Incr Bool) (thenNode elseNode : Incr α) : IO (Incr α) :=
  bind condition (fun conditionValue => pure (if conditionValue then thenNode else elseNode))

end Leancremental
