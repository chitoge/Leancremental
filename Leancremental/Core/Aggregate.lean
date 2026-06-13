import Std.Data.HashMap
import Leancremental.Core.Basic

/-!
Indexed aggregate nodes for query-style workloads.

Use these when you want one stable incremental output for a keyed collection,
such as diagnostics, symbols, or semantic tokens.

`IndexedAggregate` uses straightforward full refolds. `AssocIndexedAggregate`
adds an associative variant with better update behavior for suitable reducers.
-/

namespace Leancremental

private def ensureAggregateCanMutate (state : State) (name : String) : IO Unit := do
  if <- State.amStabilizing state then
    Internal.throwUser s!"cannot mutate {name} while stabilization is running"
  if <- State.hasPartialStabilization state then
    Internal.throwUser s!"cannot mutate {name} while a budgeted stabilization is incomplete"

def aggregateEntryIds (entries : Array (κ × Incr α)) : Array Nat :=
  entries.map (fun entry => entry.2.id)

def aggregateContainsKey [BEq κ] (entries : Array (κ × Incr α)) (key : κ) : Bool :=
  entries.any (fun entry => entry.1 == key)

def aggregateUpsert [BEq κ] (entries : Array (κ × Incr α)) (key : κ) (node : Incr α) : Array (κ × Incr α) :=
  if aggregateContainsKey entries key then
    entries.map (fun entry => if entry.1 == key then (key, node) else entry)
  else
    entries.push (key, node)

def aggregateErase [BEq κ] (entries : Array (κ × Incr α)) (key : κ) : Array (κ × Incr α) :=
  entries.filter (fun entry => entry.1 != key)

/-- A keyed aggregate with a stable output node. -/
structure IndexedAggregate (κ : Type) (α : Type) (β : Type) [BEq κ] where
  /-- State that owns the aggregate node and all member nodes. -/
  state : State
  /-- Current keyed entries in stable insertion order. -/
  entries : IO.Ref (Array (κ × Incr α))
  /-- Incremental aggregate result. -/
  node : Incr β

namespace IndexedAggregate

def ensureCanMutate [BEq κ] (aggregate : IndexedAggregate κ α β) : IO Unit := do
  ensureAggregateCanMutate aggregate.state "an indexed aggregate"

/-- Create an empty indexed aggregate. -/
def create [BEq κ]
    (state : State) (init : β) (combine : β -> κ -> α -> β) : IO (IndexedAggregate κ α β) := do
  let entries <- IO.mkRef #[]
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let digestRef <- IO.mkRef (none : Option UInt64)
  let hasValue := do pure ((<- valueRef.get).isSome)
  let clearValue := Incr.clearValueRef valueRef
  let recompute := fun _ => do
    let currentEntries <- entries.get
    let mut acc := init
    for entry in currentEntries do
      let value <- Incr.value! entry.2
      acc := combine acc entry.1 value
    Internal.writeValue valueRef cutoffRef digestRef acc
  let id <- Internal.State.registerNode state NodeKind.fold #[] recompute hasValue clearValue true true
  let generation <- Internal.State.nodeGeneration state id
  pure {
    state := state,
    entries := entries,
    node := { state := state, id := id, generation := generation, valueRef := valueRef, cutoffRef := cutoffRef, digestRef := digestRef }
  }

/-- Watch the aggregate result. -/
def watch [BEq κ] (aggregate : IndexedAggregate κ α β) : Incr β :=
  aggregate.node

/-- Return the number of keyed entries in the aggregate. -/
def size [BEq κ] (aggregate : IndexedAggregate κ α β) : IO Nat := do
  pure (← aggregate.entries.get).size

/-- Insert or replace one keyed member, preserving insertion order for existing keys. -/
def insertOrReplace [BEq κ] (aggregate : IndexedAggregate κ α β) (key : κ) (node : Incr α) : IO Unit := do
  ensureCanMutate aggregate
  Incr.ensureCurrent node
  let nextEntries := aggregateUpsert (← aggregate.entries.get) key node
  aggregate.entries.set nextEntries
  Internal.State.setChildren aggregate.state aggregate.node.id (aggregateEntryIds nextEntries)

/-- Remove one keyed member, returning whether an entry was removed. -/
def remove [BEq κ] (aggregate : IndexedAggregate κ α β) (key : κ) : IO Bool := do
  ensureCanMutate aggregate
  let entries <- aggregate.entries.get
  let nextEntries := aggregateErase entries key
  if nextEntries.size == entries.size then
    pure false
  else
    aggregate.entries.set nextEntries
    Internal.State.setChildren aggregate.state aggregate.node.id (aggregateEntryIds nextEntries)
    pure true

/-- Remove all keyed members, returning the number removed. -/
def clear [BEq κ] (aggregate : IndexedAggregate κ α β) : IO Nat := do
  ensureCanMutate aggregate
  let entries <- aggregate.entries.get
  aggregate.entries.set #[]
  Internal.State.setChildren aggregate.state aggregate.node.id #[]
  pure entries.size

end IndexedAggregate

structure AssocAggregateSlot (σ : Type) where
  /-- Stable proxy whose current child can be rewired without replacing the slot node. -/
  proxy : Var (Incr σ)
  /-- Stable slot node watched by the balanced aggregate tree. -/
  node : Incr σ

/--
A keyed aggregate specialized for associative reducers.

New keys receive fresh slot indexes until `clear`; removing a key rewires its slot
to the identity summary instead of compacting the remaining slots. That keeps the
combine tree shape stable across ordinary inserts and removes while preserving
the insertion order of currently active entries.
-/
structure AssocIndexedAggregate (κ : Type) (α : Type) (σ : Type) [BEq κ] [Hashable κ] where
  /-- State that owns the aggregate graph. -/
  state : State
  /-- Active key to slot assignments. -/
  entries : IO.Ref (Std.HashMap κ Nat)
  /-- Stable slot proxies consumed by the combine tree. -/
  slots : IO.Ref (Array (AssocAggregateSlot σ))
  /-- Next insertion slot; reset by `clear`. -/
  nextSlot : IO.Ref Nat
  /-- Number of active keyed entries. -/
  activeSize : IO.Ref Nat
  /-- Shared identity summary used by empty slots. -/
  emptyNode : Incr σ
  /-- Stable root proxy rewired only when the tree capacity grows. -/
  rootProxy : Var (Incr σ)
  /-- Stable aggregate output node. -/
  node : Incr σ
  /-- Per-entry summary function. -/
  summarize : κ -> α -> σ
  /-- Associative combiner over summaries. -/
  combine : σ -> σ -> σ

namespace AssocIndexedAggregate

def ensureCanMutate [BEq κ] [Hashable κ] (aggregate : AssocIndexedAggregate κ α σ) : IO Unit := do
  ensureAggregateCanMutate aggregate.state "an associative indexed aggregate"

private def createSlot (state : State) (initial : Incr σ) : IO (AssocAggregateSlot σ) := do
  let proxy <- Var.create state initial
  let node <- join (Var.watch proxy)
  pure { proxy := proxy, node := node }

private def buildNextLevel
    (combine : σ -> σ -> σ)
    (nodes : Array (Incr σ)) : IO (Array (Incr σ)) := do
  let mut next := #[]
  let mut index := 0
  while index < nodes.size do
    let some left := nodes[index]?
      | Internal.throwUser "associative aggregate tree construction lost its left child"
    if index + 1 < nodes.size then
      let some right := nodes[index + 1]?
        | Internal.throwUser "associative aggregate tree construction lost its right child"
      let parent <- map2 left right combine
      next := next.push parent
      index := index + 2
    else
      next := next.push left
      index := index + 1
  pure next

private def buildTree
    (combine : σ -> σ -> σ)
    (emptyNode : Incr σ)
    (leaves : Array (Incr σ)) : IO (Incr σ) := do
  if leaves.isEmpty then
    pure emptyNode
  else
    let mut level := leaves
    while level.size > 1 do
      level <- buildNextLevel combine level
    let some root := level[0]?
      | pure emptyNode
    pure root

private def getSlot! [BEq κ] [Hashable κ] (aggregate : AssocIndexedAggregate κ α σ) (slot : Nat) : IO (AssocAggregateSlot σ) := do
  let some slotInfo := (← aggregate.slots.get)[slot]?
    | Internal.throwUser s!"associative indexed aggregate lost slot {slot}"
  pure slotInfo

private def setSlotNode [BEq κ] [Hashable κ] (aggregate : AssocIndexedAggregate κ α σ) (slot : Nat) (node : Incr σ) : IO Unit := do
  let slotInfo <- getSlot! aggregate slot
  Var.set slotInfo.proxy node

private def ensureCapacity [BEq κ] [Hashable κ] (aggregate : AssocIndexedAggregate κ α σ) (needed : Nat) : IO Unit := do
  let currentSlots <- aggregate.slots.get
  if needed <= currentSlots.size then
    pure ()
  else
    let mut target := max 1 currentSlots.size
    while target < needed do
      target := target * 2
    let mut nextSlots := currentSlots
    while nextSlots.size < target do
      let slot <- createSlot aggregate.state aggregate.emptyNode
      nextSlots := nextSlots.push slot
    aggregate.slots.set nextSlots
    let root <- buildTree aggregate.combine aggregate.emptyNode (nextSlots.map (fun slot => slot.node))
    Var.set aggregate.rootProxy root

private def summaryNode [BEq κ] [Hashable κ]
    (aggregate : AssocIndexedAggregate κ α σ)
    (key : κ)
    (node : Incr α) : IO (Incr σ) := do
  Incr.ensureCurrent node
  map node (fun value => aggregate.summarize key value)

/-- Create an empty associative indexed aggregate with a stable output node. -/
def create [BEq κ] [Hashable κ]
    (state : State)
    (empty : σ)
    (summarize : κ -> α -> σ)
    (combine : σ -> σ -> σ) : IO (AssocIndexedAggregate κ α σ) := do
  let entries <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap κ Nat)
  let slots <- IO.mkRef #[]
  let nextSlot <- IO.mkRef 0
  let activeSize <- IO.mkRef 0
  let emptyNode <- const state empty
  let rootProxy <- Var.create state emptyNode
  let node <- join (Var.watch rootProxy)
  pure {
    state := state,
    entries := entries,
    slots := slots,
    nextSlot := nextSlot,
    activeSize := activeSize,
    emptyNode := emptyNode,
    rootProxy := rootProxy,
    node := node,
    summarize := summarize,
    combine := combine
  }

/-- Watch the aggregate result. -/
def watch [BEq κ] [Hashable κ] (aggregate : AssocIndexedAggregate κ α σ) : Incr σ :=
  aggregate.node

/-- Return the number of active keyed entries in the aggregate. -/
def size [BEq κ] [Hashable κ] (aggregate : AssocIndexedAggregate κ α σ) : IO Nat :=
  aggregate.activeSize.get

/--
Insert or replace one keyed member.

Replacing a key keeps its existing slot. A fresh key uses the next insertion slot
so active keys keep their original relative order even after removals.
-/
def insertOrReplace [BEq κ] [Hashable κ]
    (aggregate : AssocIndexedAggregate κ α σ)
    (key : κ)
    (node : Incr α) : IO Unit := do
  ensureCanMutate aggregate
  let summarized <- summaryNode aggregate key node
  let entries <- aggregate.entries.get
  match entries.get? key with
  | some slot =>
      setSlotNode aggregate slot summarized
  | none =>
      let slot <- aggregate.nextSlot.get
      ensureCapacity aggregate (slot + 1)
      aggregate.entries.set (entries.insert key slot)
      aggregate.nextSlot.set (slot + 1)
      aggregate.activeSize.modify (fun size => size + 1)
      setSlotNode aggregate slot summarized

/-- Remove one keyed member, returning whether an entry was removed. -/
def remove [BEq κ] [Hashable κ] (aggregate : AssocIndexedAggregate κ α σ) (key : κ) : IO Bool := do
  ensureCanMutate aggregate
  let entries <- aggregate.entries.get
  match entries.get? key with
  | none =>
      pure false
  | some slot =>
      aggregate.entries.set (entries.erase key)
      aggregate.activeSize.modify (fun size => size - 1)
      setSlotNode aggregate slot aggregate.emptyNode
      pure true

/--
Remove all keyed members, returning the number removed.

`clear` keeps the existing capacity but resets the insertion frontier so future
keys can reuse slots from the start.
-/
def clear [BEq κ] [Hashable κ] (aggregate : AssocIndexedAggregate κ α σ) : IO Nat := do
  ensureCanMutate aggregate
  let entries <- aggregate.entries.get
  for entry in entries.toList do
    setSlotNode aggregate entry.2 aggregate.emptyNode
  aggregate.entries.set (Std.HashMap.emptyWithCapacity : Std.HashMap κ Nat)
  aggregate.nextSlot.set 0
  aggregate.activeSize.set 0
  pure entries.size

end AssocIndexedAggregate
end Leancremental
