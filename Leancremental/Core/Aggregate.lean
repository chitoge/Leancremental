import Leancremental.Core.Basic

/-!
Indexed aggregate nodes for query-style workloads.

The first implementation keeps keyed entries in insertion order and recomputes
the full aggregate when any member changes. It still gives LSP-style clients a
stable node for outputs such as diagnostics, symbols, and semantic tokens while
leaving partial-delta maintenance as a future optimization.
-/

namespace Leancremental

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
  if <- State.amStabilizing aggregate.state then
    Internal.throwUser "cannot mutate an indexed aggregate while stabilization is running"
  if <- State.hasPartialStabilization aggregate.state then
    Internal.throwUser "cannot mutate an indexed aggregate while a budgeted stabilization is incomplete"

/-- Create an empty indexed aggregate. -/
def create [BEq κ]
    (state : State) (init : β) (combine : β -> κ -> α -> β) : IO (IndexedAggregate κ α β) := do
  let entries <- IO.mkRef #[]
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun _ => do
    let currentEntries <- entries.get
    let mut acc := init
    for entry in currentEntries do
      let value <- Incr.value! entry.2
      acc := combine acc entry.1 value
    Internal.writeValue valueRef cutoffRef acc
  let id <- Internal.State.registerNode state NodeKind.fold #[] recompute hasValue true
  pure { state := state, entries := entries, node := { state := state, id := id, valueRef := valueRef, cutoffRef := cutoffRef } }

/-- Watch the aggregate result. -/
def watch [BEq κ] (aggregate : IndexedAggregate κ α β) : Incr β :=
  aggregate.node

/-- Return the number of keyed entries in the aggregate. -/
def size [BEq κ] (aggregate : IndexedAggregate κ α β) : IO Nat := do
  pure (← aggregate.entries.get).size

/-- Insert or replace one keyed member, preserving insertion order for existing keys. -/
def insertOrReplace [BEq κ] (aggregate : IndexedAggregate κ α β) (key : κ) (node : Incr α) : IO Unit := do
  ensureCanMutate aggregate
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
end Leancremental