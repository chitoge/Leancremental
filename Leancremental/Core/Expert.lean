import Leancremental.Core.Basic

/-! Expert nodes with custom recomputation and dynamic dependencies. -/

namespace Leancremental
namespace Expert

/-- A dynamic dependency edge from a child incremental to an expert node. -/
structure Dependency (α : Type) where
  /-- The child incremental this dependency reads. -/
  node : Incr α
  /-- Optional callback run before the expert recomputes when the child changes. -/
  onChange : Option (α -> IO Unit)

structure PackedDependency where
  /-- Child node id for the dependency. -/
  nodeId : Nat
  /-- Run this dependency's change callback for a stabilization if needed. -/
  fireIfChanged : Nat -> IO Unit

/-- A low-level node with custom recomputation and dynamic dependencies. -/
structure Node (α : Type) where
  state : State
  incr : Incr α
  dependencies : IO.Ref (Array PackedDependency)

namespace Dependency

/-- Create a dependency descriptor for an expert node. -/
def create (node : Incr α) (onChange : Option (α -> IO Unit) := none) : Dependency α :=
  { node := node, onChange := onChange }

/-- Read the dependency's current stable value. -/
def value (dependency : Dependency α) : IO α :=
  Incr.value! dependency.node

end Dependency

namespace Node

/-- Watch an expert node as an ordinary incremental. -/
def watch (node : Node α) : Incr α :=
  node.incr

/-- Return the ids of the current expert dependencies. -/
def dependencyIds (node : Node α) : IO (Array Nat) := do
  let dependencies <- node.dependencies.get
  pure (dependencies.map (fun dependency => dependency.nodeId))

/-- Create an expert node with a custom recomputation action. -/
def create (state : State) (compute : IO α) : IO (Node α) := do
  let valueRef <- IO.mkRef none
  let cutoffRef <- IO.mkRef Cutoff.never
  let dependencies <- IO.mkRef #[]
  let hasValue := do pure ((<- valueRef.get).isSome)
  let recompute := fun stabilization => do
    let deps <- dependencies.get
    for dependency in deps do
      dependency.fireIfChanged stabilization
    let value <- compute
    Internal.writeValue valueRef cutoffRef value
  let id <- Internal.State.registerNode state NodeKind.expert #[] recompute hasValue true
  pure {
    state := state,
    incr := { state := state, id := id, valueRef := valueRef, cutoffRef := cutoffRef },
    dependencies := dependencies
  }

/-- Add a dynamic dependency to an expert node. -/
def addDependency (node : Node α) (dependency : Dependency β) : IO Unit := do
  let deps <- node.dependencies.get
  if deps.any (fun existing => existing.nodeId == dependency.node.id) then
    pure ()
  else
    let fireIfChanged := fun stabilization => do
      if <- Internal.State.nodeChangedAt node.state dependency.node.id stabilization then
        match dependency.onChange with
        | none => pure ()
        | some handler => handler (← Dependency.value dependency)
    node.dependencies.set (deps.push { nodeId := dependency.node.id, fireIfChanged := fireIfChanged })
    Internal.State.setChildren node.state node.incr.id (← dependencyIds node)

/-- Remove a dynamic dependency from an expert node. -/
def removeDependency (node : Node α) (dependency : Dependency β) : IO Unit := do
  let deps <- node.dependencies.get
  node.dependencies.set (deps.filter (fun existing => existing.nodeId != dependency.node.id))
  Internal.State.setChildren node.state node.incr.id (← dependencyIds node)

/-- Mark an expert node stale so it will recompute when necessary. -/
def makeStale (node : Node α) : IO Unit := do
  Internal.State.markNodeStale node.state node.incr.id
  if (← Incr.isNecessary node.incr) && (← State.amStabilizing node.state) then
    Internal.State.enqueueRecompute node.state node.incr.id

/-- Invalidate an expert node's cached value and mark it stale. -/
def invalidate (node : Node α) : IO Unit := do
  node.incr.valueRef.set none
  Internal.State.modifyInfo node.state node.incr.id (fun info => { info with valid := false, stale := true, computedAt := none })
  if (← Incr.isNecessary node.incr) && (← State.amStabilizing node.state) then
    Internal.State.enqueueRecompute node.state node.incr.id

end Node
end Expert
end Leancremental
