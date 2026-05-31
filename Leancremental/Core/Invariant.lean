import Leancremental.Core.State

/-!
Executable graph invariant checks inspired by OCaml Incremental's implementation notes.

These predicates capture the subset of Incremental's documented invariants that
Leancremental's current runtime represents directly: bidirectional edges, height
ordering, necessary-closure, timestamp ordering, recompute-heap sanity, and
post-stabilization stability for necessary nodes.
-/

namespace Leancremental

namespace CoreInvariant

/-- Return whether an array of node ids contains `id`. -/
def containsId (ids : Array Nat) (id : Nat) : Bool :=
  ids.any (fun candidate => candidate == id)

/-- Return whether `id` names an allocated node in `infos`. -/
def validId (infos : Array NodeInfo) (id : Nat) : Bool :=
  id < infos.size

/-- Timestamp invariant: a change time cannot be later than the recomputation that observed it. -/
def timestampsOrdered (info : NodeInfo) : Bool :=
  match info.changedAt, info.computedAt with
  | none, _ => true
  | some _, none => false
  | some changed, some computed => changed <= computed

/-- Pure violations that can be checked from public `NodeInfo` snapshots alone. -/
def infoViolations (requireStableNecessary : Bool) (infos : Array NodeInfo) : Array String := Id.run do
  let mut messages := #[]
  for index in [:infos.size] do
    match infos[index]? with
    | none =>
        messages := messages.push s!"missing node info at index {index}"
    | some info =>
        if info.id != index then
          messages := messages.push s!"node at index {index} has id {info.id}"
        if !timestampsOrdered info then
          messages := messages.push s!"node {info.id} changed after its last recomputation"
        if requireStableNecessary && info.necessary && info.stale then
          messages := messages.push s!"necessary node {info.id} is still stale"
        for childId in info.children do
          match infos[childId]? with
          | none =>
              messages := messages.push s!"node {info.id} has unknown child {childId}"
          | some child =>
              if !containsId child.parents info.id then
                messages := messages.push s!"node {info.id} lists child {childId}, but the child does not list it as a parent"
              if !(child.height < info.height) then
                messages := messages.push s!"node {info.id} height {info.height} is not greater than child {childId} height {child.height}"
              if info.necessary && !child.necessary then
                messages := messages.push s!"necessary node {info.id} has unnecessary child {childId}"
        for parentId in info.parents do
          match infos[parentId]? with
          | none =>
              messages := messages.push s!"node {info.id} has unknown parent {parentId}"
          | some parent =>
              if !containsId parent.children info.id then
                messages := messages.push s!"node {info.id} lists parent {parentId}, but the parent does not list it as a child"
  messages

/-- True when public node metadata satisfies the basic graph invariants. -/
def infoInvariant (infos : Array NodeInfo) : Bool :=
  (infoViolations false infos).isEmpty

/-- True when public node metadata also satisfies the post-stabilization stability invariant. -/
def stableInfoInvariant (infos : Array NodeInfo) : Bool :=
  (infoViolations true infos).isEmpty

/-- Empty violations are exactly the boolean basic metadata invariant. -/
theorem infoInvariant_iff_no_violations (infos : Array NodeInfo) :
    infoInvariant infos = (infoViolations false infos).isEmpty := rfl

/-- Empty violations are exactly the boolean stable metadata invariant. -/
theorem stableInfoInvariant_iff_no_violations (infos : Array NodeInfo) :
    stableInfoInvariant infos = (infoViolations true infos).isEmpty := rfl

end CoreInvariant

namespace State

/-- Snapshot all public node metadata from a state. -/
def nodeInfos (state : State) : IO (Array NodeInfo) := do
  let nodes <- state.nodes.get
  let mut infos := #[]
  for index in [:nodes.size] do
    infos := infos.push (← Internal.State.getInfo state index)
  pure infos

/-- Basic graph invariant violations for the current state. -/
def invariantViolations (state : State) : IO (Array String) := do
  let infos <- nodeInfos state
  let mut messages := CoreInvariant.infoViolations false infos
  let entries <- state.recomputeHeap.entries.get
  let mut seenEntries := #[]
  for id in entries do
    if CoreInvariant.containsId seenEntries id then
      messages := messages.push s!"recompute heap contains duplicate node {id}"
    else
      seenEntries := seenEntries.push id
    match infos[id]? with
    | none =>
        messages := messages.push s!"recompute heap contains unknown node {id}"
    | some info =>
        if !info.necessary then
          messages := messages.push s!"recompute heap contains unnecessary node {id}"
        if !info.stale then
          messages := messages.push s!"recompute heap contains non-stale node {id}"
  let observers <- state.observers.get
  for observer in observers do
    if <- observer.isActive then
      match infos[observer.nodeId]? with
      | none =>
          messages := messages.push s!"active observer points at unknown node {observer.nodeId}"
      | some info =>
          if !info.necessary then
            messages := messages.push s!"active observer points at unnecessary node {observer.nodeId}"
  pure messages

/-- Post-stabilization invariant violations for the current state. -/
def stableInvariantViolations (state : State) : IO (Array String) := do
  let mut messages <- invariantViolations state
  let nodes <- state.nodes.get
  for index in [:nodes.size] do
    let node <- Internal.State.getNode state index
    let info <- node.infoRef.get
    if info.necessary then
      if info.stale then
        messages := messages.push s!"necessary node {info.id} is still stale"
      if !(← node.hasValue) then
        messages := messages.push s!"necessary node {info.id} has no cached value"
  pure messages

/-- Throw an `IO.userError` if `violations` is non-empty. -/
def throwIfViolations (context : String) (violations : Array String) : IO Unit := do
  if violations.isEmpty then
    pure ()
  else
    Internal.throwUser (context ++ ":\n" ++ Internal.joinWith "\n" violations.toList)

/-- Check the basic graph invariants for the current state. -/
def checkInvariants (state : State) : IO Unit := do
  throwIfViolations "Leancremental invariant violation" (← invariantViolations state)

/-- Check the stronger post-stabilization invariants for the current state. -/
def checkStableInvariants (state : State) : IO Unit := do
  throwIfViolations "Leancremental stable invariant violation" (← stableInvariantViolations state)

end State

end Leancremental
