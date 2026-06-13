import Leancremental.Core.Basic

/-!
Observer creation, observer reads, and observer lifecycle operations.
-/

namespace Leancremental
namespace Observer

/--
Start observing a node.

Observing a node makes it and its dependencies necessary, so future
stabilizations keep that part of the graph up to date.

Thread-safety: observation registration mutates the owning `State`, so treat it
like graph construction rather than a free concurrent read.
-/
def observe (node : Incr α) : IO (Observer α) := do
  Incr.ensureCurrent node
  let active <- IO.mkRef true
  let lastValue <- IO.mkRef none
  let handlers <- IO.mkRef #[]
  -- Capture the index before pushing so the observer knows its own slot
  let index := (← node.state.observers.get).size
  let observer : Observer α := {
    state := node.state,
    node := node,
    active := active,
    lastValue := lastValue,
    handlers := handlers,
    indexInState := index
  }
  let refreshAndCollect : IO (Array (IO Unit)) := do
    if <- active.get then
      match <- node.valueRef.get with
      | none => pure #[]
      | some value =>
          let oldValue <- lastValue.get
          let callbacks <- handlers.get
          match oldValue with
          | none =>
              lastValue.set (some value)
              pure (callbacks.map (fun cb => cb (.initialized value)))
          | some old =>
              let stabilization <- node.state.stabilizationNum.get
              let changed <- Internal.State.nodeChangedAt node.state node.id stabilization
              if changed then
                lastValue.set (some value)
                pure (callbacks.map (fun cb => cb (.changed old value)))
              else
                pure #[]
    else
      pure #[]
  let isInitialized : IO Bool := do
    pure (Option.isSome (← lastValue.get))
  let packed : PackedObserver := {
    nodeId := node.id,
    isActive := active.get,
    isInitialized := isInitialized,
    refreshAndCollect := refreshAndCollect
  }
  node.state.observers.modify (fun observers => observers.push packed)
  -- Register this observer's index under its node id for targeted refresh
  node.state.observersByNode.modify (fun m =>
    m.insert node.id ((m.getD node.id #[]).push index))
  -- Queue for first refresh (initialization) on next stabilization
  node.state.newObserverIdsRef.modify (fun ids => ids.push index)
  Internal.State.retainNecessary node.state node.id
  pure observer

/--
Return the last stable observed value, if one has been published and the
observer is still active.

Thread-safety: uses the state's read lock.
Cost: O(1).
-/
def value? (observer : Observer α) : IO (Option α) := do
  observer.state.stateLock.read
  try
    if <- observer.active.get then
      observer.lastValue.get
    else
      pure none
  finally
    observer.state.stateLock.unlockRead

/--
Return the last stable observed value or an explanatory error string.

Before the first completed stabilization, an observer has no value yet.

Thread-safety: uses the state's read lock.
Cost: O(1).
-/
def value (observer : Observer α) : IO (Except String α) := do
  observer.state.stateLock.read
  try
    if !(<- observer.active.get) then
      pure (.error "observer has been disallowed")
    else
      match <- observer.lastValue.get with
      | some v => pure (.ok v)
      | none => pure (.error "observer has no value; call State.stabilize first")
  finally
    observer.state.stateLock.unlockRead

/--
Return the last stable observed value, raising `IO.userError` if unavailable.

Thread-safety: uses the state's read lock.
Cost: O(1).
-/
def value! (observer : Observer α) : IO α := do
  observer.state.stateLock.read
  try
    if !(<- observer.active.get) then
      Internal.throwUser "observer has been disallowed"
    match <- observer.lastValue.get with
    | some v => pure v
    | none => Internal.throwUser "observer has no value; call State.stabilize first"
  finally
    observer.state.stateLock.unlockRead

/--
Register a callback that runs after stabilizations where the observer first
publishes a value or later changes value.
-/
def onUpdate (observer : Observer α) (handler : ObserverUpdate α -> IO Unit) : IO Unit := do
  if !(<- observer.active.get) then
    Internal.throwUser "observer has been disallowed"
  observer.handlers.modify (fun handlers => handlers.push handler)

/--
Disable this observer.

After this, reads fail and future stabilizations may stop maintaining the
observer's part of the graph if nothing else still needs it.
-/
def disallowFutureUse (observer : Observer α) : IO Unit := do
  if <- observer.active.get then
    observer.active.set false
    -- Eagerly remove this observer from the node-index so refresh skips it
    let idx := observer.indexInState
    let nodeId := observer.node.id
    observer.state.observersByNode.modify (fun m =>
      m.insert nodeId ((m.getD nodeId #[]).filter (· != idx)))
    Internal.State.releaseNecessary observer.state observer.node.id
  else
    pure ()

end Observer

/-- Start observing a node. -/
def observe (node : Incr α) : IO (Observer α) :=
  Observer.observe node

end Leancremental
