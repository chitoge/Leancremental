import Leancremental.Core.Basic

/-! Observer creation and observer value access. -/

namespace Leancremental
namespace Observer

/-- Start observing a node, making it and its dependencies necessary. -/
def observe (node : Incr α) : IO (Observer α) := do
  let active <- IO.mkRef true
  let lastValue <- IO.mkRef none
  let handlers <- IO.mkRef #[]
  let observer : Observer α := {
    state := node.state,
    node := node,
    active := active,
    lastValue := lastValue,
    handlers := handlers
  }
  let refresh := do
    if <- active.get then
      match <- node.valueRef.get with
      | none => pure ()
      | some value =>
          let oldValue <- lastValue.get
          let callbacks <- handlers.get
          match oldValue with
          | none =>
              lastValue.set (some value)
              for callback in callbacks do
                callback (.initialized value)
          | some old =>
              let stabilization <- node.state.stabilizationNum.get
              let changed <- Internal.State.nodeChangedAt node.state node.id stabilization
              if changed then
                lastValue.set (some value)
                for callback in callbacks do
                  callback (.changed old value)
              else
                pure ()
    else
      pure ()
  let packed : PackedObserver := { nodeId := node.id, isActive := active.get, refresh := refresh }
  node.state.observers.modify (fun observers => observers.push packed)
  Internal.State.markNecessary node.state node.id
  pure observer

/-- Return the last stable observed value, if the observer is active and initialized. -/
def value? (observer : Observer α) : IO (Option α) := do
  if <- observer.active.get then
    observer.lastValue.get
  else
    pure none

/-- Return the last stable observed value or an explanatory error string. -/
def value (observer : Observer α) : IO (Except String α) := do
  if !(<- observer.active.get) then
    pure (.error "observer has been disallowed")
  else
    match <- observer.lastValue.get with
    | some value => pure (.ok value)
    | none => pure (.error "observer has no value; call State.stabilize first")

/-- Return the last stable observed value, raising `IO.userError` on failure. -/
def value! (observer : Observer α) : IO α := do
  match <- value observer with
  | .ok value => pure value
  | .error message => Internal.throwUser message

/-- Register a callback that runs after stabilizations where the observer initializes or changes. -/
def onUpdate (observer : Observer α) (handler : ObserverUpdate α -> IO Unit) : IO Unit := do
  if !(<- observer.active.get) then
    Internal.throwUser "observer has been disallowed"
  observer.handlers.modify (fun handlers => handlers.push handler)

/-- Disable this observer so future stabilizations can make its graph unnecessary. -/
def disallowFutureUse (observer : Observer α) : IO Unit :=
  observer.active.set false

end Observer

/-- Start observing a node, making it and its dependencies necessary. -/
def observe (node : Incr α) : IO (Observer α) :=
  Observer.observe node

end Leancremental
