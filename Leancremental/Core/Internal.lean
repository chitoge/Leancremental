import Leancremental.Core.Types

/-! Internal graph maintenance and stabilization helpers. -/

namespace Leancremental
namespace Internal

def throwUser (message : String) : IO α :=
  throw (IO.userError message)

def containsNat (xs : Array Nat) (x : Nat) : Bool :=
  xs.any (fun y => y == x)

def pushIfMissing (xs : Array Nat) (x : Nat) : Array Nat :=
  if containsNat xs x then xs else xs.push x

def eraseNat (xs : Array Nat) (x : Nat) : Array Nat :=
  xs.filter (fun y => y != x)

def dedupNat (xs : Array Nat) : Array Nat :=
  xs.foldl pushIfMissing #[]

def joinWith (separator : String) (parts : List String) : String :=
  match parts with
  | [] => ""
  | first :: rest => rest.foldl (fun acc part => acc ++ separator ++ part) first

partial def dropUntilNat (needle : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => if x == needle then x :: xs else dropUntilNat needle xs

def closeCyclePath (needle : Nat) (stack : Array Nat) : List Nat :=
  dropUntilNat needle stack.toList ++ [needle]

def formatCycle (cycle : List Nat) : String :=
  "cycle detected: " ++ joinWith " -> " (cycle.map (fun id => s!"n{id}"))

def State.getNode (state : State) (id : Nat) : IO PackedNode := do
  let nodes <- state.nodes.get
  match nodes[id]? with
  | some node => pure node
  | none => throwUser s!"unknown incremental node {id}"

def State.getInfo (state : State) (id : Nat) : IO NodeInfo := do
  let node <- State.getNode state id
  node.infoRef.get

def State.setInfo (state : State) (id : Nat) (info : NodeInfo) : IO Unit := do
  let node <- State.getNode state id
  node.infoRef.set info

def State.modifyInfo (state : State) (id : Nat) (f : NodeInfo -> NodeInfo) : IO Unit := do
  let info <- State.getInfo state id
  State.setInfo state id (f info)

def State.runObservabilityHandlers (state : State) (id : Nat) (isNowNecessary : Bool) : IO Unit := do
  let node <- State.getNode state id
  let handlers <- node.observabilityHandlers.get
  for handler in handlers do
    handler isNowNecessary

def State.enqueueRecompute (state : State) (id : Nat) : IO Unit := do
  let entries <- state.recomputeHeap.entries.get
  if containsNat entries id then
    pure ()
  else
    state.recomputeHeap.entries.set (entries.push id)

def State.clearRecomputeHeap (state : State) : IO Unit :=
  state.recomputeHeap.entries.set #[]

def State.heightOf (state : State) (id : Nat) : IO Nat := do
  let info <- State.getInfo state id
  pure info.height

def State.dequeueRecompute? (state : State) : IO (Option Nat) := do
  let entries <- state.recomputeHeap.entries.get
  if entries.isEmpty then
    pure none
  else
    let firstId := entries[0]!
    let mut minId := firstId
    let mut minIndex := 0
    let mut minHeight <- State.heightOf state firstId
    for index in [:entries.size] do
      let id := entries[index]!
      let height <- State.heightOf state id
      if height < minHeight then
        minId := id
        minIndex := index
        minHeight := height
    let mut rest := #[]
    for index in [:entries.size] do
      if index != minIndex then
        rest := rest.push entries[index]!
    state.recomputeHeap.entries.set rest
    pure (some minId)

def State.nodeChangedAt (state : State) (id stabilization : Nat) : IO Bool := do
  let info <- State.getInfo state id
  pure (info.changedAt == some stabilization)

def State.heightFromChildren (state : State) (children : Array Nat) : IO Nat := do
  let mut height := 0
  for child in children do
    let childHeight <- State.heightOf state child
    height := max height (childHeight + 1)
  pure height

partial def State.markNecessary (state : State) (id : Nat) : IO Unit := do
  let info <- State.getInfo state id
  if info.necessary then
    pure ()
  else
    State.setInfo state id { info with necessary := true }
    State.runObservabilityHandlers state id true
    for child in info.children do
      State.markNecessary state child

partial def State.collectNecessaryFrom (state : State) (seenRef : IO.Ref (Array Nat)) (id : Nat) : IO Unit := do
  let seen <- seenRef.get
  if containsNat seen id then
    pure ()
  else
    seenRef.set (seen.push id)
    let info <- State.getInfo state id
    for child in info.children do
      State.collectNecessaryFrom state seenRef child

def State.collectNecessary (state : State) : IO (Array Nat) := do
  let seenRef <- IO.mkRef #[]
  let observers <- state.observers.get
  for observer in observers do
    if <- observer.isActive then
      State.collectNecessaryFrom state seenRef observer.nodeId
  seenRef.get

partial def State.recomputeNecessary (state : State) : IO Unit := do
  let necessary <- State.collectNecessary state
  let nodes <- state.nodes.get
  for index in [:nodes.size] do
    let info <- State.getInfo state index
    let isNowNecessary := containsNat necessary index
    if info.necessary == isNowNecessary then
      pure ()
    else
      State.setInfo state index { info with necessary := isNowNecessary }
      State.runObservabilityHandlers state index isNowNecessary

def State.enqueueInitialRecomputes (state : State) : IO Unit := do
  let nodes <- state.nodes.get
  for index in [:nodes.size] do
    let node <- State.getNode state index
    let info <- node.infoRef.get
    let missingValue <- do pure (!(<- node.hasValue))
    if info.necessary && (info.stale || missingValue) then
      State.enqueueRecompute state index

partial def State.markParentsStale (state : State) (id : Nat) : IO Unit := do
  let info <- State.getInfo state id
  for parent in info.parents do
    let parentInfo <- State.getInfo state parent
    if !parentInfo.stale then
      State.setInfo state parent { parentInfo with stale := true }
    if parentInfo.necessary && (← state.stabilizing.get) then
      State.enqueueRecompute state parent

def State.markNodeStale (state : State) (id : Nat) : IO Unit := do
  State.modifyInfo state id (fun info => { info with stale := true })

def State.addParent (state : State) (child parent : Nat) : IO Unit := do
  State.modifyInfo state child (fun info => { info with parents := pushIfMissing info.parents parent })

def State.removeParent (state : State) (child parent : Nat) : IO Unit := do
  State.modifyInfo state child (fun info => { info with parents := eraseNat info.parents parent })

partial def State.setChildren (state : State) (parent : Nat) (children : Array Nat) : IO Unit := do
  let children := dedupNat children
  let info <- State.getInfo state parent
  for oldChild in info.children do
    if containsNat children oldChild then
      pure ()
    else
      State.removeParent state oldChild parent
  for child in children do
    State.addParent state child parent
  let height <- State.heightFromChildren state children
  State.setInfo state parent { info with children := children, height := height, stale := true }
  if info.necessary then
    State.recomputeNecessary state
    if <- state.stabilizing.get then
      State.enqueueRecompute state parent

def State.registerNode
    (state : State)
    (kind : NodeKind)
    (children : Array Nat)
    (recompute : Nat -> IO Bool)
    (hasValue : IO Bool)
    (initiallyStale : Bool) : IO Nat := do
  let children := dedupNat children
  let nodes <- state.nodes.get
  let id := nodes.size
  let height <- State.heightFromChildren state children
  let infoRef <- IO.mkRef {
    id := id,
    kind := kind,
    height := height,
    children := children,
    parents := #[],
    necessary := false,
    stale := initiallyStale,
    valid := true,
    computedAt := none,
    changedAt := none,
    visitingAt := none
  }
  let observabilityHandlers <- IO.mkRef #[]
  let packed : PackedNode := {
    infoRef := infoRef,
    observabilityHandlers := observabilityHandlers,
    hasValue := hasValue,
    recompute := recompute
  }
  state.nodes.set (nodes.push packed)
  for child in children do
    State.addParent state child id
  pure id

def readValue (node : Incr α) : IO α := do
  match <- node.valueRef.get with
  | some value => pure value
  | none => throwUser s!"incremental node {node.id} has no stable value"

def writeValue (valueRef : IO.Ref (Option α)) (cutoffRef : IO.Ref (Cutoff α)) (newValue : α) : IO Bool := do
  match <- valueRef.get with
  | none =>
      valueRef.set (some newValue)
      pure true
  | some oldValue =>
      let cutoff <- cutoffRef.get
      if cutoff.shouldCutoff oldValue newValue then
        pure false
      else
        valueRef.set (some newValue)
        pure true

partial def State.stabilizeOne (state : State) (stabilization id : Nat) : IO Unit := do
  let node <- State.getNode state id
  let info <- node.infoRef.get
  if info.computedAt == some stabilization then
    pure ()
  else if info.visitingAt == some stabilization then
    let stack <- state.visitStack.get
    throwUser (formatCycle (closeCyclePath id stack))
  else
    let previousStack <- state.visitStack.get
    state.visitStack.set (previousStack.push id)
    node.infoRef.set { info with visitingAt := some stabilization }
    try
      let computeRemainingChildren (children : Array Nat) := do
        for child in children do
          State.stabilizeOne state stabilization child
      match info.kind, info.children[0]? with
      | NodeKind.bind, some lhs =>
          State.stabilizeOne state stabilization lhs
          let lhsChanged <- State.nodeChangedAt state lhs stabilization
          if lhsChanged then
            pure ()
          else
            computeRemainingChildren (info.children.extract 1 info.children.size)
      | _, _ => computeRemainingChildren info.children
      let infoAfterChildren <- node.infoRef.get
      let missingValue <- do pure (!(<- node.hasValue))
      let changed <-
        if infoAfterChildren.stale || missingValue then
          node.recompute stabilization
        else
          pure false
      let infoAfterRecompute <- node.infoRef.get
      node.infoRef.set {
        infoAfterRecompute with
        stale := false,
        computedAt := some stabilization,
        changedAt := if changed then some stabilization else infoAfterRecompute.changedAt,
        visitingAt := none
      }
      state.visitStack.set previousStack
      if changed then
        State.markParentsStale state id
    catch error =>
      node.infoRef.set { (← node.infoRef.get) with visitingAt := none }
      state.visitStack.set previousStack
      throw error

partial def State.drainRecomputeHeap (state : State) (stabilization : Nat) : IO Unit := do
  match <- State.dequeueRecompute? state with
  | none => pure ()
  | some id =>
      let node <- State.getNode state id
      let info <- node.infoRef.get
      let missingValue <- do pure (!(<- node.hasValue))
      if info.necessary && (info.stale || missingValue) then
        State.stabilizeOne state stabilization id
      State.drainRecomputeHeap state stabilization

partial def State.drainRecomputeHeapWithBudget (state : State) (stabilization budget : Nat) : IO Nat := do
  if budget == 0 then
    pure 0
  else
    match <- State.dequeueRecompute? state with
    | none => pure 0
    | some id =>
        let node <- State.getNode state id
        let info <- node.infoRef.get
        let missingValue <- do pure (!(<- node.hasValue))
        if info.necessary && (info.stale || missingValue) then
          State.stabilizeOne state stabilization id
        let rest <- State.drainRecomputeHeapWithBudget state stabilization (budget - 1)
        pure (rest + 1)

end Internal
end Leancremental
