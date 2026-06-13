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

def insertNatSortedUnique (xs : Array Nat) (x : Nat) : Array Nat := Id.run do
  let mut inserted := false
  let mut result := #[]
  for y in xs do
    if inserted then
      result := result.push y
    else if x == y then
      inserted := true
      result := result.push y
    else if x < y then
      inserted := true
      result := result.push x
      result := result.push y
    else
      result := result.push y
  if !inserted then
    result := result.push x
  pure result

def sortedIdsFromNatSet (ids : Std.HashMap Nat Unit) : Array Nat :=
  (ids.toArray.map Prod.fst).qsort (· < ·)

def joinWith (separator : String) (parts : List String) : String :=
  match parts with
  | [] => ""
  | first :: rest => rest.foldl (fun acc part => acc ++ separator ++ part) first

partial def ensureBucketCapacity
    (buckets : Array (Array Nat))
    (targetSize : Nat) : Array (Array Nat) :=
  if buckets.size < targetSize then
    ensureBucketCapacity (buckets.push #[]) targetSize
  else
    buckets

def flattenBuckets (buckets : Array (Array Nat)) : Array Nat := Id.run do
  let mut entries := #[]
  for bucket in buckets do
    for id in bucket do
      entries := entries.push id
  pure entries

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

def State.nodeGeneration (state : State) (id : Nat) : IO Nat := do
  let generations <- state.nodeGenerations.get
  match generations[id]? with
  | some generation => pure generation
  | none => throwUser s!"unknown incremental node {id}"

def State.bumpNodeGeneration (state : State) (id : Nat) : IO Nat := do
  let generation <- State.nodeGeneration state id
  let nextGeneration := generation + 1
  state.nodeGenerations.modify (fun generations => generations.set! id nextGeneration)
  pure nextGeneration

def State.getInfo (state : State) (id : Nat) : IO NodeInfo := do
  let node <- State.getNode state id
  node.infoRef.get

def State.setInfo (state : State) (id : Nat) (info : NodeInfo) : IO Unit := do
  let node <- State.getNode state id
  node.infoRef.set info

def State.modifyInfo (state : State) (id : Nat) (f : NodeInfo -> NodeInfo) : IO Unit := do
  let info <- State.getInfo state id
  State.setInfo state id (f info)

def State.currentTraceStabilization (state : State) : IO (Option Nat) := do
  if <- state.stabilizing.get then
    state.partialStabilization.get
  else
    pure none

def orderedTraceEventsFrom
    (events : Array StateTraceEvent)
    (start : Nat) : Array StateTraceEvent :=
  if events.isEmpty then
    #[]
  else
    let start := start % events.size
    if start == 0 then
      events
    else
      events.extract start events.size ++ events.extract 0 start

def State.orderedTraceEvents (state : State) : IO (Array StateTraceEvent) := do
  let events <- state.traceEventsRef.get
  let start <- state.traceEventsStartRef.get
  pure (orderedTraceEventsFrom events start)

def State.appendTraceRecord (state : State) (event : StateTraceEvent) : IO Unit := do
  let mode <- state.traceModeRef.get
  match mode with
  | .off =>
      pure ()
  | .unbounded =>
      let start <- state.traceEventsStartRef.get
      if start == 0 then
        state.traceEventsRef.modify (fun events => events.push event)
      else
        let ordered <- State.orderedTraceEvents state
        state.traceEventsRef.set (ordered.push event)
        state.traceEventsStartRef.set 0
  | .bounded maxEvents =>
      if maxEvents == 0 then
        state.traceEventsRef.set #[]
        state.traceEventsStartRef.set 0
      else
        let mut events <- state.traceEventsRef.get
        let mut start <- state.traceEventsStartRef.get
        if events.isEmpty then
          start := 0
        if start != 0 && events.size != maxEvents then
          events := orderedTraceEventsFrom events start
          start := 0
        if events.size > maxEvents then
          let ordered := orderedTraceEventsFrom events start
          events := ordered.extract (ordered.size - maxEvents) ordered.size
          start := 0
        if events.size < maxEvents then
          state.traceEventsRef.set (events.push event)
          state.traceEventsStartRef.set start
        else
          let writeIndex := start % maxEvents
          state.traceEventsRef.set (events.set! writeIndex event)
          state.traceEventsStartRef.set ((writeIndex + 1) % maxEvents)

def State.recordHandlerFailure
    (state : State)
    (nodeId : Nat)
    (handlerKind : String)
    (error : IO.Error) : IO Unit := do
  let stabilization <- State.currentTraceStabilization state
  State.appendTraceRecord state {
    nodeId := nodeId,
    stabilization := stabilization,
    kind := .handlerFailed handlerKind (toString error)
  }
  let mode <- state.handlerFailureModeRef.get
  match mode with
  | .traceOnly => pure ()
  | .failFast => throw error

def State.runDependencyChangeHandlers
    (state : State)
    (id : Nat)
    (oldChildren : Array Nat)
    (newChildren : Array Nat) : IO Unit := do
  let handlers <- state.dependencyChangeHandlers.get
  for handler in handlers do
    try
      handler id oldChildren newChildren
    catch error =>
      State.recordHandlerFailure state id "dependency-change" error

def State.runObservabilityHandlers (state : State) (id : Nat) (isNowNecessary : Bool) : IO Unit := do
  let node <- State.getNode state id
  let handlers <- node.observabilityHandlers.get
  for handler in handlers do
    try
      handler isNowNecessary
    catch error =>
      State.recordHandlerFailure state id "observability" error

def State.appendTraceEvent
    (state : State)
    (nodeId : Nat)
    (stabilization : Option Nat)
    (kind : StateTraceEventKind) : IO Unit := do
  State.appendTraceRecord state {
    nodeId := nodeId,
    stabilization := stabilization,
    kind := kind
  }

def State.recomputeHeapEntries (state : State) : IO (Array Nat) := do
  let buckets <- state.recomputeHeap.buckets.get
  pure (flattenBuckets buckets)

def State.enqueueRecompute (state : State) (id : Nat) : IO Unit := do
  let members <- state.recomputeHeap.members.get
  if members.contains id then
    pure ()
  else do
    let info <- State.getInfo state id
    let height := info.height
    state.recomputeHeap.buckets.modify (fun buckets =>
      (ensureBucketCapacity buckets (height + 1)).modify height (fun b => b.push id))
    state.recomputeHeap.members.set (members.insert id ())
    let size <- state.recomputeHeap.sizeRef.get
    state.recomputeHeap.sizeRef.set (size + 1)
    let nextHeight <- state.recomputeHeap.nextHeight.get
    if size == 0 || height < nextHeight then
      state.recomputeHeap.nextHeight.set height

def State.clearRecomputeHeap (state : State) : IO Unit := do
  state.recomputeHeap.buckets.set #[]
  state.recomputeHeap.members.set (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
  state.recomputeHeap.nextHeight.set 0
  state.recomputeHeap.sizeRef.set 0

def State.recordPendingDirty (state : State) (id : Nat) : IO Unit :=
  state.pendingDirtyRef.modify (fun pending => pending.insert id ())

def State.addStaleNecessaryId (state : State) (id : Nat) : IO Unit :=
  state.staleNecessaryIdsRef.modify (fun ids => ids.insert id ())

def State.removeStaleNecessaryId (state : State) (id : Nat) : IO Unit :=
  state.staleNecessaryIdsRef.modify (fun ids => ids.erase id)

def State.addNodeTagIndex (state : State) (id : Nat) (tag : String) : IO Unit :=
  state.tagIndexRef.modify (fun index =>
    let ids := insertNatSortedUnique (index.getD tag #[]) id
    index.insert tag ids)

def State.removeNodeTagIndex (state : State) (id : Nat) (tag : String) : IO Unit :=
  state.tagIndexRef.modify (fun index =>
    let ids := eraseNat (index.getD tag #[]) id
    if ids.isEmpty then
      index.erase tag
    else
      index.insert tag ids)

def State.rebuildTagIndex (state : State) : IO Unit := do
  let nodes <- state.nodes.get
  let mut index : Std.HashMap String (Array Nat) := Std.HashMap.emptyWithCapacity
  for nodeId in [:nodes.size] do
    let info <- State.getInfo state nodeId
    for tag in info.tags do
      let ids := insertNatSortedUnique (index.getD tag #[]) nodeId
      index := index.insert tag ids
  state.tagIndexRef.set index

def State.restoreRecomputeHeapToPendingDirty (state : State) : IO Unit := do
  let entries <- State.recomputeHeapEntries state
  for id in entries do
    State.recordPendingDirty state id

def State.scheduleIfNecessary (state : State) (id : Nat) : IO Unit := do
  let node <- State.getNode state id
  let info <- node.infoRef.get
  let missingValue <- do pure (!(<- node.hasValue))
  if info.necessary && (info.stale || missingValue) then
    if <- state.stabilizing.get then
      State.enqueueRecompute state id
    else
      State.recordPendingDirty state id

def State.drainPendingDirty (state : State) : IO Unit := do
  let pending <- state.pendingDirtyRef.get
  state.pendingDirtyRef.set (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
  for (id, _) in pending do
    State.scheduleIfNecessary state id

def State.heightOf (state : State) (id : Nat) : IO Nat := do
  let info <- State.getInfo state id
  pure info.height

def State.refreshHeightFromChildren (state : State) (id : Nat) : IO Nat := do
  let info <- State.getInfo state id
  let mut height := 0
  for child in info.children do
    let childHeight <- State.heightOf state child
    height := max height (childHeight + 1)
  if height == info.height then
    pure height
  else
    State.setInfo state id { info with height := height }
    pure height

partial def State.dequeueRecomputeFrom? (state : State) (height : Nat) : IO (Option Nat) := do
  let buckets <- state.recomputeHeap.buckets.get
  if height >= buckets.size then
    pure none
  else
    let bucket := buckets[height]!
    if bucket.isEmpty then
      state.recomputeHeap.nextHeight.set (height + 1)
      State.dequeueRecomputeFrom? state (height + 1)
    else
      let id := bucket[bucket.size - 1]!
      -- bucket and buckets are dead after here; modify gets exclusive access for O(1) pop
      state.recomputeHeap.buckets.modify (fun bs => bs.modify height Array.pop)
      let members <- state.recomputeHeap.members.get
      state.recomputeHeap.members.set (members.erase id)
      state.recomputeHeap.sizeRef.modify (fun size => size - 1)
      state.recomputeHeap.nextHeight.set height
      let currentHeight <- State.refreshHeightFromChildren state id
      if currentHeight != height then
        State.enqueueRecompute state id
        State.dequeueRecomputeFrom? state (min height currentHeight)
      else
        pure (some id)

def State.dequeueRecompute? (state : State) : IO (Option Nat) := do
  let size <- state.recomputeHeap.sizeRef.get
  if size == 0 then
    pure none
  else
    State.dequeueRecomputeFrom? state (← state.recomputeHeap.nextHeight.get)

def State.nodeChangedAt (state : State) (id stabilization : Nat) : IO Bool := do
  let info <- State.getInfo state id
  pure (info.changedAt == some stabilization)

def State.heightFromChildren (state : State) (children : Array Nat) : IO Nat := do
  let mut height := 0
  for child in children do
    let childHeight <- State.heightOf state child
    height := max height (childHeight + 1)
  pure height

def State.getNecessaryRefCount (state : State) (id : Nat) : IO Nat := do
  let counts <- state.necessaryRefCounts.get
  pure (counts[id]!)

def State.setNecessaryRefCount (state : State) (id count : Nat) : IO Unit := do
  state.necessaryRefCounts.modify (fun counts => counts.set! id count)

partial def State.retainNecessary (state : State) (id : Nat) : IO Unit := do
  let count <- State.getNecessaryRefCount state id
  State.setNecessaryRefCount state id (count + 1)
  if count == 0 then
    let info <- State.getInfo state id
    State.setInfo state id { info with necessary := true }
    if info.stale then
      State.addStaleNecessaryId state id
    State.runObservabilityHandlers state id true
    State.scheduleIfNecessary state id
    for child in info.children do
      State.retainNecessary state child

partial def State.releaseNecessary (state : State) (id : Nat) : IO Unit := do
  let count <- State.getNecessaryRefCount state id
  if count == 0 then
    pure ()
  else
    let nextCount := count - 1
    State.setNecessaryRefCount state id nextCount
    if nextCount == 0 then
      let info <- State.getInfo state id
      State.setInfo state id { info with necessary := false }
      State.removeStaleNecessaryId state id
      State.runObservabilityHandlers state id false
      for child in info.children do
        State.releaseNecessary state child

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
  let nodes <- state.nodes.get
  let mut necessary := #[]
  for index in [:nodes.size] do
    let info <- State.getInfo state index
    if info.necessary then
      necessary := necessary.push index
  pure necessary

partial def State.markParentsStale (state : State) (id : Nat) : IO Unit := do
  let info <- State.getInfo state id
  for parent in info.parents do
    let parentInfo <- State.getInfo state parent
    if !parentInfo.stale then
      State.setInfo state parent { parentInfo with stale := true }
      if parentInfo.necessary then
        State.addStaleNecessaryId state parent
    if parentInfo.necessary then
      State.scheduleIfNecessary state parent

def State.markNodeStaleWith
    (state : State)
    (id : Nat)
    (reason : Option String := none)
    (stabilization : Option Nat := none) : IO Unit := do
  let info <- State.getInfo state id
  State.setInfo state id { info with stale := true }
  if info.necessary then
    State.addStaleNecessaryId state id
  State.scheduleIfNecessary state id
  let traceStabilization <-
    match stabilization with
    | some n => pure (some n)
    | none => State.currentTraceStabilization state
  State.appendTraceEvent state id traceStabilization (.markedStale (reason.orElse (fun _ => info.externalDirtyReason)))

def State.markNodeStale (state : State) (id : Nat) : IO Unit :=
  State.markNodeStaleWith state id

def State.invalidateNodeWith
    (state : State)
    (id : Nat)
    (reason : Option String := none)
    (stabilization : Option Nat := none) : IO Unit := do
  State.modifyInfo state id (fun info => { info with valid := false, stale := true, computedAt := none })
  State.markNodeStaleWith state id reason stabilization
  let traceStabilization <-
    match stabilization with
    | some n => pure (some n)
    | none => State.currentTraceStabilization state
  State.appendTraceEvent state id traceStabilization .invalidated

def State.addParent (state : State) (child parent : Nat) : IO Unit := do
  State.modifyInfo state child (fun info => { info with parents := pushIfMissing info.parents parent })

def State.removeParent (state : State) (child parent : Nat) : IO Unit := do
  State.modifyInfo state child (fun info => { info with parents := eraseNat info.parents parent })

partial def State.setChildren (state : State) (parent : Nat) (children : Array Nat) : IO Unit := do
  let children := dedupNat children
  let info <- State.getInfo state parent
  let oldChildren := info.children
  let removedChildren := oldChildren.filter (fun oldChild => !containsNat children oldChild)
  let addedChildren := children.filter (fun child => !containsNat oldChildren child)
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
    State.addStaleNecessaryId state parent
  if oldChildren != children then
    State.appendTraceEvent state parent (← State.currentTraceStabilization state) (.dependencyRewrite oldChildren children)
  if oldChildren != children then
    State.runDependencyChangeHandlers state parent oldChildren children
  if info.necessary then
    for child in removedChildren do
      State.releaseNecessary state child
    for child in addedChildren do
      State.retainNecessary state child
    State.scheduleIfNecessary state parent

def State.registerNode
    (state : State)
    (kind : NodeKind)
    (children : Array Nat)
    (recompute : Nat -> IO Bool)
    (hasValue : IO Bool)
  (clearValue : IO Bool)
  (canRecomputeAfterClear : Bool)
    (initiallyStale : Bool) : IO Nat := do
  let children := dedupNat children
  let nodes <- state.nodes.get
  let recycledNodeIds <- state.recycledNodeIdsRef.get
  let id <-
    if recycledNodeIds.isEmpty then
      let id := nodes.size
      state.nodeGenerations.modify (fun generations => generations.push 0)
      state.necessaryRefCounts.modify (fun counts => counts.push 0)
      pure id
    else
      let lastIndex := recycledNodeIds.size - 1
      let id := recycledNodeIds[lastIndex]!
      state.recycledNodeIdsRef.set (recycledNodeIds.extract 0 lastIndex)
      state.necessaryRefCounts.modify (fun counts => counts.set! id 0)
      pure id
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
    visitingAt := none,
    lastAccessedAt := none,
    externalDirtyReason := none,
    tags := #[]
  }
  let observabilityHandlers <- IO.mkRef #[]
  let packed : PackedNode := {
    infoRef := infoRef,
    observabilityHandlers := observabilityHandlers,
    hasValue := hasValue,
    clearValue := clearValue,
    canRecomputeAfterClear := canRecomputeAfterClear,
    recompute := recompute
  }
  if id == nodes.size then
    state.nodes.set (nodes.push packed)
  else
    state.nodes.set (nodes.set! id packed)
  for child in children do
    State.addParent state child id
  pure id

def State.nodeKindReclaimable (kind : NodeKind) : Bool :=
  match kind with
  | .var => false
  | .expert => false
  | _ => true

def State.mkRecycledSlotNode (id : Nat) : IO PackedNode := do
  let infoRef <- IO.mkRef {
    id := id,
    kind := NodeKind.const,
    height := 0,
    children := #[],
    parents := #[],
    necessary := false,
    stale := false,
    valid := false,
    computedAt := none,
    changedAt := none,
    visitingAt := none,
    lastAccessedAt := none,
    externalDirtyReason := none,
    tags := #[]
  }
  let observabilityHandlers <- IO.mkRef #[]
  pure {
    infoRef := infoRef,
    observabilityHandlers := observabilityHandlers,
    hasValue := pure false,
    clearValue := pure false,
    canRecomputeAfterClear := false,
    recompute := fun _ =>
      throwUser s!"reclaimed node slot {id} was recomputed before reallocation"
  }

partial def State.reclaimOrphanedNode
    (state : State)
    (visitedRef : IO.Ref (Std.HashMap Nat Unit))
    (recycledSetRef : IO.Ref (Std.HashMap Nat Unit))
    (id : Nat) : IO Nat := do
  let visited <- visitedRef.get
  if visited.contains id then
    pure 0
  else
    visitedRef.set (visited.insert id ())
    let recycledSet <- recycledSetRef.get
    if recycledSet.contains id then
      pure 0
    else
      let info <- State.getInfo state id
      let pinnedIds <- state.pinnedIdsRef.get
      if info.necessary || !info.parents.isEmpty || !State.nodeKindReclaimable info.kind || pinnedIds.contains id then
        pure 0
      else
        let node <- State.getNode state id
        let _ <- node.clearValue
        let children := info.children
        for child in children do
          State.removeParent state child id
        for tag in info.tags do
          State.removeNodeTagIndex state id tag
        State.removeStaleNecessaryId state id
        state.pendingDirtyRef.modify (fun pending => pending.erase id)
        state.recomputeHeap.members.modify (fun members => members.erase id)
        let recycled <- State.mkRecycledSlotNode id
        state.nodes.modify (fun nodes => nodes.set! id recycled)
        state.necessaryRefCounts.modify (fun counts => counts.set! id 0)
        let _ <- State.bumpNodeGeneration state id
        state.recycledNodeIdsRef.modify (fun ids => ids.push id)
        recycledSetRef.modify (fun s => s.insert id ())
        let mut reclaimed := 1
        for child in children do
          reclaimed := reclaimed + (← State.reclaimOrphanedNode state visitedRef recycledSetRef child)
        pure reclaimed

def readValue (node : Incr α) : IO α := do
  match <- node.valueRef.get with
  | some value => pure value
  | none => throwUser s!"incremental node {node.id} has no stable value"

def writeValue (valueRef : IO.Ref (Option α)) (cutoffRef : IO.Ref (Cutoff α))
               (digestRef : IO.Ref (Option UInt64)) (newValue : α) : IO Bool := do
  let cutoff <- cutoffRef.get
  match cutoff.hashValue with
  | some hashFn =>
      -- Cached-digest fast path: one hash of newValue; compare with stored digest.
      let newHash := hashFn newValue
      match <- digestRef.get with
      | none =>
          valueRef.set (some newValue)
          digestRef.set (some newHash)
          pure true
      | some storedHash =>
          if storedHash != newHash then
            -- Digests differ → definitely changed.
            valueRef.set (some newValue)
            digestRef.set (some newHash)
            pure true
          else
            -- Digests match: use shouldCutoff as collision guard.
            match <- valueRef.get with
            | none =>
                valueRef.set (some newValue)
                digestRef.set (some newHash)
                pure true
            | some oldValue =>
                if cutoff.shouldCutoff oldValue newValue then
                  pure false
                else
                  valueRef.set (some newValue)
                  digestRef.set (some newHash)
                  pure true
  | none =>
      -- Standard path.
      match <- valueRef.get with
      | none =>
          valueRef.set (some newValue)
          pure true
      | some oldValue =>
          if cutoff.shouldCutoff oldValue newValue then
            pure false
          else
            valueRef.set (some newValue)
            pure true

partial def State.stabilizeOne (state : State) (stabilization id : Nat) : IO Unit := do
  state.nodesVisitedRef.modify (· + 1)
  let node <- State.getNode state id
  let info <- node.infoRef.get
  let missingValue <- do pure (!(<- node.hasValue))
  if info.computedAt == some stabilization && !info.stale && !missingValue then
    pure ()
  else if info.visitingAt == some stabilization then
    let stack <- state.visitStack.get
    throwUser (formatCycle (closeCyclePath id stack))
  else
    let previousStack <- state.visitStack.get
    state.visitStack.set (previousStack.push id)
    node.infoRef.set { info with visitingAt := some stabilization }
    try
      let changed <-
        if info.stale || missingValue then
          if <- state.timingModeRef.get then
            let t0 <- IO.monoNanosNow
            let r <- node.recompute stabilization
            let t1 <- IO.monoNanosNow
            state.lastPassTimingsRef.modify (fun arr => arr.push (id, t1 - t0))
            pure r
          else
            node.recompute stabilization
        else
          pure false
      let infoAfterRecompute <- node.infoRef.get
      let missingValueAfterRecompute <- do pure (!(<- node.hasValue))
      node.infoRef.set {
        infoAfterRecompute with
        stale := false,
        computedAt := if missingValueAfterRecompute then infoAfterRecompute.computedAt else some stabilization,
        changedAt := if changed then some stabilization else infoAfterRecompute.changedAt,
        visitingAt := none
      }
      State.removeStaleNecessaryId state id
      State.appendTraceEvent state id (some stabilization) (.recomputed changed)
      state.visitStack.set previousStack
      if changed then
        state.changedNodeIdsRef.modify (fun ids => ids.push id)
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

def State.applyDeferredMutations (state : State) (currentEpoch : Nat) : IO Unit := do
  let ops <- state.deferredMutationsRef.get
  state.deferredMutationsRef.set #[]
  for op in ops do
    let (nodeId, storedEpoch) := match op with
      | .markStale id _ epoch => (id, epoch)
      | .invalidate id _ epoch => (id, epoch)
    -- Validate epoch: drop entries whose stored epoch no longer matches the
    -- epoch being applied (defense-in-depth; cancel should have cleared the queue).
    match storedEpoch with
    | some epoch =>
        if epoch != currentEpoch then
          State.appendTraceEvent state nodeId storedEpoch .deferredDropped
        else
          match op with
          | .markStale id reason stabilization =>
              State.markNodeStaleWith state id reason stabilization
              State.markParentsStale state id
          | .invalidate id reason stabilization =>
              State.invalidateNodeWith state id reason stabilization
              State.markParentsStale state id
    | none =>
        -- No epoch stored; apply unconditionally (not queued during stabilization).
        match op with
        | .markStale id reason stabilization =>
            State.markNodeStaleWith state id reason stabilization
            State.markParentsStale state id
        | .invalidate id reason stabilization =>
            State.invalidateNodeWith state id reason stabilization
            State.markParentsStale state id

end Internal
end Leancremental
