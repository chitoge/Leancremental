import Leancremental
import Tests.Util

/-! Query/LSP-oriented regression tests. -/

namespace Leancremental
namespace Tests
namespace Query

def natStringCodec : MemoValueCodec Nat String := {
  encode := fun value => .ok (toString value),
  decode := fun serialized =>
    match serialized.toNat? with
    | some value => .ok value
    | none => .error "expected Nat string"
}

def validatedSnapshotMetadata (schema build inputDigest : String) (timestamp : Nat) : MemoSnapshotEnvelopeMetadata := {
  schema := schema
  build := build
  inputDigest := inputDigest
  timestamp := timestamp
}

def validatedSnapshotPolicy : MemoSnapshotValidationPolicy := {
  expectedSchema := some "memo:v1"
  expectedBuild := some "build-42"
  expectedInputDigest := some "digest-alpha"
  minTimestamp := some 100
}

def arrayMemoStore (entriesRef : IO.Ref (Array (String × Incr Nat))) : MemoStore String Nat := {
  lookup := fun key => do
    pure ((← entriesRef.get).find? (fun entry => entry.1 == key) |>.map Prod.snd),
  insert := fun key node => do
    entriesRef.modify (fun entries =>
      if entries.any (fun entry => entry.1 == key) then
        entries.map (fun entry => if entry.1 == key then (key, node) else entry)
      else
        entries.push (key, node)),
  erase := fun key => do
    let entries <- entriesRef.get
    let nextEntries := entries.filter (fun entry => entry.1 != key)
    entriesRef.set nextEntries
    pure (nextEntries.size != entries.size),
  retain := fun predicate => do
    let entries <- entriesRef.get
    let nextEntries := entries.filter (fun entry => predicate entry.1 entry.2)
    entriesRef.set nextEntries
    pure (entries.size - nextEntries.size),
  clear := do
    let entries <- entriesRef.get
    entriesRef.set #[]
    pure entries.size,
  size := do
    pure (← entriesRef.get).size,
  entries :=
    entriesRef.get
}

def assertContains (label : String) (haystack needle : String) : IO Unit := do
  if (haystack.splitOn needle).length > 1 then
    pure ()
  else
    throw (IO.userError s!"{label}: expected {repr haystack} to contain {repr needle}")

def expectMemoMetadata
    (label : String)
    (metadata? : Option MemoEntryMetadata) : IO MemoEntryMetadata := do
  match metadata? with
  | some metadata => pure metadata
  | none => throw (IO.userError s!"{label}: expected memo metadata")

inductive ToyQueryKey where
  | file
  | package
  | workspace
deriving Repr, BEq, Hashable

def describeToyQueryKey : ToyQueryKey -> String
  | .file => "file"
  | .package => "package"
  | .workspace => "workspace"

inductive FakeExternalActionState where
  | pending (digest : String)
  | done (digest : String) (value : String)
deriving Repr, BEq

def externalActionTag : String := "external-action"

def fakeDigest (input : String) : String :=
  s!"digest:{input}"

def buildFakeExternalAction
    (input : Var String)
    (completions : Var (Array (String × String))) : IO (Incr FakeExternalActionState) := do
  let digest <- map (Var.watch input) fakeDigest Cutoff.ofEq
  let status <- map2 digest (Var.watch completions) (fun currentDigest ready =>
    match ready.find? (fun entry => entry.1 == currentDigest) with
    | some entry => .done currentDigest entry.2
    | none => .pending currentDigest)
  Incr.addTag status externalActionTag
  pure status

def stabilizeWithBudgetUntilDone
    (state : State)
  (budget : Nat) : IO (Array State.StabilizeBudgetResult) := do
  let mut slices := #[]
  let mut completed := false
  while !completed do
    let slice <- State.stabilizeWithBudget state budget
    slices := slices.push slice
    completed := slice.completed
  pure slices

def toyQueryRules (source : Var String) : QueryRules ToyQueryKey String where
  describeKey := describeToyQueryKey
  build := fun
    | .file => QueryM.ofIncr (Var.watch source)
    | .package => do
        let file <- QueryM.require .file
        pure s!"package({file})"
    | .workspace => do
        let pkg <- QueryM.require .package
        pure s!"workspace({pkg})"

def testQueryMStack : IO Unit := do
  let state <- State.create
  let source <- Var.create state "alpha"
  let table <- QueryTable.create state (toyQueryRules source)
  let workspace <- QueryTable.request table .workspace
  let observer <- observe workspace
  State.stabilize state
  assertEq "query stack initial workspace value" (← Observer.value! observer) "workspace(package(alpha))"

def testQueryMEditRecomputes : IO Unit := do
  let state <- State.create
  let source <- Var.create state "alpha"
  let table <- QueryTable.create state (toyQueryRules source)
  let workspace <- QueryTable.request table .workspace
  let observer <- observe workspace
  State.stabilize state
  Var.set source "beta"
  State.stabilize state
  assertEq "query stack updates after edit" (← Observer.value! observer) "workspace(package(beta))"

def testQueryMMemoReuse : IO Unit := do
  let state <- State.create
  let source <- Var.create state "alpha"
  let table <- QueryTable.create state (toyQueryRules source)
  let first <- QueryTable.request table .package
  let second <- QueryTable.request table .package
  let fileFirst <- QueryTable.request table .file
  let fileSecond <- QueryTable.request table .file
  assertEq "query request memo reuse on package" first.id second.id
  assertEq "query request memo reuse on file" fileFirst.id fileSecond.id

def measureQueryBindChurnNodeCount (rounds : Nat) (reclaimEachRound : Bool) : IO Nat := do
  let state <- State.create
  let source <- Var.create state 0
  let rules : QueryRules String Nat := {
    describeKey := fun key => key
    build := fun _ => do
      let value <- QueryM.ofIncr (Var.watch source)
      QueryM.ofIO (ret state (value % 2))
  }
  let table <- QueryTable.create state rules
  let root <- QueryTable.request table "root"
  let observer <- observe root
  State.stabilize state
  for step in [:rounds] do
    Var.set source (step + 1)
    State.stabilize state
    if reclaimEachRound then
      let _ <- State.reclaimUnreachableNodes state
      pure ()
    else
      pure ()
  assertEq "query bind churn final observed value" (← Observer.value! observer) (rounds % 2)
  State.numNodes state

def testReclaimUnreachableNodesMitigatesQueryBindChurn : IO Unit := do
  let rounds := 120
  let leakedNodeCount <- measureQueryBindChurnNodeCount rounds false
  let reclaimedNodeCount <- measureQueryBindChurnNodeCount rounds true
  assertEq "query bind churn without reclamation keeps growing nodes" (decide (leakedNodeCount >= rounds + 3)) true
  assertEq "query bind churn with reclamation stays near constant size" (decide (reclaimedNodeCount <= 10)) true
  assertEq "query bind churn reclamation materially reduces growth" (decide (reclaimedNodeCount + (rounds / 2) <= leakedNodeCount)) true

def testQueryTableInvalidatePreservesIdentity : IO Unit := do
  let state <- State.create
  let source <- Var.create state "alpha"
  let table <- QueryTable.create state (toyQueryRules source)
  let fileBefore <- QueryTable.request table .file
  let packageBefore <- QueryTable.request table .package
  let workspace <- QueryTable.request table .workspace
  let packageHit <- QueryTable.request table .package
  assertEq "query request keeps stable package identity" packageBefore.id packageHit.id

  let observer <- observe workspace
  State.stabilize state
  assertEq "query invalidate setup workspace value"
    (← Observer.value! observer) "workspace(package(alpha))"

  assertEq "query invalidate returns true for existing key"
    (← QueryTable.invalidate table .package) true
  assertEq "query invalidate clears cached package value"
    (← Incr.value? packageBefore) none
  let packageAfter <- QueryTable.request table .package
  assertEq "query invalidate preserves package identity"
    packageAfter.id packageBefore.id

  assertEq "query invalidateMatching returns one match"
    (← QueryTable.invalidateMatching table (fun key => key == .file)) 1
  assertEq "query invalidateMatching clears cached file value"
    (← Incr.value? fileBefore) none
  let fileAfter <- QueryTable.request table .file
  assertEq "query invalidateMatching preserves file identity"
    fileAfter.id fileBefore.id

  Var.set source "beta"
  State.stabilize state
  assertEq "query invalidated nodes recompute after dependency edit"
    (← Observer.value! observer) "workspace(package(beta))"

inductive CyclicQueryKey where
  | left
  | right
deriving Repr, BEq, Hashable

def describeCyclicQueryKey : CyclicQueryKey -> String
  | .left => "left"
  | .right => "right"

def cyclicQueryRules : QueryRules CyclicQueryKey String where
  describeKey := describeCyclicQueryKey
  build := fun
    | .left => do
        let right <- QueryM.require .right
        pure s!"left({right})"
    | .right => do
        let left <- QueryM.require .left
        pure s!"right({left})"

def testQueryMCycleDetection : IO Unit := do
  let state <- State.create
  let table <- QueryTable.create state cyclicQueryRules
  let message <-
    try
      let _ <- QueryTable.request table .left
      throw (IO.userError "cycle detection did not raise an error")
    catch error =>
      pure error.toString
  assertContains "query cycle error prefix" message "query cycle detected"
  assertContains "query cycle path" message "left -> right -> left"

def testExternalActionReferenceLoop : IO Unit := do
  let state <- State.create
  let input <- Var.create state "module Main"
  let completions <- Var.create state (#[] : Array (String × String))
  let action <- buildFakeExternalAction input completions
  let observer <- observe action
  let expectedDigest := fakeDigest "module Main"

  let initialSlice <- State.stabilizeWithBudget state 0
  assertEq "external action loop starts with an incomplete budget slice" initialSlice.completed false
  assertEq "external action loop keeps observer empty until a completed stabilization" (← Observer.value? observer) none

  let pendingSlices <- stabilizeWithBudgetUntilDone state 1
  assertEq "external action loop resumes to a completed pending state" (pendingSlices.back?.map (fun slice => slice.completed)) (some true)
  assertEq "external action loop exposes pending digest first" (← Observer.value! observer) (.pending expectedDigest)
  assertEq "external action loop drains stale work after pending stabilize" (← State.staleNecessaryIds state) #[]

  let taggedWhilePending <- State.nodesWithTag state externalActionTag
  assertEq "external action loop tag discovery sees the action id while pending"
    (taggedWhilePending.any (fun id => id == action.id)) true

  let completionValue <-
    match ← Observer.value! observer with
    | .pending digest =>
        let discovered <- State.nodesWithTag state externalActionTag
        assertEq "external action loop rediscovery remains stable before completion"
          (discovered.any (fun id => id == action.id)) true
        let value := s!"done:{digest}"
        Var.set completions #[(digest, value)]
        pure value
    | .done _ _ =>
        throw (IO.userError "external action loop expected a pending value before injecting completion")

  assertEq "external action loop completion injection marks necessary stale work"
    (← State.staleNecessaryIds state) #[completions.watch.id]

  let injectedSlice <- State.stabilizeWithBudget state 0
  assertEq "external action loop can interleave completion with another incomplete slice" injectedSlice.completed false

  let doneSlices <- stabilizeWithBudgetUntilDone state 1
  assertEq "external action loop resumes to a completed done state" (doneSlices.back?.map (fun slice => slice.completed)) (some true)
  assertEq "external action loop converges to the injected completion"
    (← Observer.value! observer) (.done expectedDigest completionValue)
  assertEq "external action loop drains stale work after completion" (← State.staleNecessaryIds state) #[]

def testQueryPrimitives : IO Unit := do
  let state <- State.create
  let input <- Var.create state 1
  let computeCount <- IO.mkRef 0
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let first <- MemoTable.getOrCreate table "parse:file.lean" (fun _ => do
    computeCount.modify (fun count => count + 1)
    map (Var.watch input) (fun value => value + 1))
  let second <- MemoTable.getOrCreate table "parse:file.lean" (fun _ => do
    computeCount.modify (fun count => count + 1)
    const state 999)
  assertEq "memo hit returns same node" first.id second.id
  assertEq "memo compute runs once" (← computeCount.get) 1
  assertEq "memo table size after hit" (← MemoTable.size table) 1
  let observer <- observe first
  let initialStats <- State.stabilizeWithStats state
  assertEq "memo value" (← Observer.value! observer) 2
  assertEq "stats stabilization number" initialStats.stabilization 1
  assertEq "stats active observers" initialStats.activeObservers 1
  assertEq "stats heap drained" initialStats.remainingRecomputeEntries 0
  Var.set input 10
  assertEq "stale cached value before restabilize" (← Incr.staleValue? first) (some 2)
  assertEq "input is stale before restabilize" (← Incr.isStale (Var.watch input)) true
  let updateStats <- State.stabilizeWithStats state
  assertEq "updated memo value" (← Observer.value! observer) 11
  assertEq "stats changed nodes" updateStats.nodesChanged 2
  let other <- MemoTable.getOrCreate table "parse:other.lean" (fun _ => const state 7)
  assertEq "memo miss allocates distinct node" (first.id == other.id) false
  assertEq "memo table size after miss" (← MemoTable.size table) 2

def testMemoLifecycle : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let computeCount <- IO.mkRef 0
  let first <- MemoTable.getOrCreate table "file:a" (fun _ => do
    computeCount.modify (fun count => count + 1)
    const state 1)
  assertEq "memo lifecycle initial size" (← MemoTable.size table) 1
  assertEq "memo invalidates missing key" (← MemoTable.invalidate table "missing") false
  assertEq "memo invalidates existing key" (← MemoTable.invalidate table "file:a") true
  let second <- MemoTable.getOrCreate table "file:a" (fun _ => do
    computeCount.modify (fun count => count + 1)
    const state 2)
  assertEq "memo invalidation allocates fresh node" (first.id == second.id) false
  assertEq "memo invalidation recomputes" (← computeCount.get) 2
  let _b <- MemoTable.getOrCreate table "file:b" (fun _ => const state 3)
  let _c <- MemoTable.getOrCreate table "file:c" (fun _ => const state 4)
  let removedMatching <- MemoTable.invalidateMatching table (fun key => key == "file:b")
  assertEq "memo predicate invalidation count" removedMatching 1
  assertEq "memo predicate invalidation size" (← MemoTable.size table) 2
  let scope <- MemoScope.create table
  let _hover <- MemoScope.getOrCreate scope "request:hover" (fun _ => const state 10)
  let _diagnostics <- MemoScope.getOrCreate scope "request:diagnostics" (fun _ => const state 20)
  let _hoverAgain <- MemoScope.getOrCreate scope "request:hover" (fun _ => const state 999)
  assertEq "memo scope records unique keys" (← MemoScope.ownedKeys scope).size 2
  assertEq "memo scope grows table" (← MemoTable.size table) 4
  assertEq "memo scope clear count" (← MemoScope.clear scope) 2
  assertEq "memo scope clear resets owned keys" (← MemoScope.ownedKeys scope).size 0
  assertEq "memo scope leaves unrelated keys" (← MemoTable.size table) 2
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let z <- map y (fun value => value * 2)
  let _observer <- observe z
  let partialSlice <- State.stabilizeWithBudget state 1
  assertEq "memo mutation guard starts partial" partialSlice.completed false
  let blocked <-
    try
      let _removed <- MemoTable.clear table
      pure false
    catch _ =>
      pure true
  assertEq "memo mutation blocked during partial stabilization" blocked true
  State.cancelStabilization state

def testMemoMetadataAccessAccounting : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let node <- MemoTable.getOrCreate table "meta:file" (fun _ => const state 5)
  let createdMetadata <- expectMemoMetadata "metadata after create" (← MemoTable.lookupMetadata table "meta:file")
  assertEq "metadata create access count" createdMetadata.accessCount 1
  assertEq "metadata create hit count" createdMetadata.hitCount 0
  assertEq "metadata create last accessed epoch" createdMetadata.lastAccessedStabilization (some 0)
  let observer <- observe node
  State.stabilize state
  assertEq "metadata observer setup value" (← Observer.value! observer) 5
  let lookupNode <- MemoTable.lookup table "meta:file"
  assertEq "metadata lookup hit returns node" (lookupNode.map Incr.id) (some node.id)
  let reused <- MemoTable.getOrCreate table "meta:file" (fun _ => const state 99)
  assertEq "metadata getOrCreate hit reuses node" reused.id node.id
  let accessedMetadata <- expectMemoMetadata "metadata after hits" (← MemoTable.lookupMetadata table "meta:file")
  assertEq "metadata access count increments on hits" accessedMetadata.accessCount 3
  assertEq "metadata hit count increments on hits" accessedMetadata.hitCount 2
  assertEq "metadata last accessed epoch follows stabilization" accessedMetadata.lastAccessedStabilization (some 1)

def testMemoMetadataPinning : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _node <- MemoTable.getOrCreate table "pin:file" (fun _ => const state 7)
  assertEq "pin marks entry pinned" (← MemoTable.pin table "pin:file") true
  let pinnedMetadata <- expectMemoMetadata "metadata after pin" (← MemoTable.lookupMetadata table "pin:file")
  assertEq "pin updates metadata" pinnedMetadata.pinned true
  assertEq "unpin clears entry pin" (← MemoTable.unpin table "pin:file") true
  let unpinnedMetadata <- expectMemoMetadata "metadata after unpin" (← MemoTable.lookupMetadata table "pin:file")
  assertEq "unpin updates metadata" unpinnedMetadata.pinned false

def testMemoMetadataRetentionPolicy : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _hot <- MemoTable.getOrCreate table "hot:file" (fun _ => const state 1)
  let _pinned <- MemoTable.getOrCreate table "pinned:file" (fun _ => const state 2)
  let _cold <- MemoTable.getOrCreate table "cold:file" (fun _ => const state 3)
  let _ <- MemoTable.lookup table "hot:file"
  assertEq "retention pin succeeds" (← MemoTable.pin table "pinned:file") true
  let removed <- MemoTable.retainWithMetadata table (fun _key _node metadata => metadata.accessCount > 1)
  assertEq "retention removes only cold unpinned entry" removed 1
  assertEq "retention preserves hot entry" (Option.isSome (← MemoTable.lookupMetadata table "hot:file")) true
  let pinnedMetadata <- expectMemoMetadata "retention keeps pinned metadata" (← MemoTable.lookupMetadata table "pinned:file")
  assertEq "retention preserves pinned entry" pinnedMetadata.pinned true
  assertEq "retention evicts cold metadata" (Option.isNone (← MemoTable.lookupMetadata table "cold:file")) true
  assertEq "retention updates table size" (← MemoTable.size table) 2

def testMemoMetadataCleanup : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _drop <- MemoTable.getOrCreate table "drop:file" (fun _ => const state 1)
  let _stay <- MemoTable.getOrCreate table "stay:file" (fun _ => const state 2)
  assertEq "invalidate removes entry" (← MemoTable.invalidate table "drop:file") true
  assertEq "invalidate removes metadata" (Option.isNone (← MemoTable.lookupMetadata table "drop:file")) true
  let _clearA <- MemoTable.getOrCreate table "clear:a" (fun _ => const state 3)
  let _clearB <- MemoTable.getOrCreate table "clear:b" (fun _ => const state 4)
  assertEq "clear removes remaining entries" (← MemoTable.clear table) 3
  assertEq "clear removes stay metadata" (Option.isNone (← MemoTable.lookupMetadata table "stay:file")) true
  assertEq "clear removes clear metadata" (Option.isNone (← MemoTable.lookupMetadata table "clear:a")) true

  let sweepState <- State.create
  let sweepInput <- Var.create sweepState 10
  let sweepTable <- MemoTable.create (κ := String) (α := Nat) sweepState
  let kept <- MemoTable.getOrCreate sweepTable "keep:file" (fun _ =>
    map (Var.watch sweepInput) (fun value => value + 1))
  let _swept <- MemoTable.getOrCreate sweepTable "sweep:file" (fun _ => const sweepState 20)
  let keepObserver <- observe kept
  State.stabilize sweepState
  assertEq "sweep cleanup observer setup" (← Observer.value! keepObserver) 11
  assertEq "sweep cleanup removes one unreachable entry" (← MemoTable.sweepUnreachable sweepTable) 1
  assertEq "sweep cleanup removes metadata" (Option.isNone (← MemoTable.lookupMetadata sweepTable "sweep:file")) true
  assertEq "sweep cleanup keeps reachable metadata" (Option.isSome (← MemoTable.lookupMetadata sweepTable "keep:file")) true

def testMemoCustomStore : IO Unit := do
  let state <- State.create
  let entriesRef <- IO.mkRef (#[] : Array (String × Incr Nat))
  let table <- MemoTable.createWithStore state (arrayMemoStore entriesRef)
  let first <- MemoTable.getOrCreate table "custom:file" (fun _ => const state 7)
  let second <- MemoTable.getOrCreate table "custom:file" (fun _ => const state 99)
  assertEq "custom store memo hit returns same node" first.id second.id
  assertEq "custom store size after hit" (← MemoTable.size table) 1
  assertEq "custom store backing entries after hit" (← entriesRef.get).size 1
  assertEq "custom store invalidate existing" (← MemoTable.invalidate table "custom:file") true
  let third <- MemoTable.getOrCreate table "custom:file" (fun _ => const state 11)
  assertEq "custom store invalidation allocates fresh node" (first.id == third.id) false
  assertEq "custom store size after reload" (← MemoTable.size table) 1

def testMemoSnapshotPersistence : IO Unit := do
  let state <- State.create
  let input <- Var.create state 1
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let persisted <- MemoTable.getOrCreate table "persist:file" (fun _ =>
    map (Var.watch input) (fun value => value + 1))
  let _other <- MemoTable.getOrCreate table "persist:const" (fun _ => const state 7)
  let persistedObserver <- observe persisted
  State.stabilize state
  assertEq "snapshot setup value" (← Observer.value! persistedObserver) 2
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := String)
  assertEq "snapshot single save" (← MemoTable.persistStableValue table snapshotStore natStringCodec "persist:file") true
  assertEq "snapshot bulk save count" (← MemoTable.persistStableValues table snapshotStore natStringCodec) 2
  assertEq "snapshot store size" (← snapshotStore.size) 2
  let doubled <- map persisted (fun value => value * 2)
  let _doubledObserver <- observe doubled
  Var.set input 10
  let partialSlice <- State.stabilizeWithBudget state 1
  assertEq "snapshot save guard starts partial stabilization" partialSlice.completed false
  let blockedDuringPartial <-
    try
      let _ <- MemoTable.persistStableValues table snapshotStore natStringCodec
      pure false
    catch _ =>
      pure true
  assertEq "snapshot save blocked during partial stabilization" blockedDuringPartial true
  State.cancelStabilization state

  let restoredState <- State.create
  let restoredTable <- MemoTable.create (κ := String) (α := Nat) restoredState
  assertEq "snapshot preload single value" (← MemoTable.preloadConstValue restoredTable snapshotStore natStringCodec "persist:file") true
  assertEq "snapshot preload single does not duplicate existing key"
    (← MemoTable.preloadConstValue restoredTable snapshotStore natStringCodec "persist:file") false
  assertEq "snapshot preload bulk loads remaining values" (← MemoTable.preloadConstValues restoredTable snapshotStore natStringCodec) 1
  let restoredPersisted <- MemoTable.getOrCreate restoredTable "persist:file" (fun _ => const restoredState 999)
  let restoredConst <- MemoTable.getOrCreate restoredTable "persist:const" (fun _ => const restoredState 0)
  let restoredPersistedObserver <- observe restoredPersisted
  let restoredConstObserver <- observe restoredConst
  State.stabilize restoredState
  assertEq "snapshot restored persisted value" (← Observer.value! restoredPersistedObserver) 2
  assertEq "snapshot restored const value" (← Observer.value! restoredConstObserver) 7

def testMemoFileSnapshotPersistenceAcrossRestart : IO Unit := do
  IO.FS.withTempDir (fun snapshotDir => do
    let state <- State.create
    let input <- Var.create state 1
    let table <- MemoTable.create (κ := String) (α := Nat) state
    let persisted <- MemoTable.getOrCreate table "disk:file" (fun _ =>
      map (Var.watch input) (fun value => value + 1))
    let _other <- MemoTable.getOrCreate table "disk:const" (fun _ => const state 7)
    let observer <- observe persisted
    State.stabilize state
    assertEq "file snapshot setup value" (← Observer.value! observer) 2

    let snapshotStore <- MemoSnapshotStore.fileBacked snapshotDir
    assertEq "file snapshot bulk save count" (← MemoTable.persistStableValues table snapshotStore natStringCodec) 2
    assertEq "file snapshot store size" (← snapshotStore.size) 2
    let mut fileCount := 0
    for entry in (← snapshotDir.readDir) do
      if ← entry.path.isDir then
        pure ()
      else
        fileCount := fileCount + 1
    assertEq "file snapshot one file per key" fileCount 2

    let restoredState <- State.create
    let restoredTable <- MemoTable.create (κ := String) (α := Nat) restoredState
    let restoredSnapshotStore <- MemoSnapshotStore.fileBacked snapshotDir
    assertEq "file snapshot preload after restart" (← MemoTable.preloadConstValues restoredTable restoredSnapshotStore natStringCodec) 2
    let restoredFile <- MemoTable.getOrCreate restoredTable "disk:file" (fun _ => const restoredState 0)
    let restoredConst <- MemoTable.getOrCreate restoredTable "disk:const" (fun _ => const restoredState 0)
    let restoredFileObserver <- observe restoredFile
    let restoredConstObserver <- observe restoredConst
    State.stabilize restoredState
    assertEq "file snapshot restored file value" (← Observer.value! restoredFileObserver) 2
    assertEq "file snapshot restored const value" (← Observer.value! restoredConstObserver) 7
  )

def testMemoFileSnapshotCorruptionTreatedAsMiss : IO Unit := do
  IO.FS.withTempDir (fun snapshotDir => do
    let snapshotStore <- MemoSnapshotStore.fileBacked snapshotDir
    snapshotStore.insert "disk:corrupt" "31"
    let mut corrupted := false
    for entry in (← snapshotDir.readDir) do
      if ← entry.path.isDir then
        pure ()
      else
        IO.FS.writeFile entry.path "{invalid-json"
        corrupted := true
    assertEq "file snapshot corruption fixture wrote at least one file" corrupted true
    assertEq "file snapshot lookup treats corrupted entry as miss"
      (← snapshotStore.lookup "disk:corrupt") none

    let state <- State.create
    let table <- MemoTable.create (κ := String) (α := Nat) state
    assertEq "file snapshot preload treats corrupted entry as miss"
      (← MemoTable.preloadConstValue table snapshotStore natStringCodec "disk:corrupt") false
    assertEq "file snapshot bulk preload skips corrupted entry"
      (← MemoTable.preloadConstValues table snapshotStore natStringCodec) 0
  )

def testMemoValidatedSnapshotPreloadSuccess : IO Unit := do
  let state <- State.create
  let source <- Var.create state 40
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let persisted <- MemoTable.getOrCreate table "validated:file" (fun _ =>
    map (Var.watch source) (fun value => value + 2))
  let observer <- observe persisted
  State.stabilize state
  assertEq "validated preload setup value" (← Observer.value! observer) 42
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := MemoSnapshotEnvelope String)
  let saved <- MemoTable.persistStableValueEnvelope table snapshotStore natStringCodec
    (validatedSnapshotMetadata "memo:v1" "build-42" "digest-alpha" 150)
    "validated:file"
  assertEq "validated preload saves envelope" saved true

  let restoredState <- State.create
  let restoredTable <- MemoTable.create (κ := String) (α := Nat) restoredState
  let outcome <- MemoTable.preloadConstValueValidated restoredTable snapshotStore natStringCodec validatedSnapshotPolicy "validated:file"
  assertEq "validated preload loads matching envelope" outcome .loaded
  let restored <- MemoTable.getOrCreate restoredTable "validated:file" (fun _ => const restoredState 0)
  let restoredObserver <- observe restored
  State.stabilize restoredState
  assertEq "validated preload restores value" (← Observer.value! restoredObserver) 42

def testMemoValidatedSnapshotSchemaMismatch : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := MemoSnapshotEnvelope String)
  snapshotStore.insert "schema:file" {
    metadata := validatedSnapshotMetadata "memo:v2" "build-42" "digest-alpha" 150
    payload := "12"
  }
  let outcome <- MemoTable.preloadConstValueValidated table snapshotStore natStringCodec validatedSnapshotPolicy "schema:file"
  assertEq "validated preload rejects schema mismatch" outcome
    (.rejected (.schemaMismatch "memo:v1" "memo:v2"))

def testMemoValidatedSnapshotBuildMismatch : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := MemoSnapshotEnvelope String)
  snapshotStore.insert "build:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-43" "digest-alpha" 150
    payload := "13"
  }
  let outcome <- MemoTable.preloadConstValueValidated table snapshotStore natStringCodec validatedSnapshotPolicy "build:file"
  assertEq "validated preload rejects build mismatch" outcome
    (.rejected (.buildMismatch "build-42" "build-43"))

def testMemoValidatedSnapshotInputDigestMismatch : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := MemoSnapshotEnvelope String)
  snapshotStore.insert "digest:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-42" "digest-beta" 150
    payload := "14"
  }
  let outcome <- MemoTable.preloadConstValueValidated table snapshotStore natStringCodec validatedSnapshotPolicy "digest:file"
  assertEq "validated preload rejects digest mismatch" outcome
    (.rejected (.inputDigestMismatch "digest-alpha" "digest-beta"))

def testMemoValidatedSnapshotDecodeFailure : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := MemoSnapshotEnvelope String)
  snapshotStore.insert "decode:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-42" "digest-alpha" 150
    payload := "not-a-nat"
  }
  let outcome <- MemoTable.preloadConstValueValidated table snapshotStore natStringCodec validatedSnapshotPolicy "decode:file"
  assertEq "validated preload surfaces decode failure" outcome
    (.decodeError "expected Nat string")

def testMemoSnapshotLegacyPreloadCompatibility : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := String)
  snapshotStore.insert "legacy:file" "9"
  snapshotStore.insert "legacy:other" "11"
  assertEq "legacy preload single still loads raw snapshots"
    (← MemoTable.preloadConstValue table snapshotStore natStringCodec "legacy:file") true
  assertEq "legacy preload single still skips existing keys"
    (← MemoTable.preloadConstValue table snapshotStore natStringCodec "legacy:file") false
  let summaryState <- State.create
  let summaryTable <- MemoTable.create (κ := String) (α := Nat) summaryState
  let loaded <- MemoTable.preloadConstValues summaryTable snapshotStore natStringCodec
  assertEq "legacy preload bulk still returns loaded count" loaded 2

-- FR-11: two sequential writers to the same key (simulates temp+rename race);
-- the second write wins and the stored value must be valid.
def testMemoFileSnapshotSequentialWritersSameKey : IO Unit := do
  IO.FS.withTempDir (fun snapshotDir => do
    let store <- MemoSnapshotStore.fileBacked snapshotDir
    -- First writer stores value 10
    store.insert "shared:key" "10"
    assertEq "sequential writer first value" (← store.lookup "shared:key") (some "10")
    -- Second writer overwrites with value 20 (atomic rename)
    store.insert "shared:key" "20"
    let final <- store.lookup "shared:key"
    assertEq "sequential writer second value wins" final (some "20")
    -- Preload into a MemoTable; the entry must decode to 20
    let state <- State.create
    let table <- MemoTable.create (κ := String) (α := Nat) state
    assertEq "sequential writer preload succeeds"
      (← MemoTable.preloadConstValue table store natStringCodec "shared:key") true
    let node <- MemoTable.getOrCreate table "shared:key" (fun _ => const state 0)
    let obs  <- observe node
    State.stabilize state
    assertEq "sequential writer loaded value is 20" (← Observer.value! obs) 20
  )

-- FR-11: MemoSnapshotPreloadSummary correctly counts validation rejections
-- across the full spectrum of outcomes (loaded / existing / rejected / decode error).
def testMemoSnapshotPreloadSummaryRejectionCounts : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  -- Pre-populate one entry so it shows up as "alreadyPresent"
  let _ <- MemoTable.getOrCreate table "present:file" (fun _ => const state 5)
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := MemoSnapshotEnvelope String)
  -- This one will be loaded (key not yet in table, valid envelope)
  snapshotStore.insert "toload:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-42" "digest-alpha" 150
    payload  := "99"
  }
  -- This one will be counted as alreadyPresent (key already in table)
  snapshotStore.insert "present:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-42" "digest-alpha" 150
    payload  := "5"
  }
  -- This one will be rejected (build-id mismatch)
  snapshotStore.insert "rejected:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-99" "digest-alpha" 150
    payload  := "1"
  }
  -- This one will fail to decode (bad payload)
  snapshotStore.insert "badjson:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-42" "digest-alpha" 150
    payload  := "notanumber"
  }
  let summary <- MemoTable.preloadConstValuesValidated table snapshotStore natStringCodec validatedSnapshotPolicy
  assertEq "preload summary: loaded"         summary.loaded        1
  assertEq "preload summary: alreadyPresent" summary.alreadyPresent 1
  assertEq "preload summary: rejected"       summary.rejected      1
  assertEq "preload summary: decodeError"    summary.decodeError   1
  assertEq "preload summary: missing"        summary.missing       0

def testMemoValidatedSnapshotBulkSummary : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _existing <- MemoTable.getOrCreate table "existing:file" (fun _ => const state 77)
  let snapshotStore <- MemoSnapshotStore.hashMap (κ := String) (σ := MemoSnapshotEnvelope String)
  snapshotStore.insert "loaded:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-42" "digest-alpha" 150
    payload := "21"
  }
  snapshotStore.insert "existing:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-42" "digest-alpha" 150
    payload := "99"
  }
  snapshotStore.insert "rejected:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-43" "digest-alpha" 150
    payload := "23"
  }
  snapshotStore.insert "decode:file" {
    metadata := validatedSnapshotMetadata "memo:v1" "build-42" "digest-alpha" 150
    payload := "bad"
  }
  let summary <- MemoTable.preloadConstValuesValidated table snapshotStore natStringCodec validatedSnapshotPolicy
  assertEq "validated preload bulk counts loaded" summary.loaded 1
  assertEq "validated preload bulk counts existing" summary.alreadyPresent 1
  assertEq "validated preload bulk counts rejected" summary.rejected 1
  assertEq "validated preload bulk counts decode errors" summary.decodeError 1
  assertEq "validated preload bulk missing counter stays zero" summary.missing 0

def testBudgetedStabilization : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let z <- map y (fun value => value * 2)
  let observer <- observe z
  let firstSlice <- State.stabilizeWithBudget state 1
  assertEq "initial budget slice incomplete" firstSlice.completed false
  assertEq "initial budget leaves observer empty" (← Observer.value? observer) none
  let secondSlice <- State.stabilizeWithBudget state 1
  assertEq "initial budget completes" secondSlice.completed true
  assertEq "initial budgeted value" (← Observer.value! observer) 4
  Var.set x 10
  let updateVar <- State.stabilizeWithBudget state 1
  assertEq "update first slice incomplete" updateVar.completed false
  assertEq "observer not refreshed mid budget" (← Observer.value! observer) 4
  let updateMap <- State.stabilizeWithBudget state 1
  assertEq "update second slice incomplete" updateMap.completed false
  let updateDone <- State.stabilizeWithBudget state 1
  assertEq "update budget completes" updateDone.completed true
  assertEq "budgeted updated value" (← Observer.value! observer) 22
  Var.set x 20
  let canceled <- State.stabilizeWithBudget state 1
  assertEq "cancel test starts partial" canceled.completed false
  State.cancelStabilization state
  assertEq "cancel clears partial" (← State.hasPartialStabilization state) false
  Var.set x 30
  State.stabilize state
  assertEq "full stabilize after cancel" (← Observer.value! observer) 62

def testBudgetedBindKeepsEpoch : IO Unit := do
  let state <- State.create
  let useLeft <- Var.create state true
  let left <- Var.create state 1
  let right <- Var.create state 10
  let selected <- ifThenElse (Var.watch useLeft) (Var.watch left) (Var.watch right)
  let observer <- observe selected
  State.stabilize state
  assertEq "budgeted bind initial" (← Observer.value! observer) 1
  Var.set useLeft false
  let selectorSlice <- State.stabilizeWithBudget state 1
  assertEq "budgeted bind selector slice incomplete" selectorSlice.completed false
  let bindSlice <- State.stabilizeWithBudget state 1
  assertEq "budgeted bind reuses stabilization epoch" bindSlice.stats.stabilization selectorSlice.stats.stabilization
  let doneSlice <- State.stabilizeWithBudget state 1
  assertEq "budgeted bind completes" doneSlice.completed true
  assertEq "budgeted bind switched branch" (← Observer.value! observer) 10

def testIndexedAggregate : IO Unit := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 5
  let aggregate <- IndexedAggregate.create (κ := String) state 0 (fun acc _key value => acc + value)
  IndexedAggregate.insertOrReplace aggregate "a" (Var.watch a)
  IndexedAggregate.insertOrReplace aggregate "b" (Var.watch b)
  let observer <- observe (IndexedAggregate.watch aggregate)
  State.stabilize state
  assertEq "indexed aggregate initial" (← Observer.value! observer) 3
  Var.set a 10
  State.stabilize state
  assertEq "indexed aggregate input update" (← Observer.value! observer) 12
  IndexedAggregate.insertOrReplace aggregate "b" (Var.watch c)
  State.stabilize state
  assertEq "indexed aggregate replace" (← Observer.value! observer) 15
  assertEq "indexed aggregate remove missing" (← IndexedAggregate.remove aggregate "missing") false
  assertEq "indexed aggregate remove" (← IndexedAggregate.remove aggregate "a") true
  State.stabilize state
  assertEq "indexed aggregate after remove" (← Observer.value! observer) 5
  assertEq "indexed aggregate clear count" (← IndexedAggregate.clear aggregate) 1
  State.stabilize state
  assertEq "indexed aggregate after clear" (← Observer.value! observer) 0
  IndexedAggregate.insertOrReplace aggregate "a" (Var.watch a)
  State.stabilize state
  Var.set a 20
  let partialSlice <- State.stabilizeWithBudget state 1
  assertEq "indexed aggregate guard starts partial" partialSlice.completed false
  let blocked <-
    try
      IndexedAggregate.insertOrReplace aggregate "c" (Var.watch c)
      pure false
    catch _ =>
      pure true
  assertEq "indexed aggregate mutation blocked during partial stabilization" blocked true
  State.cancelStabilization state

def testAssocIndexedAggregate : IO Unit := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let d <- Var.create state 4
  let bReplacement <- Var.create state 20
  let aggregate <- AssocIndexedAggregate.create (κ := String) state "" (fun key value => s!"[{key}:{value}]") (· ++ ·)
  AssocIndexedAggregate.insertOrReplace aggregate "a" (Var.watch a)
  AssocIndexedAggregate.insertOrReplace aggregate "b" (Var.watch b)
  AssocIndexedAggregate.insertOrReplace aggregate "c" (Var.watch c)
  let observer <- observe (AssocIndexedAggregate.watch aggregate)
  State.stabilize state
  assertEq "assoc indexed aggregate initial" (← Observer.value! observer) "[a:1][b:2][c:3]"
  assertEq "assoc indexed aggregate size initial" (← AssocIndexedAggregate.size aggregate) 3
  AssocIndexedAggregate.insertOrReplace aggregate "b" (Var.watch bReplacement)
  State.stabilize state
  assertEq "assoc indexed aggregate replace" (← Observer.value! observer) "[a:1][b:20][c:3]"
  assertEq "assoc indexed aggregate size after replace" (← AssocIndexedAggregate.size aggregate) 3
  assertEq "assoc indexed aggregate remove missing" (← AssocIndexedAggregate.remove aggregate "missing") false
  assertEq "assoc indexed aggregate remove" (← AssocIndexedAggregate.remove aggregate "b") true
  State.stabilize state
  assertEq "assoc indexed aggregate after remove" (← Observer.value! observer) "[a:1][c:3]"
  assertEq "assoc indexed aggregate size after remove" (← AssocIndexedAggregate.size aggregate) 2
  AssocIndexedAggregate.insertOrReplace aggregate "d" (Var.watch d)
  State.stabilize state
  assertEq "assoc indexed aggregate insert after tombstone keeps order" (← Observer.value! observer) "[a:1][c:3][d:4]"
  assertEq "assoc indexed aggregate clear count" (← AssocIndexedAggregate.clear aggregate) 3
  State.stabilize state
  assertEq "assoc indexed aggregate after clear" (← Observer.value! observer) ""
  assertEq "assoc indexed aggregate size after clear" (← AssocIndexedAggregate.size aggregate) 0
  AssocIndexedAggregate.insertOrReplace aggregate "d" (Var.watch d)
  AssocIndexedAggregate.insertOrReplace aggregate "a" (Var.watch a)
  State.stabilize state
  assertEq "assoc indexed aggregate clear resets insertion frontier" (← Observer.value! observer) "[d:4][a:1]"

def testAssocIndexedAggregatePathLocalUpdates : IO Unit := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let d <- Var.create state 4
  let aggregate <- AssocIndexedAggregate.create (κ := String) state 0 (fun _ value => value) (· + ·)
  AssocIndexedAggregate.insertOrReplace aggregate "a" (Var.watch a)
  AssocIndexedAggregate.insertOrReplace aggregate "b" (Var.watch b)
  AssocIndexedAggregate.insertOrReplace aggregate "c" (Var.watch c)
  AssocIndexedAggregate.insertOrReplace aggregate "d" (Var.watch d)
  let observer <- observe (AssocIndexedAggregate.watch aggregate)
  State.stabilize state
  assertEq "assoc indexed aggregate path-local initial" (← Observer.value! observer) 10
  Var.set a 10
  let firstStats <- State.stabilizeWithStats state
  assertEq "assoc indexed aggregate first single-key update" (← Observer.value! observer) 19
  if firstStats.nodesChanged <= 6 then
    pure ()
  else
    throw (IO.userError s!"assoc indexed aggregate single-key update changed too many nodes: expected at most 6, got {firstStats.nodesChanged}")
  Var.set a 11
  let secondStats <- State.stabilizeWithStats state
  assertEq "assoc indexed aggregate second single-key update" (← Observer.value! observer) 20
  assertEq "assoc indexed aggregate repeated single-key update node count" secondStats.nodesChanged firstStats.nodesChanged

def testAssocIndexedAggregateMutationGuard : IO Unit := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let aggregate <- AssocIndexedAggregate.create (κ := String) state 0 (fun _ value => value) (· + ·)
  AssocIndexedAggregate.insertOrReplace aggregate "a" (Var.watch a)
  AssocIndexedAggregate.insertOrReplace aggregate "b" (Var.watch b)
  AssocIndexedAggregate.insertOrReplace aggregate "c" (Var.watch c)
  let observer <- observe (AssocIndexedAggregate.watch aggregate)
  State.stabilize state
  assertEq "assoc indexed aggregate guard initial" (← Observer.value! observer) 6
  Var.set a 20
  let partialSlice <- State.stabilizeWithBudget state 1
  assertEq "assoc indexed aggregate guard starts partial" partialSlice.completed false
  let blocked <-
    try
      AssocIndexedAggregate.insertOrReplace aggregate "d" (Var.watch c)
      pure false
    catch _ =>
      pure true
  assertEq "assoc indexed aggregate mutation blocked during partial stabilization" blocked true
  State.cancelStabilization state

def testIncrResult : IO Unit := do
  let state <- State.create
  let okNode <- IncrResult.ok (ε := String) state 2
  let mapped <- IncrResult.map okNode (fun value => value * 3)
  let bound <- IncrResult.bind okNode (fun value => IncrResult.ok (ε := String) state (value + 5))
  let errorNode <- IncrResult.error (α := Nat) state "parse failed"
  let mappedError <- IncrResult.map errorNode (fun value => value * 10)
  let recovered <- IncrResult.recover errorNode (fun _ => IncrResult.ok (ε := String) state 7)
  let combined <- IncrResult.map2 mapped recovered (fun left right => left + right)
  let valueProjection <- IncrResult.value? mapped
  let errorProjection <- IncrResult.error? mappedError
  Incr.setCutoff mapped IncrResult.cutoffOfEq
  let mappedObserver <- observe mapped
  let boundObserver <- observe bound
  let errorObserver <- observe mappedError
  let recoveredObserver <- observe recovered
  let combinedObserver <- observe combined
  let valueObserver <- observe valueProjection
  let errorTextObserver <- observe errorProjection
  State.stabilize state
  assertOk "result map ok" (← Observer.value! mappedObserver) 6
  assertOk "result bind ok" (← Observer.value! boundObserver) 7
  assertError "result map preserves error" (← Observer.value! errorObserver) "parse failed"
  assertOk "result recover" (← Observer.value! recoveredObserver) 7
  assertOk "result map2" (← Observer.value! combinedObserver) 13
  assertEq "result value projection" (← Observer.value! valueObserver) (some 6)
  assertEq "result error projection" (← Observer.value! errorTextObserver) (some "parse failed")

def testDocumentVersioning : IO Unit := do
  let state <- State.create
  let doc <- Document.create state 10
  let query <- map (Document.watchContent doc) (fun value => value + 1)
  let tagged <- Document.tag doc query
  let currentOnly <- Document.requireCurrent doc tagged
  let taggedObserver <- observe tagged
  let currentObserver <- observe currentOnly
  State.stabilize state
  assertEq "document tagged initial" (← Observer.value! taggedObserver) ({ version := 0, value := 11 } : Document.Versioned Nat)
  assertOk "document current initial" (← Observer.value! currentObserver) 11
  let token <- Document.requestToken doc 42
  let newVersion <- Document.edit doc (fun value => value + 10)
  assertEq "document edit version" newVersion 1
  assertEq "document stale tagged value" (← Incr.staleValue? tagged) (some ({ version := 0, value := 11 } : Document.Versioned Nat))
  assertEq "document token becomes stale" (← Document.requestIsCurrent doc token) false
  State.stabilize state
  assertEq "document tagged after edit" (← Observer.value! taggedObserver) ({ version := 1, value := 21 } : Document.Versioned Nat)
  assertOk "document current after edit" (← Observer.value! currentObserver) 21
  let snapshot <- Document.snapshot doc
  assertEq "document snapshot" snapshot ({ version := 1, content := 20 } : Document.Snapshot Nat)
  let staleResult <- const state ({ version := 0, value := 999 } : Document.Versioned Nat)
  let rejected <- Document.requireCurrent doc staleResult
  let rejectedObserver <- observe rejected
  State.stabilize state
  assertError "document rejects stale result" (← Observer.value! rejectedObserver) "stale result for document version 0, current version is 1"

def testMemoSweepUnreachable : IO Unit := do
  let state <- State.create
  let input <- Var.create state 1
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let kept <- MemoTable.getOrCreate table "keep" (fun _ =>
    map (Var.watch input) (fun value => value + 1))
  let swept1 <- MemoTable.getOrCreate table "sweep:one" (fun _ => const state 100)
  let swept2 <- MemoTable.getOrCreate table "sweep:two" (fun _ => const state 200)
  let keepObserver <- observe kept
  let sweptObserver <- observe swept2
  State.stabilize state
  assertEq "sweep setup observer value" (← Observer.value! keepObserver) 2
  assertEq "reachable node helper includes observed node" (← Incr.isReachableFromActiveObservers kept) true
  assertEq "reachable node helper excludes unobserved node" (← Incr.isReachableFromActiveObservers swept1) false
  Observer.disallowFutureUse sweptObserver
  State.stabilize state
  let removed <- MemoTable.sweepUnreachable table
  assertEq "sweep removes unreachable entries" removed 2
  assertEq "sweep keeps reachable memo entry" (← MemoTable.size table) 1
  assertEq "sweep removed first unreachable key" (Option.isNone (← MemoTable.lookup table "sweep:one")) true
  assertEq "sweep removed second unreachable key" (Option.isNone (← MemoTable.lookup table "sweep:two")) true
  assertEq "sweep keeps reachable key" (Option.isSome (← MemoTable.lookup table "keep")) true
  let y <- map (Var.watch input) (fun value => value * 2)
  let z <- map y (fun value => value + 1)
  let _zObserver <- observe z
  let partialSlice <- State.stabilizeWithBudget state 1
  assertEq "sweep guard enters partial stabilization" partialSlice.completed false
  let blockedDuringPartial <-
    try
      let _ <- MemoTable.sweepUnreachable table
      pure false
    catch _ =>
      pure true
  assertEq "sweep blocked during partial stabilization" blockedDuringPartial true
  State.cancelStabilization state
  let sweepAttemptedDuringStabilization <- IO.mkRef false
  let sweepBlockedDuringStabilization <- IO.mkRef false
  let frozen <- freeze kept
  State.onDependenciesChanged state (fun id _oldChildren _newChildren => do
    if id == frozen.id then
      sweepAttemptedDuringStabilization.set true
      let blocked <-
        try
          let _ <- MemoTable.sweepUnreachable table
          pure false
        catch _ =>
          pure true
      sweepBlockedDuringStabilization.set blocked
    else
      pure ())
  let _frozenObserver <- observe frozen
  State.stabilize state
  assertEq "sweep was attempted during stabilization" (← sweepAttemptedDuringStabilization.get) true
  assertEq "sweep blocked during active stabilization" (← sweepBlockedDuringStabilization.get) true

-- C3: FR-10 QueryM churn bound test

/-- k=100 keys, each binding on a per-key Bool selector; flip selectors t=1,000 times
    with reclaimUnreachableNodes every r=100 flips; live nodes bounded by c₁·k + c₂. -/
def testQueryChurnBoundedNodeGrowth : IO Unit := do
  let k := 100
  let t := 1000
  let r := 100
  -- c₁=4, c₂=100: measured 3 live nodes per key (var+bind+const) × 1.25 headroom
  -- WITH reclaim: maxLive ≈ 300; WITHOUT reclaim: maxLive ≈ 1300 → bound catches violation
  let c1 := 4
  let c2 := 100
  let state <- State.create
  -- Per-key Bool selector vars
  let mut selectorVars : Array (Var Bool) := #[]
  for _ in [:k] do
    let v <- Var.create state false
    selectorVars := selectorVars.push v
  -- Build rules: each key's result depends on its selector via bind
  let selectorArr := selectorVars  -- immutable capture for the closure
  let rules : QueryRules Nat Nat := {
    describeKey := fun i => s!"key-{i}"
    build := fun i => do
      match selectorArr[i % k]? with
      | none => QueryM.ofIO (ret state (0 : Nat))
      | some v =>
          let sel <- QueryM.ofIncr (Var.watch v)
          QueryM.ofIO (ret state (if sel == true then (1 : Nat) else 0))
  }
  let table <- QueryTable.create state rules
  -- Intern all keys and observe them
  let mut observers : Array (Observer Nat) := #[]
  for i in [:k] do
    let node <- QueryTable.request table i
    let obs <- observe node
    observers := observers.push obs
  State.stabilize state
  -- Churn: flip selectors and reclaim periodically
  for step in [:t] do
    let keyIdx := step % k
    match selectorVars[keyIdx]? with
    | none => pure ()
    | some sel =>
        Var.set sel (!(← sel.current.get))
        State.stabilize state
        if (step + 1) % r == 0 then
          let _ <- State.reclaimUnreachableNodes state
          let (total, recycled) <- State.nodeSlotStats state
          let live := total - recycled
          assertEq s!"churn step {step+1}: live nodes ≤ c₁·k+c₂={c1*k+c2}"
            (decide (live <= c1 * k + c2)) true
  -- Verify values are correct (all selectors in their final state)
  for i in [:k] do
    match selectorVars[i]?, observers[i]? with
    | some sel, some obs =>
        let expectedVal : Nat := if (← sel.current.get) == true then 1 else 0
        assertEq s!"churn key {i} final value" (← Observer.value! obs) expectedVal
    | _, _ => pure ()

-- C2: FR-4 table coherence — MemoTable pins interned nodes so GC can't reclaim them
def testMemoTablePinsProtectFromGC : IO Unit := do
  let state <- State.create
  let source <- Var.create state "hello"
  let table <- QueryTable.create state (toyQueryRules source)
  -- Intern a node via request
  let nodeBeforeReclaim <- QueryTable.request table .file
  let idBefore := nodeBeforeReclaim.id
  let genBefore <- Internal.State.nodeGeneration state idBefore
  -- Drop all observers so the node would normally be reclaimable
  -- (the QueryTable holds no observer — pinning is the only protection)
  let _ <- State.reclaimUnreachableNodes state
  -- Request again: must return same node id + generation (pin prevented reclaim)
  let nodeAfterReclaim <- QueryTable.request table .file
  assertEq "FR-4: pin protects node id across GC" nodeAfterReclaim.id idBefore
  let genAfter <- Internal.State.nodeGeneration state idBefore
  assertEq "FR-4: pin protects generation across GC" genAfter genBefore
  -- Stabilize and check value is correct
  let obs <- observe nodeAfterReclaim
  State.stabilize state
  assertEq "FR-4: pinned node value still correct" (← Observer.value! obs) "hello"

def runAll : IO Unit := do
  testQueryPrimitives
  testMemoLifecycle
  testMemoMetadataAccessAccounting
  testMemoMetadataPinning
  testMemoMetadataRetentionPolicy
  testMemoMetadataCleanup
  testMemoCustomStore
  testMemoSnapshotPersistence
  testMemoFileSnapshotPersistenceAcrossRestart
  testMemoFileSnapshotCorruptionTreatedAsMiss
  testMemoValidatedSnapshotPreloadSuccess
  testMemoValidatedSnapshotSchemaMismatch
  testMemoValidatedSnapshotBuildMismatch
  testMemoValidatedSnapshotInputDigestMismatch
  testMemoValidatedSnapshotDecodeFailure
  testMemoSnapshotLegacyPreloadCompatibility
  -- E4: FR-11 file-backed snapshot store tests
  testMemoFileSnapshotSequentialWritersSameKey
  testMemoSnapshotPreloadSummaryRejectionCounts
  testMemoValidatedSnapshotBulkSummary
  testQueryMStack
  testQueryMEditRecomputes
  testQueryMMemoReuse
  testReclaimUnreachableNodesMitigatesQueryBindChurn
  testQueryTableInvalidatePreservesIdentity
  testQueryMCycleDetection
  testExternalActionReferenceLoop
  testBudgetedStabilization
  testBudgetedBindKeepsEpoch
  testIndexedAggregate
  testAssocIndexedAggregate
  testAssocIndexedAggregatePathLocalUpdates
  testAssocIndexedAggregateMutationGuard
  testIncrResult
  testDocumentVersioning
  testMemoSweepUnreachable
  -- C3: FR-10 churn bound
  testQueryChurnBoundedNodeGrowth
  -- C2: FR-4 pin protection
  testMemoTablePinsProtectFromGC

end Query
end Tests
end Leancremental
