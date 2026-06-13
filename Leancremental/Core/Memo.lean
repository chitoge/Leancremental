import Std.Data.HashMap
import Lean.Data.Json
import Leancremental.Core.Basic

/-!
Keyed memoization for query-style incremental graph construction.

An LSP-oriented interpreter or compiler often has stable query keys such as
files, declaration names, syntax node ids, or request-local positions. A
`MemoTable` maps those keys to graph nodes so repeated requests reuse the same
incremental computation instead of allocating duplicate subgraphs.

The live memo table stores `Incr α` handles, so its backing store is necessarily
process-local. To support user choice for storage and serialization without
pretending that live graph nodes are serializable, this module splits the API
into two layers:

- `MemoStore κ α`: pluggable live storage for memoized `Incr α` nodes.
- `MemoSnapshotStore κ σ` plus `MemoValueCodec α σ`: optional snapshot storage
  for stable serialized values, which can later be preloaded back as `const`
  nodes.
-/

namespace Leancremental

def memoContainsKey [BEq κ] (keys : Array κ) (key : κ) : Bool :=
  keys.any (fun existing => existing == key)

/--
Pluggable live storage for memoized incremental nodes.

This stores live `Incr` handles, so it is only for in-process use.
-/
structure MemoStore (κ : Type) (α : Type) where
  /-- Look up a live memoized node by key. -/
  lookup : κ -> IO (Option (Incr α))
  /-- Insert or replace one live memoized node. -/
  insert : κ -> Incr α -> IO Unit
  /-- Remove one memoized node, returning whether it existed. -/
  erase : κ -> IO Bool
  /-- Keep only entries accepted by `predicate`, returning the number removed. -/
  retain : (κ -> Incr α -> Bool) -> IO Nat
  /-- Remove all entries, returning the number removed. -/
  clear : IO Nat
  /-- Number of currently stored entries. -/
  size : IO Nat
  /-- Snapshot the current live entries. -/
  entries : IO (Array (κ × Incr α))

namespace MemoStore

/-- In-memory `Std.HashMap` implementation of `MemoStore`. -/
def hashMap [BEq κ] [Hashable κ] : IO (MemoStore κ α) := do
  let cache <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap κ (Incr α))
  pure {
    lookup := fun key => do
      pure ((← cache.get).get? key),
    insert := fun key node =>
      cache.modify (fun current => current.insert key node),
    erase := fun key => do
      let current <- cache.get
      let existed := (current.get? key).isSome
      cache.set (current.erase key)
      pure existed,
    retain := fun predicate => do
      let current <- cache.get
      let filtered := current.filter predicate
      cache.set filtered
      pure (current.size - filtered.size),
    clear := do
      let current <- cache.get
      cache.set (Std.HashMap.emptyWithCapacity : Std.HashMap κ (Incr α))
      pure current.size,
    size := do
      pure (← cache.get).size,
    entries := do
      pure (← cache.get).toList.toArray
  }

end MemoStore

/-- Runtime metadata tracked for each live memo entry. -/
structure MemoEntryMetadata where
  /-- Number of successful entry accesses, including the creation miss that installed the entry. -/
  accessCount : Nat := 0
  /-- Number of direct cache hits that reused an existing entry. -/
  hitCount : Nat := 0
  /-- Most recent completed or active stabilization number that accessed this entry. -/
  lastAccessedStabilization : Option Nat := none
  /-- Whether retention policies should keep this entry resident. -/
  pinned : Bool := false
deriving Repr, BEq, Inhabited

/--
Codec between stable memo values and a serialized snapshot representation.

This is used for snapshot preload and persistence. It serializes values, not
live graph nodes.
-/
structure MemoValueCodec (α : Type) (σ : Type) where
  /-- Encode one stable memo value to the snapshot representation. -/
  encode : α -> Except String σ
  /-- Decode one snapshot representation back to a memo value. -/
  decode : σ -> Except String α

namespace MemoValueCodec

/-- Identity codec for in-memory snapshot experiments and tests. -/
def id : MemoValueCodec α α := {
  encode := fun value => .ok value,
  decode := fun value => .ok value
}

/--
JSON codec for any `α` with `Lean.ToJson` and `Lean.FromJson` instances.

Encodes via `Lean.Json.compress (Lean.toJson value)` and decodes via
`Lean.fromJson?` after `Lean.Json.parse`. Decode failures surface as
`decodeError` outcomes in `MemoSnapshotPreloadSummary` — no exceptions.
-/
def ofJson [Lean.ToJson α] [Lean.FromJson α] : MemoValueCodec α String := {
  encode := fun value => .ok (Lean.Json.compress (Lean.toJson value)),
  decode := fun serialized =>
    (Lean.Json.parse serialized |>.mapError toString) >>=
    (fun json => Lean.fromJson? json |>.mapError toString)
}

end MemoValueCodec

/-- Metadata stored alongside one serialized memo snapshot payload. -/
structure MemoSnapshotEnvelopeMetadata where
  /-- Snapshot schema or format identifier. -/
  schema : String
  /-- Build or binary compatibility identifier. -/
  build : String := ""
  /-- Digest of the source inputs the snapshot was derived from. -/
  inputDigest : String := ""
  /-- Caller-supplied timestamp for staleness checks. -/
  timestamp : Nat := 0
deriving Repr, BEq, Inhabited

/-- Serialized memo payload together with metadata used for validation. -/
structure MemoSnapshotEnvelope (σ : Type) where
  /-- Compatibility and freshness metadata. -/
  metadata : MemoSnapshotEnvelopeMetadata
  /-- Encoded stable memo value payload. -/
  payload : σ

/-- Optional checks applied before loading an envelope snapshot. -/
structure MemoSnapshotValidationPolicy where
  /-- Require an exact schema match when provided. -/
  expectedSchema : Option String := none
  /-- Require an exact build identifier match when provided. -/
  expectedBuild : Option String := none
  /-- Require an exact input digest match when provided. -/
  expectedInputDigest : Option String := none
  /-- Require the snapshot timestamp to be at least this fresh when provided. -/
  minTimestamp : Option Nat := none
deriving Repr, BEq, Inhabited

/-- Why a validated snapshot envelope was rejected before decode. -/
inductive MemoSnapshotRejectionReason where
  /-- The snapshot schema did not match the expected schema. -/
  | schemaMismatch (expected : String) (actual : String)
  /-- The snapshot build identifier did not match the expected build. -/
  | buildMismatch (expected : String) (actual : String)
  /-- The snapshot input digest did not match the expected digest. -/
  | inputDigestMismatch (expected : String) (actual : String)
  /-- The snapshot timestamp was older than the minimum accepted timestamp. -/
  | timestampTooOld (minimum : Nat) (actual : Nat)
deriving Repr, BEq

namespace MemoSnapshotValidationPolicy

/-- Validate one snapshot envelope metadata record against a caller policy. -/
def validate (policy : MemoSnapshotValidationPolicy)
    (metadata : MemoSnapshotEnvelopeMetadata) : Except MemoSnapshotRejectionReason Unit := do
  match policy.expectedSchema with
  | some expected =>
      if metadata.schema == expected then
        pure ()
      else
        .error (.schemaMismatch expected metadata.schema)
  | none =>
      pure ()
  match policy.expectedBuild with
  | some expected =>
      if metadata.build == expected then
        pure ()
      else
        .error (.buildMismatch expected metadata.build)
  | none =>
      pure ()
  match policy.expectedInputDigest with
  | some expected =>
      if metadata.inputDigest == expected then
        pure ()
      else
        .error (.inputDigestMismatch expected metadata.inputDigest)
  | none =>
      pure ()
  match policy.minTimestamp with
  | some minimum =>
      if minimum <= metadata.timestamp then
        pure ()
      else
        .error (.timestampTooOld minimum metadata.timestamp)
  | none =>
      pure ()

end MemoSnapshotValidationPolicy

/-- Result of attempting to preload one validated snapshot entry. -/
inductive MemoSnapshotPreloadOutcome where
  /-- The snapshot decoded and was loaded as a `const` node. -/
  | loaded
  /-- The memo table already had a live entry for this key. -/
  | alreadyPresent
  /-- The snapshot store had no entry for this key. -/
  | missing
  /-- The snapshot metadata failed validation. -/
  | rejected (reason : MemoSnapshotRejectionReason)
  /-- The snapshot payload could not be decoded. -/
  | decodeError (error : String)
deriving Repr, BEq

/-- Summary counters for bulk validated snapshot preload operations. -/
structure MemoSnapshotPreloadSummary where
  /-- Number of successfully loaded entries. -/
  loaded : Nat := 0
  /-- Number of keys skipped because the live table already had a value. -/
  alreadyPresent : Nat := 0
  /-- Number of keys missing from the snapshot store. -/
  missing : Nat := 0
  /-- Number of entries rejected by metadata validation. -/
  rejected : Nat := 0
  /-- Number of entries whose payload failed to decode. -/
  decodeError : Nat := 0
deriving Repr, BEq, Inhabited

namespace MemoSnapshotPreloadSummary

/-- Increment one summary counter for one preload outcome. -/
def record (summary : MemoSnapshotPreloadSummary)
    (outcome : MemoSnapshotPreloadOutcome) : MemoSnapshotPreloadSummary :=
  match outcome with
  | .loaded => { summary with loaded := summary.loaded + 1 }
  | .alreadyPresent => { summary with alreadyPresent := summary.alreadyPresent + 1 }
  | .missing => { summary with missing := summary.missing + 1 }
  | .rejected _ => { summary with rejected := summary.rejected + 1 }
  | .decodeError _ => { summary with decodeError := summary.decodeError + 1 }

end MemoSnapshotPreloadSummary

/--
Pluggable storage for serialized memo value snapshots.

Unlike `MemoStore`, this stores serialized stable values rather than live graph
nodes.
-/
structure MemoSnapshotStore (κ : Type) (σ : Type) where
  /-- Look up one serialized snapshot value by key. -/
  lookup : κ -> IO (Option σ)
  /-- Insert or replace one serialized snapshot value. -/
  insert : κ -> σ -> IO Unit
  /-- Remove one serialized snapshot value, returning whether it existed. -/
  erase : κ -> IO Bool
  /-- Remove all snapshot entries, returning the number removed. -/
  clear : IO Nat
  /-- Number of currently stored snapshot entries. -/
  size : IO Nat
  /-- Snapshot the current serialized entries. -/
  entries : IO (Array (κ × σ))

namespace MemoSnapshotStore

/-- In-memory `Std.HashMap` implementation of `MemoSnapshotStore`. -/
def hashMap [BEq κ] [Hashable κ] : IO (MemoSnapshotStore κ σ) := do
  let cache <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap κ σ)
  pure {
    lookup := fun key => do
      pure ((← cache.get).get? key),
    insert := fun key value =>
      cache.modify (fun current => current.insert key value),
    erase := fun key => do
      let current <- cache.get
      let existed := (current.get? key).isSome
      cache.set (current.erase key)
      pure existed,
    clear := do
      let current <- cache.get
      cache.set (Std.HashMap.emptyWithCapacity : Std.HashMap κ σ)
      pure current.size,
    size := do
      pure (← cache.get).size,
    entries := do
      pure (← cache.get).toList.toArray
  }

private def fileSnapshotSuffix : String := ".lcmemo"

private def hexCharOfNibble (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat ('0'.toNat + n)
  else
    Char.ofNat ('a'.toNat + (n - 10))

private def hexByte (byte : UInt8) : String :=
  let value := byte.toNat
  String.ofList [hexCharOfNibble (value / 16), hexCharOfNibble (value % 16)]

private def encodeKeyFileStem (key : String) : String :=
  key.toUTF8.foldl (init := "") (fun acc byte => acc ++ hexByte byte)

private def nibbleOfHexChar? (c : Char) : Option Nat :=
  let value := c.toNat
  if '0'.toNat <= value && value <= '9'.toNat then
    some (value - '0'.toNat)
  else if 'a'.toNat <= value && value <= 'f'.toNat then
    some (10 + (value - 'a'.toNat))
  else if 'A'.toNat <= value && value <= 'F'.toNat then
    some (10 + (value - 'A'.toNat))
  else
    none

private def decodeHexBytes? (encoded : String) : Option ByteArray :=
  let rec go (chars : List Char) (acc : ByteArray) : Option ByteArray :=
    match chars with
    | [] => some acc
    | high :: low :: rest =>
        match nibbleOfHexChar? high, nibbleOfHexChar? low with
        | some hi, some lo =>
            go rest (acc.push (UInt8.ofNat (hi * 16 + lo)))
        | _, _ => none
    | _ => none
  go encoded.toList ByteArray.empty

private def decodeKeyFileStem? (stem : String) : Option String := do
  let bytes <- decodeHexBytes? stem
  String.fromUTF8? bytes

private def snapshotFileNameForKey (key : String) : String :=
  encodeKeyFileStem key ++ fileSnapshotSuffix

private def snapshotPathForKey (root : System.FilePath) (key : String) : System.FilePath :=
  root / snapshotFileNameForKey key

private def keyFromSnapshotFileName? (fileName : String) : Option String := do
  let stem <- fileName.dropSuffix? fileSnapshotSuffix
  decodeKeyFileStem? stem.toString

private def serializeSnapshotValue (key value : String) : String :=
  Lean.Json.compress <| Lean.Json.mkObj [
    ("key", Lean.toJson key),
    ("value", Lean.toJson value)
  ]

private def parseSnapshotValue? (content : String) : Option (String × String) := do
  let root <-
    match Lean.Json.parse content with
    | .ok value => some value
    | .error _ => none
  let keyJson <-
    match root.getObjVal? "key" with
    | .ok value => some value
    | .error _ => none
  let valueJson <-
    match root.getObjVal? "value" with
    | .ok value => some value
    | .error _ => none
  let key <-
    match Lean.fromJson? keyJson with
    | .ok value => some (value : String)
    | .error _ => none
  let value <-
    match Lean.fromJson? valueJson with
    | .ok parsed => some (parsed : String)
    | .error _ => none
  pure (key, value)

private def readSnapshotValue? (path : System.FilePath) (expectedKey : String) : IO (Option String) := do
  let content? <-
    try
      pure (some (← IO.FS.readFile path))
    catch _ =>
      pure none
  match content? with
  | none => pure none
  | some content =>
      match parseSnapshotValue? content with
      | some (actualKey, value) =>
          if actualKey == expectedKey then
            pure (some value)
          else
            pure none
      | none =>
          pure none

private def snapshotFiles (root : System.FilePath) : IO (Array (String × System.FilePath)) := do
  if !(← root.pathExists) then
    pure #[]
  else
    let diskEntries <- root.readDir
    let mut files := #[]
    for entry in diskEntries do
      if ← entry.path.isDir then
        pure ()
      else
        match keyFromSnapshotFileName? entry.fileName with
        | some key =>
            files := files.push (key, entry.path)
        | none =>
            pure ()
    pure files

private partial def freshTempSnapshotPath
    (root : System.FilePath)
    (targetFileName : String)
    (pid : String)
    (counter : IO.Ref Nat) : IO System.FilePath := do
  let current <- counter.get
  counter.set (current + 1)
  let candidate := root / s!".{targetFileName}.tmp.{pid}.{current}"
  if ← candidate.pathExists then
    freshTempSnapshotPath root targetFileName pid counter
  else
    pure candidate

/--
File-backed reference implementation of `MemoSnapshotStore` for `String` keys
and `String` payloads.

Each key is stored in one file under `root`. Writes use a temp file in the same
directory followed by `rename` so updates are atomic when the filesystem
supports atomic renames.
-/
def fileBacked (root : System.FilePath) : IO (MemoSnapshotStore String String) := do
  IO.FS.createDirAll root
  let tempCounter <- IO.mkRef 0
  let pid := toString (← IO.Process.getPID)
  let loadEntries : IO (Array (String × String)) := do
    let files <- snapshotFiles root
    let mut loaded := #[]
    for file in files do
      match ← readSnapshotValue? file.2 file.1 with
      | some value =>
          loaded := loaded.push (file.1, value)
      | none =>
          pure ()
    pure loaded
  pure {
    lookup := fun key =>
      readSnapshotValue? (snapshotPathForKey root key) key,
    insert := fun key value => do
      IO.FS.createDirAll root
      let target := snapshotPathForKey root key
      let tempPath <- freshTempSnapshotPath root (snapshotFileNameForKey key) pid tempCounter
      let encoded := serializeSnapshotValue key value
      try
        IO.FS.writeFile tempPath encoded
        IO.FS.rename tempPath target
      catch error =>
        try
          IO.FS.removeFile tempPath
        catch _ =>
          pure ()
        throw error,
    erase := fun key => do
      let target := snapshotPathForKey root key
      if ← target.pathExists then
        IO.FS.removeFile target
        pure true
      else
        pure false,
    clear := do
      let files <- snapshotFiles root
      let mut removed := 0
      for file in files do
        if ← file.2.pathExists then
          IO.FS.removeFile file.2
          removed := removed + 1
        else
          pure ()
      pure removed,
    size := do
      pure (← loadEntries).size,
    entries :=
      loadEntries
  }

end MemoSnapshotStore

/--
A keyed cache of incremental nodes within one `State`.

Use `MemoTable` when repeated requests for the same key should reuse the same
incremental node.
-/
structure MemoTable (κ : Type) (α : Type) [BEq κ] [Hashable κ] where
  /-- State that owns every node stored in this table. -/
  state : State
  /-- Pluggable live key-to-node storage. -/
  store : MemoStore κ α
  /-- Per-entry lifecycle metadata kept in sync with the live store. -/
  metadataRef : IO.Ref (Std.HashMap κ MemoEntryMetadata)

namespace MemoTable

def ensureCanMutate [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Unit := do
  if <- State.amStabilizing table.state then
    Internal.throwUser "cannot mutate a memo table while stabilization is running"
  if <- State.hasPartialStabilization table.state then
    Internal.throwUser "cannot mutate a memo table while a budgeted stabilization is incomplete"

def ensureStableSnapshotReadable [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Unit := do
  if <- State.amStabilizing table.state then
    Internal.throwUser "cannot snapshot memo values while stabilization is running"
  if <- State.hasPartialStabilization table.state then
    Internal.throwUser "cannot snapshot memo values while a budgeted stabilization is incomplete"

private def rawLookup [BEq κ] [Hashable κ] (table : MemoTable κ α) (key : κ) : IO (Option (Incr α)) :=
  table.store.lookup key

private def installMetadata [BEq κ] [Hashable κ]
    (table : MemoTable κ α) (key : κ) (metadata : MemoEntryMetadata) : IO Unit :=
  table.metadataRef.modify (fun current => current.insert key metadata)

private def eraseMetadata [BEq κ] [Hashable κ] (table : MemoTable κ α) (key : κ) : IO Unit :=
  table.metadataRef.modify (fun current => current.erase key)

private def pruneMetadataToLiveEntries [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Unit := do
  let liveKeys := (← table.store.entries).map Prod.fst
  table.metadataRef.modify (fun current =>
    current.filter (fun key _metadata => memoContainsKey liveKeys key))

private def recordAccess [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (key : κ)
    (countAsHit : Bool) : IO Unit := do
  let accessEpoch <- State.currentStabilization table.state
  let current <- table.metadataRef.get
  let updated :=
    match current.get? key with
    | some metadata =>
        { metadata with
            accessCount := metadata.accessCount + 1
            hitCount := metadata.hitCount + if countAsHit then 1 else 0
            lastAccessedStabilization := some accessEpoch }
    | none =>
        { accessCount := 1
          hitCount := if countAsHit then 1 else 0
          lastAccessedStabilization := some accessEpoch
          pinned := false }
  table.metadataRef.set (current.insert key updated)

private def incPinNode (state : State) (nodeId : Nat) : IO Unit :=
  state.pinnedIdsRef.modify (fun m => m.insert nodeId ((m.getD nodeId 0) + 1))

private def decPinNode (state : State) (nodeId : Nat) : IO Unit :=
  state.pinnedIdsRef.modify (fun m =>
    let c := m.getD nodeId 0
    if c <= 1 then m.erase nodeId else m.insert nodeId (c - 1))

private def insertCreatedEntry [BEq κ] [Hashable κ]
    (table : MemoTable κ α) (key : κ) (node : Incr α) : IO Unit := do
  let accessEpoch <- State.currentStabilization table.state
  table.store.insert key node
  installMetadata table key {
    accessCount := 1
    hitCount := 0
    lastAccessedStabilization := some accessEpoch
    pinned := false
  }
  incPinNode table.state node.id

private def insertLoadedEntry [BEq κ] [Hashable κ]
    (table : MemoTable κ α) (key : κ) (node : Incr α) : IO Unit := do
  table.store.insert key node
  installMetadata table key {}
  incPinNode table.state node.id

private def preloadEnvelopeValue [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (codec : MemoValueCodec α σ)
    (policy : MemoSnapshotValidationPolicy)
    (key : κ)
    (envelope : MemoSnapshotEnvelope σ) : IO MemoSnapshotPreloadOutcome := do
  match MemoSnapshotValidationPolicy.validate policy envelope.metadata with
  | .error reason =>
      pure (.rejected reason)
  | .ok () =>
      match codec.decode envelope.payload with
      | .error error =>
          pure (.decodeError error)
      | .ok value =>
          let node <- const table.state value
          insertLoadedEntry table key node
          pure .loaded

/--
Create a memo table using the default in-memory `Std.HashMap` live store.

Cost: expected O(1).
Thread-safety: table creation is ordinary setup code; concurrent mutation of one
table is not documented as generally thread-safe.
-/
def create [BEq κ] [Hashable κ] (state : State) : IO (MemoTable κ α) := do
  let store <- MemoStore.hashMap (κ := κ) (α := α)
  let metadataRef <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap κ MemoEntryMetadata)
  pure { state := state, store := store, metadataRef := metadataRef }

/--
Create a memo table backed by a caller-supplied live store.

Cost: expected O(1) plus caller store creation cost.
-/
def createWithStore [BEq κ] [Hashable κ] (state : State) (store : MemoStore κ α) : IO (MemoTable κ α) :=
  do
    let metadataRef <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap κ MemoEntryMetadata)
    pure { state := state, store := store, metadataRef := metadataRef }

/--
Look up a cached incremental node by key.

This records a cache hit in the entry metadata when the key is present.

Cost: expected O(1) with the default hash-map store.
-/
def lookup [BEq κ] [Hashable κ] (table : MemoTable κ α) (key : κ) : IO (Option (Incr α)) := do
  match <- rawLookup table key with
  | some node =>
      recordAccess table key true
      pure (some node)
  | none =>
      pure none

/-- Return the current runtime metadata for `key`, if the entry exists. -/
def lookupMetadata [BEq κ] [Hashable κ]
    (table : MemoTable κ α) (key : κ) : IO (Option MemoEntryMetadata) := do
  let current <- table.metadataRef.get
  match current.get? key with
  | some metadata =>
      pure (some metadata)
  | none =>
      match <- rawLookup table key with
      | some _ => pure (some {})
      | none => pure none

/-- Update one metadata record in place, returning `false` when the key is absent. -/
def modifyMetadata [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (key : κ)
    (update : MemoEntryMetadata -> MemoEntryMetadata) : IO Bool := do
  let current <- table.metadataRef.get
  match current.get? key with
  | some metadata =>
      table.metadataRef.set (current.insert key (update metadata))
      pure true
  | none =>
      match <- rawLookup table key with
      | none => pure false
      | some _ =>
          table.metadataRef.set (current.insert key (update {}))
          pure true

/-- Mark a memo entry as pinned so retention policies do not evict it. -/
def pin [BEq κ] [Hashable κ] (table : MemoTable κ α) (key : κ) : IO Bool :=
  modifyMetadata table key (fun metadata => { metadata with pinned := true })

/-- Remove the pinned marker from a memo entry. -/
def unpin [BEq κ] [Hashable κ] (table : MemoTable κ α) (key : κ) : IO Bool :=
  modifyMetadata table key (fun metadata => { metadata with pinned := false })

/-- Return a snapshot of the current live memo entries. -/
def entries [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO (Array (κ × Incr α)) :=
  table.store.entries

/--
Return the cached node for `key`, or allocate it with `compute` and store it.

Repeated calls for the same key reuse the same node identity.

Use `MemoScope`, `invalidate`, or `sweepUnreachable` when you want finer control
over entry lifetime.

Cost: expected O(1) on a cache hit with the default store, plus `compute` on a
miss.
-/
def getOrCreate [BEq κ] [Hashable κ]
    (table : MemoTable κ α) (key : κ) (compute : κ -> IO (Incr α)) : IO (Incr α) := do
  match <- lookup table key with
  | some node => pure node
  | none =>
      let node <- compute key
      insertCreatedEntry table key node
      pure node

/--
Remove one key from the memo table.

Existing observers of the removed node keep working, but future lookups for the
same key will build or load a fresh node.

Cost: expected O(1) with the default store.
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def invalidate [BEq κ] [Hashable κ] (table : MemoTable κ α) (key : κ) : IO Bool := do
  ensureCanMutate table
  let nodeIdOpt := (← rawLookup table key).map (·.id)
  let removed <- table.store.erase key
  if removed then
    eraseMetadata table key
    if let some nodeId := nodeIdOpt then
      decPinNode table.state nodeId
  pure removed

/--
Remove every key that satisfies `predicate`, returning the number removed.

Cost: O(all memo entries).
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def invalidateMatching [BEq κ] [Hashable κ] (table : MemoTable κ α) (predicate : κ -> Bool) : IO Nat := do
  ensureCanMutate table
  let before <- table.store.entries
  let removed <- table.store.retain (fun key _node => !predicate key)
  pruneMetadataToLiveEntries table
  let after <- table.store.entries
  let afterIds := after.foldl (fun m (_, n) => m.insert n.id ()) (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
  for (_, node) in before do
    unless afterIds.contains node.id do
      decPinNode table.state node.id
  pure removed

/--
Remove all entries from the memo table, returning the number removed.

Cost: O(all memo entries).
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def clear [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Nat := do
  ensureCanMutate table
  let before <- table.store.entries
  let removed <- table.store.clear
  table.metadataRef.set (Std.HashMap.emptyWithCapacity : Std.HashMap κ MemoEntryMetadata)
  for (_, node) in before do
    decPinNode table.state node.id
  pure removed

/--
Keep only entries accepted by `predicate`, always preserving pinned entries, and
return the number removed.

Cost: O(all memo entries).
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def retainWithMetadata [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (predicate : κ -> Incr α -> MemoEntryMetadata -> Bool) : IO Nat := do
  ensureCanMutate table
  let before <- table.store.entries
  let currentMetadata <- table.metadataRef.get
  let removed <- table.store.retain (fun key node =>
    let metadata := match currentMetadata.get? key with
      | some metadata => metadata
      | none => {}
    metadata.pinned || predicate key node metadata)
  pruneMetadataToLiveEntries table
  let after <- table.store.entries
  let afterIds := after.foldl (fun m (_, n) => m.insert n.id ()) (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
  for (_, node) in before do
    unless afterIds.contains node.id do
      decPinNode table.state node.id
  pure removed

/--
Evict entries selected by a metadata-aware policy, except for pinned entries.

Cost: O(all memo entries).
-/
def evictByPolicy [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (policy : κ -> Incr α -> MemoEntryMetadata -> Bool) : IO Nat :=
  retainWithMetadata table (fun key node metadata => !policy key node metadata)

/--
Remove memoized entries whose nodes are no longer reachable from active
observers.

Cost: O(all memo entries + reachability traversal).
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def sweepUnreachable [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Nat := do
  ensureCanMutate table
  let before <- table.store.entries
  let reachable <- State.reachableNodeIds table.state
  let removed <- table.store.retain (fun _key node => Internal.containsNat reachable node.id)
  pruneMetadataToLiveEntries table
  let after <- table.store.entries
  let afterIds := after.foldl (fun m (_, n) => m.insert n.id ()) (Std.HashMap.emptyWithCapacity : Std.HashMap Nat Unit)
  for (_, node) in before do
    unless afterIds.contains node.id do
      decPinNode table.state node.id
  pure removed

/-- Return the number of entries currently cached in the memo table. Cost: expected O(1). -/
def size [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Nat :=
  table.store.size

/--
Persist one memoized stable value through a caller-supplied snapshot store.

This serializes the node's current stable value through `codec`. It does not try
to serialize the live `Incr α` graph node itself.

Cost: expected O(1) lookup plus encode cost and snapshot-store write cost.
Thread-safety: rejected while active or incomplete stabilization makes stable
snapshot reads unsafe.
-/
def persistStableValue [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (snapshotStore : MemoSnapshotStore κ σ)
    (codec : MemoValueCodec α σ)
    (key : κ) : IO Bool := do
  ensureStableSnapshotReadable table
  match <- rawLookup table key with
  | none => pure false
  | some node =>
      match <- Incr.value? node with
      | none => pure false
      | some value =>
          match codec.encode value with
          | .error error => Internal.throwUser s!"failed to encode memo value: {error}"
          | .ok encoded =>
              snapshotStore.insert key encoded
              pure true

/--
Persist every memo entry that currently has a stable value.

Cost: O(all memo entries) plus encode and snapshot-store write costs.
-/
def persistStableValues [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (snapshotStore : MemoSnapshotStore κ σ)
    (codec : MemoValueCodec α σ) : IO Nat := do
  ensureStableSnapshotReadable table
  let currentEntries <- entries table
  let mut saved := 0
  for entry in currentEntries do
    match <- Incr.value? entry.2 with
    | none => pure ()
    | some value =>
        match codec.encode value with
        | .error error => Internal.throwUser s!"failed to encode memo value: {error}"
        | .ok encoded =>
            snapshotStore.insert entry.1 encoded
            saved := saved + 1
  pure saved

/--
Persist one memoized stable value into an envelope snapshot store with caller
metadata.

Cost: expected O(1) lookup plus encode and snapshot-store write costs.
-/
def persistStableValueEnvelope [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (snapshotStore : MemoSnapshotStore κ (MemoSnapshotEnvelope σ))
    (codec : MemoValueCodec α σ)
    (metadata : MemoSnapshotEnvelopeMetadata)
    (key : κ) : IO Bool := do
  ensureStableSnapshotReadable table
  match <- lookup table key with
  | none => pure false
  | some node =>
      match <- Incr.value? node with
      | none => pure false
      | some value =>
          match codec.encode value with
          | .error error => Internal.throwUser s!"failed to encode memo value: {error}"
          | .ok encoded =>
              snapshotStore.insert key { metadata := metadata, payload := encoded }
              pure true

/--
Persist every stable memo entry into an envelope snapshot store.

Cost: O(all memo entries) plus encode and snapshot-store write costs.
-/
def persistStableValuesEnvelope [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (snapshotStore : MemoSnapshotStore κ (MemoSnapshotEnvelope σ))
    (codec : MemoValueCodec α σ)
    (metadataFor : κ -> α -> MemoSnapshotEnvelopeMetadata) : IO Nat := do
  ensureStableSnapshotReadable table
  let currentEntries <- entries table
  let mut saved := 0
  for entry in currentEntries do
    match <- Incr.value? entry.2 with
    | none => pure ()
    | some value =>
        match codec.encode value with
        | .error error => Internal.throwUser s!"failed to encode memo value: {error}"
        | .ok encoded =>
            snapshotStore.insert entry.1 {
              metadata := metadataFor entry.1 value,
              payload := encoded
            }
            saved := saved + 1
  pure saved

/--
Load one serialized snapshot value into the memo table as a `const` node.

This restores only the stable value snapshot. It does not recreate the original
computation graph, so callers should invalidate or replace these entries when
new source-of-truth inputs become dirty.

Cost: expected O(1) lookup plus decode cost on a hit.
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def preloadConstValue [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (snapshotStore : MemoSnapshotStore κ σ)
    (codec : MemoValueCodec α σ)
    (key : κ) : IO Bool := do
  ensureCanMutate table
  match <- rawLookup table key with
  | some _ => pure false
  | none =>
      match <- snapshotStore.lookup key with
      | none => pure false
      | some encoded =>
          match codec.decode encoded with
          | .error error => Internal.throwUser s!"failed to decode memo value: {error}"
          | .ok value =>
              let node <- const table.state value
              insertLoadedEntry table key node
              pure true

/--
Load every serialized snapshot entry into the memo table as a `const` node when
the key is currently missing.

Cost: O(all snapshot entries) plus decode costs.
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def preloadConstValues [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (snapshotStore : MemoSnapshotStore κ σ)
    (codec : MemoValueCodec α σ) : IO Nat := do
  ensureCanMutate table
  let snapshotEntries <- snapshotStore.entries
  let mut loaded := 0
  for entry in snapshotEntries do
    if (← rawLookup table entry.1).isSome then
      pure ()
    else
      match codec.decode entry.2 with
      | .error error => Internal.throwUser s!"failed to decode memo value: {error}"
      | .ok value =>
          let node <- const table.state value
          insertLoadedEntry table entry.1 node
          loaded := loaded + 1
  pure loaded

/--
Load one envelope snapshot value into the memo table as a `const` node when the
key is absent and the metadata passes validation.

Cost: expected O(1) lookup plus validation and decode costs on a hit.
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def preloadConstValueValidated [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (snapshotStore : MemoSnapshotStore κ (MemoSnapshotEnvelope σ))
    (codec : MemoValueCodec α σ)
    (policy : MemoSnapshotValidationPolicy)
    (key : κ) : IO MemoSnapshotPreloadOutcome := do
  ensureCanMutate table
  match <- rawLookup table key with
  | some _ =>
      pure .alreadyPresent
  | none =>
      match <- snapshotStore.lookup key with
      | none =>
          pure .missing
      | some envelope =>
          preloadEnvelopeValue table codec policy key envelope

/--
Load every envelope snapshot entry into the memo table as a `const` node when
missing and validation succeeds, returning counters by outcome class.

Cost: O(all snapshot entries) plus validation and decode costs.
Thread-safety: mutation is rejected during active or incomplete stabilization.
-/
def preloadConstValuesValidated [BEq κ] [Hashable κ]
    (table : MemoTable κ α)
    (snapshotStore : MemoSnapshotStore κ (MemoSnapshotEnvelope σ))
    (codec : MemoValueCodec α σ)
    (policy : MemoSnapshotValidationPolicy) : IO MemoSnapshotPreloadSummary := do
  ensureCanMutate table
  let snapshotEntries <- snapshotStore.entries
  let mut summary : MemoSnapshotPreloadSummary := {}
  for entry in snapshotEntries do
    let outcome <-
      match <- rawLookup table entry.1 with
      | some _ =>
          pure .alreadyPresent
      | none =>
          preloadEnvelopeValue table codec policy entry.1 entry.2
    summary := MemoSnapshotPreloadSummary.record summary outcome
  pure summary

end MemoTable

/--
A request-local or owner-local view of a shared memo table.

`MemoScope` records which keys were touched through the scope so they can be
cleared together later.
-/
structure MemoScope (κ : Type) (α : Type) [BEq κ] [Hashable κ] where
  /-- Shared table that stores the actual cached nodes. -/
  table : MemoTable κ α
  /-- Keys touched through this scope. -/
  keys : IO.Ref (Array κ)

namespace MemoScope

/-- Create an empty scope over an existing memo table. Cost: O(1). -/
def create [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO (MemoScope κ α) := do
  let keys <- IO.mkRef #[]
  pure { table := table, keys := keys }

/-- Return the keys currently tracked by this scope. Cost: O(1). -/
def ownedKeys [BEq κ] [Hashable κ] (scope : MemoScope κ α) : IO (Array κ) :=
  scope.keys.get

/--
Get or create a memoized node and record the key in this scope.

Cost: `MemoTable.getOrCreate` plus O(scope keys) duplicate-check cost in the
current implementation.
-/
def getOrCreate [BEq κ] [Hashable κ]
    (scope : MemoScope κ α) (key : κ) (compute : κ -> IO (Incr α)) : IO (Incr α) := do
  let node <- MemoTable.getOrCreate scope.table key compute
  scope.keys.modify (fun keys => if memoContainsKey keys key then keys else keys.push key)
  pure node

/--
Remove all keys touched through this scope from the underlying table.

Cost: O(scope keys), plus the cost of invalidating each touched key.
-/
def clear [BEq κ] [Hashable κ] (scope : MemoScope κ α) : IO Nat := do
  let keys <- scope.keys.get
  let mut removed := 0
  for key in keys do
    if <- MemoTable.invalidate scope.table key then
      removed := removed + 1
  scope.keys.set #[]
  pure removed

end MemoScope
end Leancremental
