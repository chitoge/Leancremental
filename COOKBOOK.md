# Cookbook

This file collects short task-oriented recipes.

Each recipe answers a concrete usage question without requiring the full
explanatory path of the tutorial.

## Recipe 1 — Sum Two Mutable Inputs

Use this when two mutable inputs feed one derived value.

```lean
import Leancremental

open Leancremental

def sumTwo : IO Nat := do
  let state <- State.create
  let x <- Var.create state 10
  let y <- Var.create state 20
  let sum <- map2 (Var.watch x) (Var.watch y) (fun a b => a + b)
  let observer <- observe sum

  State.stabilize state
  Var.set x 15
  State.stabilize state
  Observer.value! observer
```

Outcome: `35`

Key point: updates become visible after stabilization, not at `Var.set` time.

## Recipe 2 — Read Only After Stabilization

Use this when a direct input update has happened but observer output still looks
old.

```lean
def readAfterStabilize : IO (Nat × Nat) := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)
  let observer <- observe doubled

  State.stabilize state
  Var.set x 10
  let before <- Observer.value! observer
  State.stabilize state
  let after <- Observer.value! observer
  pure (before, after)
```

Outcome:

- `before = 2`
- `after = 20`

Key point: `Var.set` marks work stale; `State.stabilize` performs the refresh.

## Recipe 3 — Switch Between Two Branches

Use this when the active dependency should depend on a boolean or selector.

```lean
def switching : IO Nat := do
  let state <- State.create
  let chooseLeft <- Var.create state true
  let left <- Var.create state 7
  let right <- Var.create state 100

  let selected <- ifThenElse (Var.watch chooseLeft) (Var.watch left) (Var.watch right)
  let observer <- observe selected

  State.stabilize state
  Var.set chooseLeft false
  State.stabilize state
  Observer.value! observer
```

Outcome: `100`

Key point: `ifThenElse` is built on `bind`, so only the active branch stays
necessary.

## Recipe 4 — Reuse Work For Repeated Query Keys

Use this when repeated requests for the same key should reuse one node.

```lean
def memoizedQuery : IO (Nat × Bool) := do
  let state <- State.create
  let counter <- IO.mkRef 0
  let table <- MemoTable.create (κ := String) (α := Nat) state

  let first <- MemoTable.getOrCreate table "file:A" (fun _ => do
    counter.modify (fun n => n + 1)
    const state 42)

  let second <- MemoTable.getOrCreate table "file:A" (fun _ => do
    counter.modify (fun n => n + 1)
    const state 99)

  pure (← counter.get, first.id == second.id)
```

Outcome: `(1, true)`

Key point: `MemoTable.getOrCreate` reuses the existing node for the same key.

## Recipe 5 — Reject A Stale Document Result

Use this when a result is tied to one document version and must not be used
after the document changes.

```lean
def staleDocumentResult : IO (Except String Nat) := do
  let state <- State.create
  let doc <- Document.create state 10
  let snapshot <- Document.snapshot doc
  let stale <- const state { version := snapshot.version, value := snapshot.content + 1 }
  let currentOnly <- Document.requireCurrent doc stale
  let observer <- observe currentOnly

  let _ <- Document.edit doc (fun n => n + 5)
  State.stabilize state
  Observer.value! observer
```

Outcome: an error value

Key point: `Document.requireCurrent` checks a version-tagged value against the
current document version.

If code outside the graph needs to drop stale replies instead, use a request
token:

```lean
def staleRequestToken : IO Bool := do
  let state <- State.create
  let doc <- Document.create state 10
  let token <- Document.requestToken doc 7
  let _ <- Document.edit doc (fun n => n + 5)
  Document.requestIsCurrent doc token
```

Outcome: `false`

## Recipe 6 — Keep A Last Known Value While New Work Is Pending

Use this when an old cached answer is acceptable while a newer stabilization is
still pending.

```lean
def staleFallback : IO (Option Nat × Nat) := do
  let state <- State.create
  let x <- Var.create state 3
  let doubled <- map (Var.watch x) (fun n => n * 2)
  let observer <- observe doubled

  State.stabilize state
  Var.set x 10
  let oldValue <- Incr.staleValue? doubled
  State.stabilize state
  let newValue <- Observer.value! observer
  pure (oldValue, newValue)
```

Outcome:

- `oldValue = some 6`
- `newValue = 20`

Key point: `Incr.staleValue?` reads the cached value even while the node is stale.

## Recipe 7 — Invalidate One Memo Key

Use this when one key should rebuild on the next lookup without disturbing the
rest of the table.

```lean
def memoInvalidate : IO (Nat × Bool × Nat) := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _ <- MemoTable.getOrCreate table "file:A" (fun _ => const state 42)
  let _ <- MemoTable.getOrCreate table "file:B" (fun _ => const state 99)
  let sizeBefore <- MemoTable.size table
  let wasPresent <- MemoTable.invalidate table "file:A"
  let sizeAfter <- MemoTable.size table
  pure (sizeBefore, wasPresent, sizeAfter)
```

Outcome:

- `sizeBefore = 2`
- `wasPresent = true`
- `sizeAfter = 1`

Key point: invalidation removes one table entry; later lookups rebuild it.

## Recipe 8 — Clear Request-Local Entries With `MemoScope`

Use this when request-local memoized entries should be removed in one step.

```lean
def memoScopeClear : IO (Nat × Nat × Nat) := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _ <- MemoTable.getOrCreate table "shared:base" (fun _ => const state 0)
  let scope <- MemoScope.create table
  let _ <- MemoScope.getOrCreate scope "request:hover" (fun _ => const state 1)
  let _ <- MemoScope.getOrCreate scope "request:diagnostics" (fun _ => const state 2)
  let before <- MemoTable.size table
  let removed <- MemoScope.clear scope
  let after <- MemoTable.size table
  pure (before, removed, after)
```

Outcome:

- `before = 3`
- `removed = 2`
- `after = 1`

Key point: the shared entry survives; only the scope-tracked entries are cleared.

## Recipe 9 — Preload Memo Values Into A Fresh State

Use this when stable memoized values should be carried into a fresh `State`
without recomputing them.

```lean
def memoCodecRoundtrip : IO (Option String) := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := String) state
  let node <- MemoTable.getOrCreate table "file:A" (fun _ => const state "hello")
  let obs <- observe node
  State.stabilize state
  let _ <- Observer.value! obs

  let snapStore <- MemoSnapshotStore.hashMap (κ := String) (σ := String)
  let _ <- MemoTable.persistStableValues table snapStore MemoValueCodec.ofJson

  let state2 <- State.create
  let table2 <- MemoTable.create (κ := String) (α := String) state2
  let _ <- MemoTable.preloadConstValues table2 snapStore MemoValueCodec.ofJson

  let node2 <- MemoTable.getOrCreate table2 "file:A" (fun _ => const state2 "fallback")
  let obs2 <- observe node2
  State.stabilize state2
  Observer.value? obs2
```

Outcome: `some "hello"`

Key point: stable values can be persisted and reinstalled as preloaded `const`
nodes in a new state.

## Recipe 10 — Stop Unnecessary Propagation With A Cutoff

Use this when a derived node often recomputes to the same value.

```lean
def cutoffStop : IO (Nat × Nat) := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2) Cutoff.ofEq
  let obs <- observe doubled
  State.stabilize state
  let before <- Observer.value! obs
  Var.set x 1
  State.stabilize state
  let after <- Observer.value! obs
  pure (before, after)
```

Outcome: `(2, 2)`

Key point: `Cutoff.ofEq` stops the unchanged result from propagating again.

## Recipe 11 — Safe Federation Stabilize-And-Advance

Use this when a federated runtime must capture the stabilization number from one
pass and advance its frontier without racing another stabilization.

```lean
let stats ← State.stabilizeWithStats fs.localState
let newFrontier ← fs.advanceFrontierAt stats.stabilization
```

Key point: the stabilization number captured by `stabilizeWithStats` is safer
than reading the current epoch later with `advanceFrontier`.

## Related Docs

- Use [TUTORIAL.md](TUTORIAL.md) for the larger runtime model and longer explanations.
- Use [CONCURRENCY.md](CONCURRENCY.md) only when calling `State.stabilize` with `parallel := true`.
- Use [FEDERATION.md](FEDERATION.md) only when coordinating several independent `State` instances.
