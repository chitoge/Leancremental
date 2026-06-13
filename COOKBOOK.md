# Leancremental Cookbook

This file is a small collection of task-oriented examples.

Each example answers a concrete question like "how do I sum two changing
inputs?" without requiring you to read the whole tutorial first.

## 1. Sum Two Mutable Inputs

Problem:

- you have two changing numbers
- you want to read their sum after edits

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

Result:

- the final value is `35`

## 2. Read A Value Only After Stabilization

Problem:

- you changed an input
- you want to understand why the observer still shows the old value

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

Result:

- `before = 2`
- `after = 20`

Lesson:

- `Var.set` marks work stale
- `State.stabilize` performs the recomputation

## 3. Switch Between Two Branches

Problem:

- you want the result to follow one of two inputs depending on a boolean

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

Result:

- the final value is `100`

Lesson:

- `ifThenElse` is built on `bind`
- only the selected branch is necessary

## 4. Reuse Work For Repeated Query Keys

Problem:

- asking for the same query key repeatedly should reuse one graph node

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

Result:

- the final value is `(1, true)`

Lesson:

- the computation for `"file:A"` ran once
- the second call reused the same memoized node instead of building another one

## 5. Reject A Stale Document Result

Problem:

- you have a query result tied to one document version
- you want to refuse to use it after the document changes

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

Result:

- the final value is an error, because the value was tagged with the old
  document version

Lesson:

- `Document.requireCurrent` checks a version-tagged value against the current
  document version

If you want to suppress stale replies from outside the graph, use a request
token instead:

```lean
def staleRequestToken : IO Bool := do
  let state <- State.create
  let doc <- Document.create state 10
  let token <- Document.requestToken doc 7
  let _ <- Document.edit doc (fun n => n + 5)
  Document.requestIsCurrent doc token
```

Result:

- the final value is `false`

Lesson:

- `Document.requestToken` captures the version a client request started from
- `Document.requestIsCurrent` tells you whether it is still safe to publish the reply

## 6. Keep A Last Known Value While New Work Is Pending

Problem:

- you want to show the old answer while a newer stabilization has not run yet

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

Result:

- `oldValue = some 6`
- `newValue = 20`

Lesson:

- `Incr.staleValue?` reads the cached value even while the node is stale

## 7. Invalidate A Single Memo Key

Problem:

- one file changed and you want to force the next lookup to rebuild, without
  touching the rest of the table

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

Result:

- `sizeBefore = 2`
- `wasPresent = true`
- `sizeAfter = 1`

Lesson:

- `MemoTable.invalidate` removes one key and returns whether it existed
- existing observers of the removed node keep working; the next
  `getOrCreate` for that key will build a fresh node

## 8. Clear Request-Local Entries With MemoScope

Problem:

- one request finishes and you want to remove its memoized entries without
  touching entries that belong to other requests

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

Result:

- `before = 3`
- `removed = 2`
- `after = 1`

Lesson:

- `MemoScope.getOrCreate` adds the key to both the shared table and the
  scope's key list
- `MemoScope.clear` invalidates only the scope-tracked keys; the shared
  entry survives

## 9. Carry Memo Values Into A Fresh State With MemoValueCodec

Problem:

- you want to pass computed stable values from one `State` into a fresh one
  without rerunning the computation

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

Result:

- the final value is `some "hello"`

Lesson:

- `persistStableValues` reads the stable value of each memoized node and
  encodes it through the codec into the snapshot store
- `preloadConstValues` decodes those values and installs them as `const`
  nodes so the next `getOrCreate` returns the preloaded result instead of
  running the compute function again
- `MemoValueCodec.ofJson` handles the encode/decode step for any type with
  `ToJson` and `FromJson` instances; for file-backed persistence, swap
  `MemoSnapshotStore.hashMap` for `MemoSnapshotStore.fileBacked`

## When To Read The Tutorial

Use this cookbook when you want a quick pattern.

Use [TUTORIAL.md](TUTORIAL.md) when you want:

- the bigger mental model
- more explanation of `necessary`, `Cutoff`, and `bind`
- the advanced query and proof APIs
