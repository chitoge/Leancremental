# Query-Style Workloads

This document collects the query-oriented parts of Leancremental: reusable query nodes, request-scoped invalidation, stale-value fallbacks, budgeted stabilization, keyed aggregates, result-as-data composition, and document freshness checks.

The executable snippets below are mirrored in [Tests/QueriesExamples.lean](Tests/QueriesExamples.lean), and the test executable runs them through `Leancremental.Tests.QueriesExamples.runAll`.

`TUTORIAL.md` covers the core runtime loop. This document starts where the tutorial stops: workloads where node identity, request freshness, and incremental reuse matter as much as raw recomputation.

## Reusing Query Nodes

For compiler and LSP-style workloads, the important operation is not just
building a graph. It is reusing the same graph node for the same query key. A
`MemoTable` provides that first layer of query identity.

`MemoTable` works like:

- a map from keys to reusable graph nodes

Without it, repeatedly asking for "parse this file" may build duplicate work.
With it, the same key reuses the same node.

```lean
def memoTableExample : IO (Nat × Nat × Nat) := do
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
  let observer <- observe second
  State.stabilize state
  pure (← Observer.value! observer, ← computeCount.get, first.id)
```

The second lookup returns the already-created node, so the alternative
computation is not run. This is the shape you want for queries such as parsing a
file, resolving a declaration name, or computing diagnostics for a stable key.

Memo tables also support explicit invalidation. A `MemoScope` records the keys
touched by one request or owner, then removes those entries from the shared table
when the request ends. Existing observers of removed nodes keep working, but
future lookups allocate fresh nodes.

```lean
def memoScopeExample : IO (Nat × Nat) := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _shared <- MemoTable.getOrCreate table "file:shared" (fun _ => const state 1)
  let scope <- MemoScope.create table
  let _hover <- MemoScope.getOrCreate scope "request:hover" (fun _ => const state 2)
  let _diagnostics <- MemoScope.getOrCreate scope "request:diagnostics" (fun _ => const state 3)
  let removed <- MemoScope.clear scope
  pure (removed, ← MemoTable.size table)
```

Editor clients often prefer a stale answer over no answer while newer edits are
pending. `Incr.staleValue?` makes that fallback explicit.

```lean
def staleValueExample : IO (Option Nat × Nat) := do
  let state <- State.create
  let input <- Var.create state 1
  let result <- map (Var.watch input) (fun value => value + 1)
  let observer <- observe result
  State.stabilize state
  Var.set input 10
  let stale <- Incr.staleValue? result
  State.stabilize state
  pure (stale, ← Observer.value! observer)
```

`State.stabilizeWithStats` keeps the existing full-stabilization behavior but
also reports the stabilization number, node-touch count, changed-node count,
active observer count, and remaining recompute entries.

```lean
def stabilizeStatsExample : IO (Nat × Nat × Nat) := do
  let state <- State.create
  let input <- Var.create state 1
  let result <- map (Var.watch input) (fun value => value + 1)
  let _observer <- observe result
  let stats <- State.stabilizeWithStats state
  pure (stats.stabilization, stats.nodesStabilized, stats.activeObservers)
```

For latency-sensitive clients, `State.stabilizeWithBudget` runs a bounded number
of recompute roots and pauses between roots. Incomplete slices do not refresh
observers; a later slice resumes the same stabilization number, which is
important for dynamic `bind` graphs. If a newer edit should abandon pending
work, call `State.cancelStabilization` before applying that edit.

```lean
def budgetedStabilizationExample : IO Nat := do
  let state <- State.create
  let input <- Var.create state 1
  let plusOne <- map (Var.watch input) (fun value => value + 1)
  let doubled <- map plusOne (fun value => value * 2)
  let observer <- observe doubled
  let first <- State.stabilizeWithBudget state 1
  if first.completed then
    throw (IO.userError "budgeted stabilization completed too early")
  let _second <- State.stabilizeWithBudget state 1
  Observer.value! observer
```

Indexed aggregates provide a stable output node for keyed collections such as
diagnostics, symbols, or semantic tokens. The current implementation refolds the
whole keyed set when a member changes, but membership updates preserve the same
aggregate node.

```lean
def indexedAggregateExample : IO Nat := do
  let state <- State.create
  let first <- Var.create state 1
  let second <- Var.create state 2
  let aggregate <- IndexedAggregate.create (κ := String) state 0 (fun acc _key value => acc + value)
  IndexedAggregate.insertOrReplace aggregate "first" (Var.watch first)
  IndexedAggregate.insertOrReplace aggregate "second" (Var.watch second)
  let observer <- observe (IndexedAggregate.watch aggregate)
  State.stabilize state
  Var.set first 10
  State.stabilize state
  Observer.value! observer
```

Compiler failures are normal query results, not necessarily `IO` failures.
`IncrResult` is a small layer over `Incr (Except ε α)` with `map`, `map2`,
`bind`, `recover`, and projection helpers.

```lean
def resultExample : IO (Except String Nat) := do
  let state <- State.create
  let parsed <- IncrResult.ok (ε := String) state 2
  let checked <- IncrResult.bind parsed (fun value => IncrResult.ok (ε := String) state (value + 3))
  let observer <- observe checked
  State.stabilize state
  Observer.value! observer
```

`Document` provides a lightweight version layer for LSP-style clients. Document
content and the document version are ordinary incremental variables. There are
two related APIs here:

- `Document.requireCurrent` checks whether a version-tagged value still matches
  the document's current version.
- `Document.requestToken` lets code outside the graph decide whether a response
  is still safe to publish after other edits have happened.

This is not persistent multi-version execution. It is a small correctness layer
for "was this result computed for the document version I still care about?".

```lean
def documentVersionExample : IO (Except String Nat) := do
  let state <- State.create
  let doc <- Document.create state 10
  let snapshot <- Document.snapshot doc
  let stale <- const state { version := snapshot.version, value := snapshot.content + 1 }
  let currentOnly <- Document.requireCurrent doc stale
  let observer <- observe currentOnly
  let _nextVersion <- Document.edit doc (fun value => value + 10)
  State.stabilize state
  Observer.value! observer
```

After the edit, the observer returns an error because the value was tagged with
the old version.

```lean
def documentRequestTokenExample : IO Bool := do
  let state <- State.create
  let doc <- Document.create state 10
  let token <- Document.requestToken doc 7
  let _nextVersion <- Document.edit doc (fun value => value + 10)
  Document.requestIsCurrent doc token
```

This second example is the usual "drop the stale reply" check in an editor or
language server.

### Per-Key Query Inputs

The `build` field of `QueryRules` lets a rule reach other queries via
`QueryM.require` and arbitrary nodes via `QueryM.ofIncr`. The trickier case is
a rule that needs a *per-key input* — for example, the parsed text of a document
identified by the query key.

The idiomatic pattern is to keep the per-key inputs in a `MemoTable` (or a plain
`IO.Ref (HashMap κ (Var α))`) outside the `QueryTable`, then close over a
reference to that registry. When the rule body only performs `IO` work and
returns an `Incr` node, wrap it with `QueryM.ofIO`:

```lean
-- Registry of per-document source vars, managed by the editor layer.
let sourceVars : IO.Ref (HashMap String (Var String)) <- IO.mkRef {}

let rules : QueryRules String String := {
  build := fun key => QueryM.ofIO do
    -- Look up (or lazily create) the Var that holds this document's source text.
    let vars <- sourceVars.get
    let sourceVar <- match vars[key]? with
      | some v => pure v
      | none   =>
          -- First time we see this key; create a Var and register it.
          let v <- Var.create state ""
          sourceVars.modify (fun m => m.insert key v)
          pure v
    -- Return the incremental computation built from the live Var.
    map (Var.watch sourceVar) parseSource
}
```

Two pitfalls to avoid:

1. **Capturing a snapshot instead of the ref.** If you write
   `let vars <- sourceVars.get` *outside* the rule builder and close over the
   resulting `HashMap`, later insertions into `sourceVars` are invisible to the
   rule. Always close over the `IO.Ref` itself and call `.get` inside the rule.

2. **Creating a new `Var` on every rule invocation.** The guard on `vars[key]?`
   above ensures the `Var` is created once per key and reused. Without it, every
   stabilization that reactivates the rule would produce a fresh disconnected node.

### Multiple Query Families

`QueryTable κ α` forces a single value type `α` for all keys. When a single
`State` needs to serve multiple query families — for example parse results
(`ParseResult`), type-check results (`CheckResult`), and diagnostics
(`Diagnostics`) — there are two shapes:

**One table per family (recommended for most cases):**

```lean
let parseTable  <- QueryTable.create parseRules  state
let checkTable  <- QueryTable.create checkRules  state
let diagTable   <- QueryTable.create diagRules   state
```

Multiple tables on the same `State` are fully independent. There are no
interaction hazards with stabilization, pinning, or `reclaimUnreachableNodes`:
those operations act on `State`, and each table's nodes are ordinary `State`
nodes. The only shared resource is the `State` mutex during stabilization, which
serializes all graph updates regardless of which table they come from.

Choose this shape when the result types are unrelated or when you want separate
`MemoScope` granularity for each family.

**Sum type on one table (useful for uniform dispatch):**

```lean
inductive QueryValue where
  | parse (r : ParseResult)
  | check (r : CheckResult)
  | diag  (r : Diagnostics)

let table <- QueryTable.create combinedRules state
```

Partial projections (`match result with | .parse r => ... | _ => throw ...`)
at call sites are the cost. Choose this shape when all families share the same
key type and you need to enumerate or fan out over all results for a key in a
single pass.

Neither shape has interaction hazards with `reclaimUnreachableNodes`. The
operation scans the reachability closure from live observers — which table a
node came from is irrelevant.
