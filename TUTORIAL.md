# A Leancremental Tutorial

Leancremental is a Lean 4 library for self-adjusting computations. It follows
the central shape of Jane Street's OCaml Incremental library: user code builds a
graph of derived values, changes enter through variables, and an explicit
stabilization step brings observed values up to date.

This tutorial is original Leancremental documentation, but it intentionally uses
the same sequence of ideas as OCaml Incremental's introductory material. That
makes it a useful feature check: if a concept appears below with a Lean API and a
working example, we have a corresponding implementation. If it appears in the
parity table as missing or partial, it is still future work.

The executable snippets below are mirrored in
[Tests/TutorialExamples.lean](Tests/TutorialExamples.lean), and the test
executable runs them through `Leancremental.Tests.TutorialExamples.runAll`.

## The Basic Loop

Every Leancremental graph lives in a `State`. OCaml Incremental usually creates a
fresh world by applying a generative functor. Leancremental makes the world an
explicit value because graph mutation lives in `IO`.

```lean
import Leancremental

open Leancremental

def prism : IO Float := do
  let state <- State.create

  let width <- Var.create state 3.0
  let depth <- Var.create state 5.0
  let height <- Var.create state 4.0

  let baseArea <- map2 (Var.watch width) (Var.watch depth) (fun w d => w * d)
  let volume <- map2 baseArea (Var.watch height) (fun area h => area * h)

  let volumeObserver <- observe volume
  State.stabilize state
  let first <- Observer.value! volumeObserver

  Var.set height 10.0
  let stillOld <- Observer.value! volumeObserver
  State.stabilize state
  let updated <- Observer.value! volumeObserver

  if first == 60.0 && stillOld == 60.0 then
    pure updated
  else
    throw (IO.userError "unexpected prism state")
```

The important rhythm is the same as OCaml Incremental:

- `Var.create` creates external inputs.
- `Var.watch` turns a variable into an incremental value.
- `map`, `map2`, and higher-arity maps through `map5` describe derived values.
- `observe` marks a value as necessary.
- `State.stabilize` propagates pending changes.
- `Observer.value!` reads a stable observed value.

Setting a variable does not immediately change observer values. It marks the
corresponding node stale, and the next stabilization recomputes the observed
part of the graph.

```lean
def higherArityExample : IO Nat := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let d <- Var.create state 4
  let e <- Var.create state 5
  let total <- map5 (Var.watch a) (Var.watch b) (Var.watch c) (Var.watch d) (Var.watch e)
    (fun a b c d e => a + b + c + d + e)
  let observer <- observe total
  State.stabilize state
  Observer.value! observer
```

## Necessary Nodes

Leancremental only computes values that are needed by an active observer. If a
node is not on a path to an observer, it can remain stale without affecting the
observable result.

```lean
def necessaryExample : IO (Bool × Bool) := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)

  let before <- Incr.isNecessary doubled
  let _observer <- observe doubled
  State.stabilize state
  let after <- Incr.isNecessary doubled

  pure (before, after)
```

This corresponds to OCaml Incremental's distinction between observed nodes and
necessary nodes. Leancremental also exposes `Incr.onObservabilityChange` so code
can watch transitions into and out of the necessary set.

```lean
def observabilityExample : IO (Array Bool) := do
  let state <- State.create
  let x <- Var.create state 1
  let events <- IO.mkRef #[]

  Incr.onObservabilityChange (Var.watch x) (fun necessary =>
    events.modify (fun xs => xs.push necessary))

  let observer <- observe (Var.watch x)
  State.stabilize state
  Observer.disallowFutureUse observer
  State.stabilize state

  events.get
```

## Cutoffs

A cutoff decides whether a recomputed value should propagate downstream. OCaml
Incremental defaults to physical equality. Leancremental defaults to
`Cutoff.never`, because Lean values do not have a uniform physical equality
operation. Use `Cutoff.ofEq` or `Cutoff.ofDecidableEq` when equality is the right
notion of unchanged.

```lean
def cutoffExample : IO Nat := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)
  Incr.setCutoff doubled Cutoff.ofEq

  let observer <- observe doubled
  State.stabilize state
  Var.set x 1
  State.stabilize state
  Observer.value! observer
```

The observer remains at `2`, and dependents of `doubled` do not fire merely
because `x` was set to the same effective value.

## Dynamic Graphs With Bind

`bind` is the feature that moves Incremental beyond a spreadsheet. The graph can
change shape as data changes. `ifThenElse` is implemented on top of `bind`: only
the selected branch is necessary.

```lean
def branchExample : IO Nat := do
  let state <- State.create
  let useLeft <- Var.create state true
  let left <- Var.create state 10
  let right <- Var.create state 100

  let selected <- ifThenElse (Var.watch useLeft) (Var.watch left) (Var.watch right)
  let observer <- observe selected
  State.stabilize state

  Var.set right 101
  State.stabilize state
  let unchanged <- Observer.value! observer

  Var.set useLeft false
  State.stabilize state
  let switched <- Observer.value! observer

  if unchanged == 10 then pure switched else throw (IO.userError "bad branch")
```

Before `useLeft` changes, updates to `right` do not affect `selected`, because
the right branch is not necessary. After the switch, the result follows `right`.

The same pattern supports dynamic configuration. Here is an average of a dynamic
prefix of an array of incremental inputs.

```lean
def averagePrefix (state : State) (values : Array (Incr Nat)) (length : Incr Nat) : IO (Incr Nat) :=
  bind length (fun n => do
    let count := Nat.min n values.size
    let selected := values.extract 0 count
    let total <- sumNat state selected
    map total (fun sum => if count == 0 then 0 else sum / count))
```

When `length` changes, the bind node rewires the dependencies to the selected
prefix. This is the same conceptual role that `bind` plays in OCaml
Incremental's dynamic examples.

`dependOn` is useful when one incremental should keep another incremental alive
without using its value.

```lean
def dependOnExample : IO (Nat × Bool) := do
  let state <- State.create
  let value <- Var.create state 10
  let dependency <- Var.create state 20
  let result <- dependOn (Var.watch value) (Var.watch dependency)
  let observer <- observe result
  State.stabilize state
  pure (← Observer.value! observer, ← Incr.isNecessary (Var.watch dependency))
```

`freeze` captures a value at the first stabilization where the frozen node is
computed. `freezeWhen` follows a source until a boolean trigger becomes true.

```lean
def freezeExample : IO Nat := do
  let state <- State.create
  let x <- Var.create state 1
  let frozen <- freeze (Var.watch x)
  let observer <- observe frozen
  State.stabilize state
  Var.set x 2
  State.stabilize state
  Observer.value! observer
```

## Folds And Sums

Leancremental currently has straightforward full-array folds:

```lean
def foldExample : IO Nat := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let total <- sumNat state #[Var.watch a, Var.watch b, Var.watch c]
  let observer <- observe total
  State.stabilize state
  Observer.value! observer
```

OCaml Incremental also has optimized balanced and unordered folds that can update
in time proportional to the number of changed inputs for some operations. Those
are not implemented yet in Leancremental; `arrayFold` recomputes the whole fold
when any input changes.

## Debugging The Graph

Leancremental exposes a small debugging API:

```lean
def dotExample : IO String := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- Var.create state 2
  let z <- map2 (Var.watch x) (Var.watch y) (fun x y => x + y)
  let _observer <- observe z
  State.stabilize state
  State.toDot state
```

`State.toDot` returns a Graphviz DOT graph. `State.detectCycle` and
`State.formatCycle` expose cycle diagnostics, and stabilization reports cycle
paths when it detects one.

The OCaml implementation comments also identify invariants that are useful for
proof work. Leancremental exposes the subset represented by the current runtime:
bidirectional parent/child metadata, height ordering, necessary-node closure,
timestamp ordering, recompute-heap sanity, and the post-stabilization fact that
necessary nodes are not stale and have cached values.

```lean
def invariantExample : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun n => n + 1)
  let _observer <- observe y
  State.stabilize state
  State.checkStableInvariants state
```

OCaml's bind-scope invariant is stronger than what Leancremental can currently
state: it relies on explicit scopes and an adjust-heights heap. That is the next
place to enrich the proof model if we want proofs about dynamic graphs to match
OCaml Incremental more closely.

## Clocks

OCaml Incremental includes a timing-wheel-backed clock. Leancremental has a
smaller deterministic clock over `Nat` time. Time advances only when user code
calls `Clock.advanceTo` or `Clock.advanceBy`, and observers see the change after
stabilization.

```lean
def clockExample : IO BeforeOrAfter := do
  let state <- State.create
  let clock <- Clock.create state 100
  let boundary <- Clock.atTime clock 105
  let observer <- observe boundary

  State.stabilize state
  Clock.advanceBy clock 5
  State.stabilize state
  Observer.value! observer
```

The implemented clock APIs are `watchNow`, `advanceTo`, `advanceBy`, `atTime`,
`after`, `atIntervals`, and `stepFunction`.

## Expert Nodes

Expert nodes are a low-level escape hatch. They are useful when a node wants to
manage dependencies directly or update internal state based on which dependency
changed. Ordinary code should prefer `map`, `map2`, `bind`, and folds.

```lean
def expertExample : IO Nat := do
  let state <- State.create
  let x <- Var.create state 3

  let dependency := Expert.Dependency.create (Var.watch x)
  let expert <- Expert.Node.create state (do
    let value <- Expert.Dependency.value dependency
    pure (value * 10))
  Expert.Node.addDependency expert dependency

  let observer <- observe (Expert.Node.watch expert)
  State.stabilize state
  Observer.value! observer
```

Leancremental's expert API covers creation, watching, dependency add/remove,
dependency `onChange` callbacks, `makeStale`, and `invalidate`. It does not yet
offer OCaml Incremental's one-step stabilization API.

## Pure Model For Proofs

The executable engine is `IO`-backed. For theorem work, `Leancremental.Pure`
provides a total expression language for stable snapshots of the pure subset.

```lean
def pureExample : Nat :=
  let x : Pure.Var Nat := { value := 2 }
  let y : Pure.Var Nat := { value := 3 }
  let expr := Pure.map2 (Pure.Var.watch x) (Pure.Var.watch y) (fun x y => x + y)
  Pure.eval expr
```

This model is not a replacement for the executable graph engine. It is a proof
surface for equations such as map composition, fold evaluation, and snapshot
soundness.

`Leancremental.Core` also imports a small bridge module. The strongest current
bridge is spec-first: write a `Pure.Expr`, prove facts about that expression, and
compile the same expression into executable nodes with `CoreSnapshot.observeExpr`.

```lean
def compiledPureExample : IO Nat := do
  let state <- State.create
  let expr := Pure.map2 (Pure.const 2) (Pure.const 3) (fun x y => x + y)
  let observer <- CoreSnapshot.observeExpr state expr
  State.stabilize state
  Observer.value! observer
```

That makes the proof describe the code by construction: the expression being
simplified by Lean is also the recipe used to allocate the runtime graph. For
hand-written `IO` graphs, the next proof layer should add explicit refinement
lemmas saying which `Pure.Expr` each graph implements.

Once an executable value has been observed and read from `IO`,
`CoreSnapshot.stableValueSnapshot` reflects that stable value into the pure
model.

```lean
def coreSnapshotExample : Nat :=
  (CoreSnapshot.stableValueSnapshot 5).value
```

Pure fold inputs can also drive an executable `arrayFold` node.

```lean
def compiledPureFoldExample : IO Nat := do
  let state <- State.create
  let exprs := #[Pure.const 1, Pure.const 2, Pure.const 3]
  let observer <- CoreSnapshot.observeFoldArray state exprs 0 (fun acc value => acc + value)
  State.stabilize state
  Observer.value! observer
```

## Query-Style Interpreters

For compiler and LSP-style workloads, the important operation is not just
building a graph. It is reusing the same graph node for the same query key. A
`MemoTable` provides that first layer of query identity.

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
content and the document version are ordinary incremental variables. Query
results can be tagged with the version used to compute them, and request tokens
can be checked before publishing a response. This is not persistent
multi-version execution, but it is enough to suppress stale responses in a
single graph.

```lean
def documentVersionExample : IO (Except String Nat) := do
  let state <- State.create
  let doc <- Document.create state 10
  let query <- map (Document.watchContent doc) (fun value => value + 1)
  let tagged <- Document.tag doc query
  let currentOnly <- Document.requireCurrent doc tagged
  let observer <- observe currentOnly
  State.stabilize state
  let _nextVersion <- Document.edit doc (fun value => value + 10)
  State.stabilize state
  Observer.value! observer
```

## Feature Parity Checklist

| OCaml Incremental concept | Leancremental status | Leancremental API | Notes |
| --- | --- | --- | --- |
| Independent incremental world | Implemented | `State.create` | Explicit value instead of a generative functor. |
| Constants | Implemented | `const`, `ret` | `ret` avoids Lean's `return` syntax keyword. |
| Mutable variables | Implemented | `Var.create`, `Var.watch`, `Var.set`, `Var.replace`, `Var.value` | `latest_value` semantics during stabilization are not separated yet. |
| Mapping | Partial | `map`, `map2`, `map3`, `map4`, `map5`, `both` | Higher arity `map6` through `map15` are not generated yet. |
| Binding and dynamic graphs | Implemented | `bind`, `join`, `ifThenElse` | Scope tracking and invalidation lists are simpler than OCaml's implementation. |
| Observers | Implemented | `observe`, `Observer.value`, `Observer.value!`, `Observer.onUpdate`, `Observer.disallowFutureUse` | No finalizer-based observer cleanup. |
| Necessary/unnecessary tracking | Implemented | `Incr.isNecessary`, `Incr.onObservabilityChange` | Callback shape is simpler than OCaml's node update state machine. |
| Explicit stabilization | Implemented | `State.stabilize`, `State.amStabilizing` | Uses a height-ordered queue plus dependency-first stabilization. |
| Cutoffs | Implemented | `Cutoff.never`, `Cutoff.always`, `Cutoff.ofEq`, `Cutoff.ofDecidableEq`, `Incr.setCutoff` | Default is `Cutoff.never`, not physical equality. |
| Array fold | Implemented | `arrayFold`, `all`, `forAll`, `existsAny`, `sumNat` | Full recompute fold only. |
| Balanced and unordered folds | Missing | None | Needed for OCaml-style optimized aggregate maintenance. |
| Numeric sums | Partial | `sum`, `sumNat`, `sumFloat` | Generic full-recompute sums exist; inverse-based sums and optional sums are missing. |
| Freeze and snapshot | Partial | `freeze`, `freezeWhen`, `CoreSnapshot.compile`, `CoreSnapshot.observeExpr`, `CoreSnapshot.observeFoldArray`, `CoreSnapshot.stableValueSnapshot` | Graph-level freeze exists; clock snapshot is still missing. |
| `depend_on` and `necessary_if_alive` | Partial | `dependOn` | `necessary_if_alive` is still missing. |
| Scope and memoization helpers | Missing | None | OCaml's `Scope`, `lazy_from_fun`, and memoization APIs are not modeled. |
| Graph export | Implemented | `State.toDot`, `State.saveDotToFile` | DOT output is intentionally compact. |
| Cycle diagnostics | Implemented | `State.detectCycle`, `State.checkAcyclic`, `State.formatCycle` | Stabilization errors include node paths. |
| Graph invariants | Partial | `CoreInvariant.infoInvariant`, `State.checkInvariants`, `State.checkStableInvariants`, `Proof.Invariant.GraphInvariant` | Covers edge symmetry, height, necessary closure, timestamps, heap sanity, stable necessary nodes, and a Prop-level no-cycle theorem; bind-scope and adjust-height invariants remain future work. |
| Pure shape proofs | Implemented | `Pure.Expr.height`, `Pure.Expr.nodeCount`, `Pure.Expr.foldHeight`, `CoreSnapshot.expectedValue_*` lemmas | Proof layer mirrors the constructors currently supported by `CoreSnapshot.compile` and the pure fold compiler. |
| Node debug values and stats | Partial | `State.nodeInfo`, `Incr.height`, `Incr.isStale` | Full stats counters and node value states are missing. |
| Clocks | Partial | `Clock.create`, `Clock.watchNow`, `Clock.advanceTo`, `Clock.advanceBy`, `Clock.atTime`, `Clock.after`, `Clock.atIntervals`, `Clock.stepFunction` | Deterministic `Nat` time, not timing-wheel `Time_ns`. |
| Expert nodes | Partial | `Expert.Dependency`, `Expert.Node` | Core dependency management exists; one-step stabilization is missing. |
| Pure proof model | Lean-specific addition | `Leancremental.Pure` | Not an OCaml feature; supports proof engineering around stable snapshots. |
| Query memoization | Lean-specific addition | `MemoTable`, `MemoScope`, `Incr.staleValue?`, `State.stabilizeWithStats`, `State.stabilizeWithBudget`, `State.cancelStabilization` | Supports query-style compiler and LSP workloads; graph-node garbage collection is still future work. |
| Indexed aggregates | Lean-specific addition | `IndexedAggregate` | Stable keyed aggregate nodes for editor outputs; full refold only for now. |
| Error-as-data queries | Lean-specific addition | `IncrResult` | Expected query failures compose as `Except` values instead of `IO` exceptions. |
| Document versions | Lean-specific addition | `Document` | Lightweight document version tagging and request freshness; not persistent multi-version execution. |

## What To Build Next

The tutorial examples exercise the core Incremental story, so the next work is
mostly about completing OCaml's more specialized APIs:

- Add clock `snapshot`.
- Add graph-node garbage collection for memo entries that have no live observers.
- Add balanced and unordered folds, then inverse-based `sum` variants.
- Add `necessary_if_alive` and richer observability controls.
- Add scope/memoization helpers for bind-heavy graph construction.
- Add stats counters and richer node-value inspection.
- Strengthen theorems relating the `IO` engine's stable snapshots to
  `Leancremental.Pure`.