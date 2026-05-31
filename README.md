# Leancremental

Leancremental is a Lean 4 library for building self-adjusting computations. It is
inspired by [Jane Street's OCaml `incremental` library](https://github.com/janestreet/incremental): you build a graph of
values, update mutable inputs, then explicitly stabilize the graph to refresh the
observed results.

Use it when you have derived values that should be recomputed only when their
inputs change. The intended long-term use case is query-style tooling: parsers,
interpreters, compilers, diagnostics, semantic tokens, and LSP requests that need
to react quickly to edits.

For a longer walkthrough and an OCaml Incremental parity checklist, see
[TUTORIAL.md](TUTORIAL.md).

Lean API documentation is published from CI to
[GitHub Pages](https://chitoge.github.io/Leancremental/).

## Status

This is an experimental Lean implementation, but it is already usable for small
incremental graphs and query-engine prototypes. The runtime supports variables,
observers, cutoffs, dynamic dependencies, query memoization, budgeted
stabilization, graph debugging, clocks, expert nodes, and a proof-oriented pure
model.

The proof layer is intentionally honest about its current boundary. Leancremental
has executable invariant checkers and several Lean theorems about pure models,
metadata shapes, graph invariants, cutoffs, and query helpers. It does not yet
contain a static theorem that the mutable `IO.Ref` runtime always implements the
pure semantics after stabilization.

## Quick Start

```lean
import Leancremental

open Leancremental

def example : IO Nat := do
  let state <- State.create

  let x <- Var.create state 13
  let y <- Var.create state 17
  let z <- map2 (Var.watch x) (Var.watch y) (fun x y => x + y)

  let observer <- observe z
  State.stabilize state

  Var.set x 19
  State.stabilize state

  Observer.value! observer
```

The final value is `36`. The important points are:

- `State.create` creates an incremental graph.
- `Var.create` creates mutable inputs owned by that graph.
- `Var.watch` turns a variable into an incremental value.
- `map2` builds a derived value.
- `observe` makes a value necessary.
- `State.stabilize` recomputes necessary stale values.
- `Observer.value!` reads the latest stabilized result.

## Mental Model

A Leancremental program has three phases.

1. Build a graph of `Incr α` values from variables and combinators.
2. Change inputs with `Var.set` or `Var.replace`.
3. Call `State.stabilize` to propagate changes to active observers.

Only observed values are necessary. Necessary nodes keep their dependencies live,
and stale necessary nodes are scheduled through a height-ordered recompute queue.
That mirrors the central discipline of OCaml Incremental: dependencies should be
stable before their parents recompute.

The API lives in `IO`. OCaml Incremental hides graph mutation behind a functorized
interface; Leancremental keeps mutation explicit because the runtime stores graph
state in `IO.Ref`s.

## Core Runtime

Importing `Leancremental` gives access to the main runtime API.

Basic graph construction:

- `State.create`
- `Var.create`, `Var.watch`, `Var.set`, `Var.replace`, `Var.value`
- `const`, `ret`
- `map`, `map2`, `map3`, `map4`, `map5`, `both`
- `arrayFold`, `all`, `forAll`, `existsAny`, `sum`, `sumNat`, `sumFloat`

Dynamic graph structure:

- `bind`, `join`, `ifThenElse`
- `dependOn`
- `freeze`, `freezeWhen`

Observation and propagation:

- `observe`
- `Observer.value?`, `Observer.value!`, `Observer.onUpdate`
- `Observer.disallowFutureUse`
- `State.stabilize`
- `State.stabilizeWithStats`
- `State.stabilizeWithBudget`, `State.cancelStabilization`
- `Incr.staleValue?`
- `Incr.onObservabilityChange`

Cutoffs:

```lean
Incr.setCutoff someNode Cutoff.ofEq
```

Leancremental uses `Cutoff.never` by default. Unlike OCaml Incremental, it does
not assume a uniform physical-equality cutoff for arbitrary Lean values. Use
`Cutoff.ofEq` or `Cutoff.ofDecidableEq` when equality-based propagation is what
you want.

## Query And LSP Support

The library includes a small set of APIs aimed at compiler and editor workloads.

- `MemoTable` reuses graph nodes for stable query keys.
- `MemoScope` tracks request- or owner-local memoized keys and can clear them.
- `Incr.staleValue?` reads the last cached value while edits are pending.
- `State.stabilizeWithStats` reports stabilization counts and touched nodes.
- `State.stabilizeWithBudget` lets clients split stabilization across latency
  budgets and resume later.
- `IndexedAggregate` keeps a stable keyed aggregate node for diagnostics,
  symbols, semantic tokens, and similar outputs.
- `IncrResult` keeps expected failures in the graph as `Except` values instead
  of throwing `IO` exceptions.
- `Document` tags query results with lightweight document versions and request
  tokens, so stale responses can be rejected before publishing.

These APIs are intentionally modest. They do not provide persistent multi-version
execution or graph garbage collection yet.

## Debugging And Invariants

The runtime exposes executable diagnostics:

- `State.toDot` and `State.saveDotToFile` export the graph.
- `State.detectCycle` reports cycle paths.
- `State.checkInvariants` checks basic graph metadata invariants.
- `State.checkStableInvariants` additionally checks post-stabilization
  invariants for necessary nodes.

The invariant checks cover facts represented by public `NodeInfo` snapshots:
parents and children agree, parent heights are greater than child heights,
necessary nodes are closed over dependencies, timestamps are ordered, and stable
necessary nodes are no longer stale.

## Clocks And Expert Nodes

`Clock` provides deterministic time-based incrementals over `Nat` time. Time only
changes when user code calls `Clock.advanceTo` or `Clock.advanceBy`, and those
changes propagate on the next stabilization.

`Expert.Node` is a low-level escape hatch for custom recomputation. Expert nodes
can have dynamic dependencies and dependency callbacks. Prefer ordinary typed
combinators unless you need custom incremental maintenance.

## Pure Model And Proofs

`Leancremental.Pure` is a total expression language for reasoning about the pure
subset of the API. It models constants, `map`, `map2`, folds, boolean folds,
`sumNat`, variables as explicit values, and snapshots whose stored value is
proved equal to the expression's evaluation.

`CoreSnapshot` is the bridge between the pure model and the executable runtime:

- `CoreSnapshot.compile` builds executable `const`, `map`, and `map2` graphs from
  a `Pure.Expr`.
- `CoreSnapshot.compileFoldArray` builds executable fold graphs from pure inputs.
- `CoreSnapshot.observeExpr` and `CoreSnapshot.observeFoldArray` compile and
  observe those graphs.
- `CoreSnapshot.observeExprChecked` and `CoreSnapshot.observeFoldArrayChecked`
  run the actual graph, stabilize it, and fail if the observed value does not
  match the pure model.
- `CoreSnapshot.certifyValue` and `CoreSnapshot.certifyFoldValue` turn a matching
  observed value into a proof-carrying `Pure.Snapshot`, assuming a lawful `BEq`.

`CoreSnapshot.stableValueSnapshot` is deliberately weaker: it wraps an already
read value in a trivial constant pure model. It does not prove that the value came
from any non-trivial computation graph.

`Leancremental.Proof` collects the current proof layer:

- cutoff simplification lemmas
- Prop-level graph invariant records over `NodeInfo`
- height-order facts and child-cycle exclusion
- pure expression height and node-count facts
- expected-value and certification lemmas for `CoreSnapshot`
- local metadata-constructor lemmas for leaf, unary, and binary nodes
- query-helper lemmas for memo key tracking, indexed aggregates, and
  `IncrResult.cutoffOfEq`

The next serious proof milestone is to lift the pure metadata preservation lemmas
to larger `IO` state transitions and eventually prove static correctness theorems
for stabilization itself.

## Project Layout

- [Leancremental.lean](Leancremental.lean) is the public umbrella import.
- [Leancremental/Core.lean](Leancremental/Core.lean) re-exports the runtime.
- [Leancremental/Pure.lean](Leancremental/Pure.lean) contains the total pure
  expression model.
- [Leancremental/Proof.lean](Leancremental/Proof.lean) re-exports proof modules.
- [Tests.lean](Tests.lean) is the executable test runner.
- [Tests/TutorialExamples.lean](Tests/TutorialExamples.lean) checks the tutorial
  snippets.

## Development

Build and test with:

```bash
lake build
lake exe tests
```

For a clean verification run:

```bash
lake clean
lake build
lake exe tests
```

## License

MIT License. See [LICENSE](LICENSE).
