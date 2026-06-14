# Parallel Stabilization

Leancremental can recompute independent graph nodes concurrently inside a single
stabilization pass.

Most users do not need this page. If you always call `State.stabilize state`
without `parallel := true`, you can skip it.

The executable snippets here are mirrored in
[Tests/ConcurrencyExamples.lean](Tests/ConcurrencyExamples.lean), and the test
executable runs them through
`Leancremental.Tests.ConcurrencyExamples.runAll`.

## Short Version

By default, `State.stabilize` runs sequentially.

If you call:

```lean
State.stabilize state true
```

Leancremental will try to recompute independent work in parallel inside that
single pass.

For ordinary use, the main rule is simple:

- pure `map`-style computations are fine in parallel mode
- `bind`, `freeze`, and `Expert.Node` still run sequentially

## When This Helps

Parallel stabilization helps when:

- many independent derived nodes become stale at once
- those nodes are expensive enough that parallel work outweighs task overhead
- you are already running Lean with more than one worker thread

It helps less when:

- the graph is mostly one long dependency chain
- most stale work sits behind `bind` or `freeze`
- each recomputation is tiny

## What The Runtime Uses To Do This Safely

The runtime assigns every node a **height**.
A node's height is greater than the height of its children.

Plain-language consequence:

- nodes at the same height do not depend on each other
- so the runtime can finish one height level, then move to the next

That is the whole idea behind parallel stabilization.
The runtime works level by level:

1. find the next height that has stale necessary nodes
2. run the parallel-safe nodes at that height together
3. finish the sequential-only nodes at that height
4. move upward

You do not need to manage those levels yourself.
They are internal scheduling details.

## What Runs In Parallel

These node kinds can run in parallel when they sit at the same height:

- `const`
- `var`
- `map`, `map2`, `map3`, `map4`, `map5`
- `arrayFold`

These stay sequential:

- `bind`
- `freeze`
- `Expert.Node`

Why:

- `map`-style nodes just read their inputs and compute a result
- `bind` and `freeze` can rewire graph structure
- `Expert.Node` runs arbitrary user `IO`

## What You Need To Remember As A User

### Pure `map`-style code is the normal safe case

The closures passed to `map`, `map2`, and related combinators are pure
functions. That is the normal case, and it is the easiest case for parallel
mode.

```lean
let doubled <- map (Var.watch x) (fun n => n * 2)
let tripled <- map (Var.watch x) (fun n => n * 3)
let squared <- map (Var.watch x) (fun n => n * n)
State.stabilize state true
```

### `Expert.Node` needs more care

`Expert.Node` is not part of the parallel tier.
It still runs sequentially.

That means parallel mode does **not** make `Expert.Node` compute functions race
with each other inside one stabilization pass.

The existing expert-node cautions still apply:

- do not call `State.stabilize` from inside expert recomputation
- do not call `Var.set` from inside expert recomputation
- if your own code shares mutable state across threads, synchronize it explicitly

## What Parallel Mode Does Not Change

Parallel stabilization does **not** remove the global write lock.

The user-visible behavior is still:

- one `State.stabilize` call produces one stable pass
- observer callbacks run after recomputation finishes
- concurrent `Var.set` and `State.stabilize` calls on the same `State` are still serialized

So this feature is **intra-pass parallelism**, not general shared-state
concurrency.

## Practical Advice

Use parallel mode when you have measured a real bottleneck and your stale work
contains many independent `map`-style nodes.

Stay with the default sequential mode when:

- you are still learning the library
- your workload is small
- most of the graph's cost comes from dynamic rewiring rather than wide parallel work

## Where To Read Next

- [README.md](README.md) for the main public overview
- [CONCEPTS.md](CONCEPTS.md) for the single-state runtime model
- [FEDERATION.md](FEDERATION.md) for coordination across multiple `State` instances
- [Leancremental/Core/State.lean](Leancremental/Core/State.lean) for the API details
