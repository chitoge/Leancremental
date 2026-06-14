# Parallel Stabilization

This document covers one specific feature: running eligible node recomputation
in parallel during a single `State.stabilize` pass.

It is not part of the default runtime path. If code always calls
`State.stabilize state` without `parallel := true`, this page is optional.

The executable snippets here are mirrored in
[Tests/ConcurrencyExamples.lean](Tests/ConcurrencyExamples.lean).

## What It Does

By default, `State.stabilize` runs sequentially.

```lean
State.stabilize state
```

Parallel mode opts in to concurrent recomputation for eligible nodes:

```lean
State.stabilize state true
```

The feature is about work **inside one stabilization pass**. It does not change
the external API shape or the fact that one `State` remains one locked mutable
runtime.

## When It Helps

Parallel stabilization is most useful when:

- many independent derived nodes become stale at once
- those recomputations are large enough to outweigh task overhead
- the program already runs with more than one Lean worker thread

It helps less when:

- the graph is mostly one dependency chain
- most stale work sits behind `bind` or `freeze`
- recomputations are tiny

## Scheduling Model

The runtime assigns each node a height.
A node's height is greater than the height of its children.

Practical consequence:

- nodes at the same height do not depend on each other
- the runtime can process one height level and then move upward

That is the basic scheduling idea behind parallel stabilization.
It is an internal detail, but it explains why some work can run together safely.

## What Can Run In Parallel

These node kinds can run in parallel when they are at the same height:

- `const`
- `var`
- `map`, `map2`, `map3`, `map4`, `map5`
- `arrayFold`

These stay sequential:

- `bind`
- `freeze`
- `Expert.Node`

Reason:

- `map`-style nodes read inputs and compute a value
- `bind` and `freeze` can rewire graph structure
- `Expert.Node` runs arbitrary user `IO`

## User-Facing Rules

### Ordinary `map`-style code is the expected case

The functions passed to `map`, `map2`, and related combinators are pure
functions. That is the normal case for parallel mode.

```lean
let doubled <- map (Var.watch x) (fun n => n * 2)
let tripled <- map (Var.watch x) (fun n => n * 3)
let squared <- map (Var.watch x) (fun n => n * n)
State.stabilize state true
```

### `Expert.Node` remains a special case

`Expert.Node` does not enter the parallel tier.
It still runs sequentially.

The usual expert-node cautions still apply:

- do not call `State.stabilize` inside expert recomputation
- do not call `Var.set` inside expert recomputation
- synchronize any shared mutable state that your own code manages across threads

## What Parallel Mode Does Not Change

Parallel mode does not remove the global write lock.
The externally visible behavior is still:

- one `State.stabilize` call produces one completed pass
- observer callbacks run after recomputation finishes
- concurrent mutation and stabilization on the same `State` are still serialized

## Related Docs

- [README.md](README.md)
- [CONCEPTS.md](CONCEPTS.md)
- [FEDERATION.md](FEDERATION.md)
