# Federation

This document covers the federation layer: coordination across several
independent incremental states.

It is not part of ordinary single-state use.
If a program has one `State` inside one process, this page is optional.

## What It Is For

A normal Leancremental runtime has one `State` and one stabilization loop.
That is enough for many programs.

Federation matters when several agents or processes each own their own `State`,
but still need to exchange values or track shared progress.

Examples:

- one process parses while another serves diagnostics
- several workers own different parts of a larger system
- a distributed tool needs to know which edits every agent has already seen

## Core Terms

### `FederatedState n`

A `FederatedState n` wraps one ordinary local `State` together with the extra
metadata needed for cross-agent coordination.

### `RemoteVar α`

A `RemoteVar α` is a local `Var α` whose values are driven by another agent's
published output.

### `VecTimestamp n`

A `VecTimestamp n` stores one progress counter per agent.

For one agent, one number is enough.
For several agents, one number per agent is needed.

### `Frontier`

A `Frontier` summarizes which timestamps are definitely complete.

## Safe Local Pattern

If one thread owns the local `State`, this is usually enough:

```lean
State.stabilize fs.localState
let frontier <- fs.advanceFrontier
```

If several threads may call `State.stabilize` on the same `localState`, capture
the stabilization number inside the pass:

```lean
def federationSafeAdvance : IO Bool := do
  let slot : Fin 2 := ⟨0, by omega⟩
  let fs <- FederatedState.create "agent-0" 2 slot
  let x <- Var.create fs.localState 10
  let doubled <- map (Var.watch x) (fun n => n * 2)
  let observer <- observe doubled

  let stats <- State.stabilizeWithStats fs.localState
  let frontier <- fs.advanceFrontierAt stats.stabilization
  let epochVec := FederatedState.epochToVec 2 slot stats.stabilization

  pure (frontier.covers epochVec && (← Observer.value! observer) == 20)
```

The same behavior is verified in `Tests.FederationExamples.storySafeAdvanceSnippet`.

## Main Pitfalls

### Building A Global Frontier One Agent At A Time

Repeatedly advancing a frontier is fine for one agent's own monotone progress.
It is not the right way to combine progress from several agents.

Use
[`FederatedState.globalFrontier`](https://chitoge.github.io/Leancremental/Leancremental/Core/Federation.html#Leancremental.FederatedState.globalFrontier)
when one frontier must reflect all agents at once.

### Reading The Local Epoch Too Late

[`FederatedState.advanceFrontier`](https://chitoge.github.io/Leancremental/Leancremental/Core/Federation.html#Leancremental.FederatedState.advanceFrontier)
reads the current stabilization number after the pass completes.

That is fine under single-threaded ownership.
If another thread may stabilize the same local state before that read happens,
prefer `advanceFrontierAt` together with `State.stabilizeWithStats`.

## What Federation Does Not Change

Federation does not merge several agents into one shared `State`.
Each agent still owns its own local incremental graph.

Federation adds coordination around those separate graphs.

## Related Docs

- [README.md](README.md)
- [CONCEPTS.md](CONCEPTS.md)
- [COOKBOOK.md](COOKBOOK.md)
- [CONCURRENCY.md](CONCURRENCY.md)
