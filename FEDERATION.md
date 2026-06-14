# Federation

Leancremental's federation layer is for programs that coordinate **multiple**
independent incremental worlds.

Most users do not need this page. If your program has one `State` inside one
process, you can skip it.

## What Problem It Solves

A normal Leancremental program has one `State` and one stabilization loop.
That is enough for:

- a single editor process
- one compiler server
- one analysis pipeline

Federation matters when you have several agents or processes that each own
**their own** `State`, but still need to exchange progress or published values.

Examples:

- one process parses files while another serves diagnostics
- several workers compute different parts of a build graph
- a distributed tool wants to know which edits every agent has already seen

## Core Terms

### `FederatedState n`

A `FederatedState n` wraps one ordinary local `State` together with metadata for
cross-agent coordination.

You can think of it as:

- one normal incremental graph
- plus an agent id
- plus a progress record that can be compared with other agents

### `RemoteVar α`

A `RemoteVar α` is a local `Var α` that is updated from another agent's
published values.

Use it when one process receives updates from another process and wants those
updates to enter the local incremental graph as ordinary inputs.

### `VecTimestamp n`

A `VecTimestamp n` is one progress counter per agent.

Plain-language picture:

- with one agent, a single number is enough
- with several agents, you need one number for each agent
- together, those numbers say how far each agent has progressed

### `Frontier`

A `Frontier` describes which timestamps are definitely complete.

If you do not already work with distributed systems terminology, the simplest
mental model is:

- a frontier is a summary of "everything up to here is done"

## Safe Local Pattern

If one thread owns the local `State`, this is usually enough:

```lean
State.stabilize fs.localState
let frontier <- fs.advanceFrontier
```

If multiple threads may call `State.stabilize` on the same `localState`, prefer
capturing the stabilization number inside the pass:

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

This example is mirrored in `Tests.FederationExamples.storySafeAdvanceSnippet`.

That avoids racing with a second stabilization that finishes before
`advanceFrontier` reads the current epoch.

## Main Pitfalls

### 1. Do Not Build a Global Frontier One Agent At A Time

For one agent, repeatedly advancing a frontier is fine.

For several agents, that can lose information when two agents have progressed in
incomparable ways. Use
[`FederatedState.globalFrontier`](https://chitoge.github.io/Leancremental/Leancremental/Core/Federation.html#Leancremental.FederatedState.globalFrontier)
to build the combined frontier from all agents' epochs at once.

### 2. Do Not Read The Local Epoch Too Late

[`FederatedState.advanceFrontier`](https://chitoge.github.io/Leancremental/Leancremental/Core/Federation.html#Leancremental.FederatedState.advanceFrontier)
reads the current stabilization number after the pass has finished.

That is fine in single-threaded ownership.
It is not the safest choice if another thread may stabilize the same local
state before you read that number.

In that case, use `advanceFrontierAt` with
`State.stabilizeWithStats`.

## What Federation Does Not Change

Federation does **not** merge several agents into one shared `State`.
Each agent still owns its own local incremental graph.

Federation only adds coordination around those separate graphs.

## Where To Read Next

- [CONCEPTS.md](CONCEPTS.md) for the core single-state runtime model
- [CONCURRENCY.md](CONCURRENCY.md) for parallel stabilization inside one `State`
- [COOKBOOK.md](COOKBOOK.md) for short recipes, including a federation recipe
- [Leancremental/Core/Federation.lean](Leancremental/Core/Federation.lean) for the API surface
