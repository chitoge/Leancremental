import Leancremental.Core.Types
import Leancremental.Core.State

/-!
Federation helpers for coordinating multiple independent incremental states.

Most users do not need this module. It matters when several agents or processes
each own their own local `State`, but still need to exchange published values or
track cross-agent progress.

The local incremental runtime stays unchanged: each agent still runs an ordinary
`State`. The federation layer adds coordination data around that local state,
including per-agent progress tracking and remote-input bookkeeping.
-/

namespace Leancremental

/--
A mutable input variable driven by cross-agent publication rather than
direct `Var.set` calls.

`sourceAgentId` identifies which agent publishes to this variable.
`key` is the channel name within that agent's publication stream.
-/
structure RemoteVar (α : Type) where
  /-- The local `Var` that mirrors the remote agent's published value. -/
  localVar : Var α
  /-- Identifier of the remote agent that publishes to this variable. -/
  sourceAgentId : String
  /-- Publication channel key within the remote agent's stream. -/
  key : String

/--
A federated state wraps one local `State` together with the metadata needed to
coordinate with other agents.

`n` is the number of agents in the cluster, and `agentSlot` says which slot in
the shared progress vector belongs to this agent.
-/
structure FederatedState (n : Nat) where
  /-- Human-readable identifier for this agent. -/
  agentId : String
  /-- The local incremental world (ordinary Nat-timestamped state). -/
  localState : State
  /-- This agent's index in the `n`-dimensional vector clock. -/
  agentSlot : Fin n
  /-- This agent's local progress frontier over `VecTimestamp n`. -/
  localFrontier : IO.Ref (Frontier (VecTimestamp n))
  /-- Registered remote subscription keys (sourceAgentId × channelKey). -/
  remoteKeys : IO.Ref (Array (String × String))

namespace FederatedState

/-- Create a new federated state with an empty local graph and zero recorded progress. -/
def create (agentId : String) (n : Nat) (agentSlot : Fin n) :
    IO (FederatedState n) := do
  let localState ← State.create
  let zeroFrontier : Frontier (VecTimestamp n) := { elements := #[fun _ => 0] }
  let localFrontier ← IO.mkRef zeroFrontier
  let remoteKeys ← IO.mkRef (Array.empty : Array (String × String))
  pure { agentId, localState, agentSlot, localFrontier, remoteKeys }

/-- Map one local stabilization number to a per-agent progress vector by placing
    `epoch` in this agent's slot and `0` in all other slots. -/
def epochToVec (n : Nat) (slot : Fin n) (epoch : Nat) : VecTimestamp n :=
  fun i => if i == slot then epoch else 0

/--
Advance the local progress record to a specific stabilization epoch.

Use this when you already have the stabilization number in hand, especially if
multiple threads may call `State.stabilize` on the same local state. Passing the
epoch explicitly avoids reading a newer epoch by mistake after the pass has finished.

```lean
-- Safe pattern: epoch is captured under the write lock by stabilizeWithStats
let stats ← State.stabilizeWithStats fs.localState
let fr ← fs.advanceFrontierAt stats.stabilization
```
-/
def advanceFrontierAt (fs : FederatedState n) (epoch : StabilizationId) :
    IO (Frontier (VecTimestamp n)) := do
  let epochVec := epochToVec n fs.agentSlot epoch
  let oldFrontier ← fs.localFrontier.get
  let newFrontier := Frontier.advance oldFrontier epochVec
  fs.localFrontier.set newFrontier
  pure newFrontier

/--
Advance the local progress record to include the most recent completed local pass.

This reads the current stabilization number from `localState`, converts it to
this agent's progress vector, and stores the result in `localFrontier`.

**Single-writer requirement**: `currentStabilization` is read after
`State.stabilize` releases its write lock.  If another thread calls
`State.stabilize` on the same `localState` and completes before this read,
the frontier advances to that thread's epoch rather than yours.
In single-agent usage this is harmless; if `localState` is shared across
threads, use `advanceFrontierAt` with `stats.stabilization` from
`State.stabilizeWithStats` for the race-free epoch.
-/
def advanceFrontier (fs : FederatedState n) : IO (Frontier (VecTimestamp n)) := do
  fs.advanceFrontierAt (← fs.localState.currentStabilization)

/--
Register a `RemoteVar` subscription channel.

Use this for bookkeeping when one agent mirrors values published by another.
The actual delivery still happens by updating `remoteVar.localVar` and then
running stabilization on the local state.
-/
def registerRemoteVar (fs : FederatedState n) (rv : RemoteVar α) : IO Unit :=
  fs.remoteKeys.modify (·.push (rv.sourceAgentId, rv.key))

/--
Construct one combined progress frontier from the latest known epoch of every agent.

The caller is responsible for gathering those per-agent epochs. This function
just packages them into one frontier value for coverage checks.
-/
def globalFrontier (n : Nat) (epochs : VecTimestamp n) : Frontier (VecTimestamp n) :=
  { elements := #[epochs] }

end FederatedState

end Leancremental
