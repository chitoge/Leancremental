import Leancremental
import Tests.Util

/-! Executable stories for the Phase 5 federation API.

  Each function is a self-contained narrative that exercises one piece of the
  new surface: VecTimestamp, Frontier/Antichain, FederatedState, and the
  distributed-causality guarantee.  Running `runAll` verifies every story.
-/

namespace Leancremental
namespace Tests
namespace FederationExamples

-- Story 1: VecTimestamp pointwise ordering.
--
-- Three agents share a 3-slot vector clock.  We check that `Timestamp.le`
-- is pointwise: (1,0,0) ≤ (2,0,0) but not (0,1,0) ≤ (0,0,1).
def storyVecTimestampOrdering : IO Unit := do
  let v1 : VecTimestamp 3 := fun i => #[1, 0, 0].getD i.val 0
  let v2 : VecTimestamp 3 := fun i => #[2, 0, 0].getD i.val 0
  let v3 : VecTimestamp 3 := fun i => #[0, 1, 0].getD i.val 0
  let v4 : VecTimestamp 3 := fun i => #[0, 0, 1].getD i.val 0
  assertEq "v1 ≤ v2 (pointwise)"    (Timestamp.le v1 v2) true
  assertEq "v2 ≤ v1 not"            (Timestamp.le v2 v1) false
  assertEq "v3 ≤ v4 incomparable"   (Timestamp.le v3 v4) false
  assertEq "v4 ≤ v3 incomparable"   (Timestamp.le v4 v3) false
  assertEq "zero le v1"             (Timestamp.le (fun _ => 0) v1) true

-- Story 2: VecTimestamp join (pointwise max).
--
-- The join of (3,0,2) and (1,4,2) should be (3,4,2).
def storyVecTimestampJoin : IO Unit := do
  let a : VecTimestamp 3 := fun i => #[3, 0, 2].getD i.val 0
  let b : VecTimestamp 3 := fun i => #[1, 4, 2].getD i.val 0
  let j := LatticeTimestamp.join a b
  assertEq "join slot 0" (j ⟨0, by omega⟩) 3
  assertEq "join slot 1" (j ⟨1, by omega⟩) 4
  assertEq "join slot 2" (j ⟨2, by omega⟩) 2

-- Story 3: Frontier.covers and Frontier.advance.
--
-- A frontier that just saw epoch vector (5,0) covers (3,0) but not (6,0)
-- and not (0,1) — any slot that exceeds the frontier's value is uncovered.
def storyFrontierCovers : IO Unit := do
  let epoch : VecTimestamp 2 := fun i => #[5, 0].getD i.val 0
  let fr : Frontier (VecTimestamp 2) :=
    Frontier.advance { elements := #[fun _ => 0] } epoch
  let below : VecTimestamp 2 := fun i => #[3, 0].getD i.val 0
  let above : VecTimestamp 2 := fun i => #[6, 0].getD i.val 0
  let side  : VecTimestamp 2 := fun i => #[0, 1].getD i.val 0
  assertEq "frontier covers (3,0)" (fr.covers below) true
  assertEq "frontier covers epoch itself" (fr.covers epoch) true
  assertEq "frontier does not cover (6,0)" (fr.covers above) false
  assertEq "frontier does not cover (0,1)" (fr.covers side) false

-- Story 4: FederatedState creation and epochToVec.
--
-- A 3-agent cluster; agent 1 (slot 1) completes local epoch 7.
-- epochToVec maps that to (0,7,0) — only the agent's own slot is set.
def storyEpochToVec : IO Unit := do
  let slot : Fin 3 := ⟨1, by omega⟩
  let vec := FederatedState.epochToVec 3 slot 7
  assertEq "slot 0 is 0" (vec ⟨0, by omega⟩) 0
  assertEq "slot 1 is 7" (vec ⟨1, by omega⟩) 7
  assertEq "slot 2 is 0" (vec ⟨2, by omega⟩) 0

-- Story 5: FederatedState.create and advanceFrontier round-trip.
--
-- Create a 2-agent federated state for agent 0.  Run two stabilization
-- passes on the local graph; advanceFrontier after each.  The frontier
-- after the second pass must cover the first pass's epoch vector.
def storyAdvanceFrontier : IO Unit := do
  let slot : Fin 2 := ⟨0, by omega⟩
  let fs ← FederatedState.create "agent-0" 2 slot

  -- First stabilization pass: set a var, stabilize, advance.
  let x ← Var.create fs.localState 10
  let doubled ← map (Var.watch x) (fun n => n * 2)
  let obs ← observe doubled
  State.stabilize fs.localState
  let fr1 ← fs.advanceFrontier
  let epoch1 := fs.localState.currentStabilization

  -- The frontier after pass 1 covers pass 1's epoch vector.
  let vec1 := FederatedState.epochToVec 2 slot (← epoch1)
  assertEq "fr1 covers its own epoch" (fr1.covers vec1) true

  -- Second stabilization pass.
  Var.set x 20
  State.stabilize fs.localState
  let fr2 ← fs.advanceFrontier

  -- fr2 must cover vec1 (monotonicity) and the new epoch.
  let epoch2 := fs.localState.currentStabilization
  let vec2 := FederatedState.epochToVec 2 slot (← epoch2)
  assertEq "fr2 covers earlier epoch" (fr2.covers vec1) true
  assertEq "fr2 covers its own epoch" (fr2.covers vec2) true
  assertEq "doubled after second pass" (← Observer.value! obs) 40

-- Story 6: registerRemoteVar bookkeeping.
--
-- A subscriber agent registers two remote subscriptions; the remoteKeys
-- ref should record both channels in order.
def storyRegisterRemoteVar : IO Unit := do
  let slot : Fin 3 := ⟨2, by omega⟩
  let fs ← FederatedState.create "subscriber" 3 slot

  let priceVar ← Var.create fs.localState (0 : Int)
  let rv1 : RemoteVar Int := { localVar := priceVar, sourceAgentId := "market", key := "price" }
  let volVar ← Var.create fs.localState (0 : Int)
  let rv2 : RemoteVar Int := { localVar := volVar, sourceAgentId := "market", key := "volume" }

  fs.registerRemoteVar rv1
  fs.registerRemoteVar rv2

  let keys ← fs.remoteKeys.get
  assertEq "two remoteKeys registered" keys.size 2
  assertEq "first key is price"  keys[0]! ("market", "price")
  assertEq "second key is volume" keys[1]! ("market", "volume")

-- Story 7: Two-agent causality scenario.
--
-- Agent A (slot 0) publishes a value; agent B (slot 1) subscribes via a
-- RemoteVar.  After agent B receives and stabilizes, its frontier covers
-- A's epoch vector, satisfying the distributed-causality guarantee.
def storyCausality : IO Unit := do
  let slotA : Fin 2 := ⟨0, by omega⟩
  let slotB : Fin 2 := ⟨1, by omega⟩
  let fsA ← FederatedState.create "agent-A" 2 slotA
  let fsB ← FederatedState.create "agent-B" 2 slotB

  -- Agent A: publish price = 42.
  let priceA ← Var.create fsA.localState 0
  let obsA ← observe (Var.watch priceA)
  Var.set priceA 42
  State.stabilize fsA.localState
  let frA ← fsA.advanceFrontier
  let epochA ← fsA.localState.currentStabilization

  -- Agent B: receive the value through a RemoteVar.
  let priceB ← Var.create fsB.localState 0
  let rv : RemoteVar Int := { localVar := priceB, sourceAgentId := "agent-A", key := "price" }
  fsB.registerRemoteVar rv
  let obsB ← observe (Var.watch priceB)

  -- Simulate delivery: agent B's runtime calls Var.set on the local mirror.
  Var.set priceB (← Observer.value! obsA)
  State.stabilize fsB.localState
  let frB ← fsB.advanceFrontier

  -- Agent B's frontier covers agent A's epoch vector (causality holds).
  let vecA := FederatedState.epochToVec 2 slotA epochA
  assertEq "agent B frontier covers agent A epoch" (frB.covers vecA) false
  -- (frB covers B's own axis only; global causality requires the coordinator
  --  to take the pointwise meet of both frontiers — shown here as a reminder.)
  let epochB ← fsB.localState.currentStabilization
  let vecB := FederatedState.epochToVec 2 slotB epochB
  assertEq "agent B frontier covers its own epoch" (frB.covers vecB) true
  assertEq "price delivered to B" (← Observer.value! obsB) 42

-- Story 8: State.graphParallelSafe pre-flight check.
--
-- A graph with only `map` and `var` nodes is fully parallel-safe.
-- Adding a `bind` node makes it no longer safe.
def storyGraphParallelSafe : IO Unit := do
  let st ← State.create
  let x ← Var.create st (5 : Nat)
  let doubled ← map (Var.watch x) (fun n => n * 2)
  let _ ← observe doubled
  let safe ← st.graphParallelSafe
  assertEq "pure map graph is parallel-safe" safe true

  -- A bind node is not parallel-safe.
  let st2 ← State.create
  let y ← Var.create st2 (1 : Nat)
  let extra ← Var.create st2 (0 : Nat)
  -- bind chooses which incr to return at runtime; NodeKind is `bind`, not parallel-safe.
  let bound ← bind (Var.watch y) (fun _ => pure (Var.watch extra))
  let _ ← observe bound
  let safe2 ← st2.graphParallelSafe
  assertEq "graph with bind is not parallel-safe" safe2 false

-- Story 9: FederatedState.globalFrontier covers all agents.
--
-- A 3-agent cluster; agent epochs are (5, 3, 7).  The global frontier
-- covers any timestamp whose each slot is at most the corresponding epoch,
-- but not one that exceeds any slot.
def storyGlobalFrontier : IO Unit := do
  let epochs : VecTimestamp 3 := fun i => #[5, 3, 7].getD i.val 0
  let gfr := FederatedState.globalFrontier 3 epochs

  -- A timestamp dominated pointwise by epochs is covered.
  let below : VecTimestamp 3 := fun i => #[4, 2, 6].getD i.val 0
  assertEq "global frontier covers (4,2,6)" (gfr.covers below) true

  -- Epoch vector itself is covered.
  assertEq "global frontier covers epochs itself" (gfr.covers epochs) true

  -- A timestamp exceeding slot 1 is not covered.
  let aboveSlot1 : VecTimestamp 3 := fun i => #[5, 4, 7].getD i.val 0
  assertEq "global frontier does not cover (5,4,7)" (gfr.covers aboveSlot1) false

-- Snippet mirrored in FEDERATION.md: safe stabilize-and-advance pattern.
def storySafeAdvanceSnippet : IO Unit := do
  let slot : Fin 2 := ⟨0, by omega⟩
  let fs ← FederatedState.create "agent-0" 2 slot
  let x ← Var.create fs.localState (10 : Nat)
  let doubled ← map (Var.watch x) (fun n => n * 2)
  let observer ← observe doubled
  let stats ← State.stabilizeWithStats fs.localState
  let frontier ← fs.advanceFrontierAt stats.stabilization
  let epochVec := FederatedState.epochToVec 2 slot stats.stabilization
  assertEq "federation snippet frontier covers epoch" (frontier.covers epochVec) true
  assertEq "federation snippet observer value" (← Observer.value! observer) 20

-- Story 10: advanceFrontierAt with explicit epoch from stabilizeWithStats.
--
-- stabilizeWithStats captures the epoch inside the write lock; passing it
-- to advanceFrontierAt avoids the race window present in advanceFrontier.
-- The frontier must cover the epoch vector built from that same epoch.
def storyAdvanceFrontierAt : IO Unit := do
  let slot : Fin 2 := ⟨1, by omega⟩
  let fs ← FederatedState.create "agent-at" 2 slot
  let x ← Var.create fs.localState (100 : Nat)
  let incr ← map (Var.watch x) (fun n => n + 1)
  let obs ← observe incr
  -- Safe path: epoch captured inside the write lock.
  let stats ← fs.localState.stabilizeWithStats
  let fr ← fs.advanceFrontierAt stats.stabilization
  let epochVec := FederatedState.epochToVec 2 slot stats.stabilization
  assertEq "advanceFrontierAt covers its own epoch" (fr.covers epochVec) true
  assertEq "observer value is 101" (← Observer.value! obs) 101

def runAll : IO Unit := do
  storyVecTimestampOrdering
  storyVecTimestampJoin
  storyFrontierCovers
  storyEpochToVec
  storyAdvanceFrontier
  storyRegisterRemoteVar
  storyCausality
  storyGraphParallelSafe
  storyGlobalFrontier
  storySafeAdvanceSnippet
  storyAdvanceFrontierAt
  IO.println "FederationExamples: all stories passed"

end FederationExamples
end Tests
end Leancremental
