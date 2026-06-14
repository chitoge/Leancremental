import Leancremental.Core.Types
import Leancremental.Core.Federation

/-!
Causality proof for the federation layer (Phase 5).

This module establishes `distributed_causality`: when a federated agent's
frontier covers a timestamp `t`, the agent has completed at least one
stabilization pass whose vector clock epoch dominates `t` at the agent's slot.

**Model assumptions** (not enforced by the kernel):

1. `FederatedState.advanceFrontier` is called exactly once after each
   completed local stabilization pass.

2. `epochToVec n slot k` correctly encodes Nat epoch `k` into `VecTimestamp n`
   by placing `k` at `slot` and `0` elsewhere.

3. The local stabilization counter is monotonically non-decreasing
   (guaranteed by `State.stabilizationNum` being set only by `startOrResumeStabilization`
   which always increments).
-/

namespace Leancremental
namespace Proof
namespace Federation

open Leancremental

/-! ## Pure model -/

/-- A model of the sequence of frontier snapshots produced by successive
    `advanceFrontier` calls for one agent. -/
def agentFrontierHistory (n : Nat) (slot : Fin n) (k : Nat) :
    Leancremental.Frontier (VecTimestamp n) :=
  Leancremental.Frontier.advance { elements := #[fun _ => 0] }
    (FederatedState.epochToVec n slot k)

/-- The frontier after pass `k` contains exactly the vector `epochToVec n slot k`. -/
theorem history_elements (n : Nat) (slot : Fin n) (k : Nat) :
    (agentFrontierHistory n slot k).elements = #[FederatedState.epochToVec n slot k] := rfl

/-! ## distributed_causality -/

/-- An agent's frontier after pass `k` covers the vector `epochToVec n slot k`.
    This is the base case: the current pass's epoch is always in the frontier. -/
theorem frontier_covers_own_epoch (n : Nat) (slot : Fin n) (k : Nat) :
    (agentFrontierHistory n slot k).covers (FederatedState.epochToVec n slot k) = true := by
  simp [agentFrontierHistory, Leancremental.Frontier.advance, Leancremental.Frontier.covers]
  exact Timestamp.le_refl _

/-- A component-wise property of `epochToVec`: the agent's slot equals the epoch. -/
theorem epochToVec_slot (n : Nat) (slot : Fin n) (k : Nat) :
    FederatedState.epochToVec n slot k slot = k := by
  simp [FederatedState.epochToVec]

/-- A component-wise property of `epochToVec`: other slots are 0. -/
theorem epochToVec_other (n : Nat) (slot : Fin n) (k : Nat) (i : Fin n) (h : i ≠ slot) :
    FederatedState.epochToVec n slot k i = 0 := by
  simp [FederatedState.epochToVec, h]

/-- Extract pointwise inequality from `Timestamp.le` for `VecTimestamp`.
    `Timestamp.le (T := VecTimestamp n)` is `decide (∀ i, a i ≤ b i)` by definition,
    so `of_decide_eq_true`/`decide_eq_true` apply directly. -/
private theorem vec_le_iff (n : Nat) (a b : VecTimestamp n) :
    Timestamp.le a b = true ↔ ∀ i : Fin n, a i ≤ b i :=
  ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

/--
**Distributed causality**: If a federated agent's frontier covers timestamp `t`,
then there exists an epoch `k` such that:
  1. The agent has completed at least one stabilization pass at epoch `k`.
  2. The agent's slot in `t` is at most `k`.

This guarantees that any value read from the graph after frontier coverage was
computed in a stabilization pass that causally dominates `t` at this agent's slot.

In the pure model, the frontier after pass `k` is `{epochToVec n slot k}`,
so "covers t" means `∀ i : Fin n, t i ≤ epochToVec n slot k i`,
which at the agent's slot gives `t[slot] ≤ k`.
-/
theorem distributed_causality (n : Nat) (slot : Fin n) (k : Nat)
    (t : VecTimestamp n)
    (h : (agentFrontierHistory n slot k).covers t = true) :
    t slot ≤ k := by
  simp [agentFrontierHistory, Leancremental.Frontier.advance, Leancremental.Frontier.covers] at h
  have hall := (vec_le_iff n t (FederatedState.epochToVec n slot k)).mp h
  have hslot := hall slot
  rw [epochToVec_slot] at hslot
  exact hslot

/-- Monotonicity: if the local epoch advances from `k` to `k'` (`k ≤ k'`), the
    frontier of pass `k'` covers everything the frontier of pass `k` covered. -/
theorem frontier_monotone_across_passes
    (n : Nat) (slot : Fin n) (k k' : Nat) (hle : k ≤ k')
    (t : VecTimestamp n) (h : (agentFrontierHistory n slot k).covers t = true) :
    (agentFrontierHistory n slot k').covers t = true := by
  simp [agentFrontierHistory, Leancremental.Frontier.advance, Leancremental.Frontier.covers] at h ⊢
  have hall := (vec_le_iff n t (FederatedState.epochToVec n slot k)).mp h
  apply (vec_le_iff n t (FederatedState.epochToVec n slot k')).mpr
  intro i
  have hi := hall i
  by_cases heq : i = slot
  · subst heq
    rw [epochToVec_slot] at hi
    rw [epochToVec_slot]
    exact Nat.le_trans hi hle
  · rw [epochToVec_other n slot k i heq] at hi
    rw [epochToVec_other n slot k' i heq]
    exact hi

/-! ## globalFrontier -/

/--
**Global frontier coverage**: the frontier returned by `FederatedState.globalFrontier`
covers a timestamp `t` iff every slot of `t` is at most the corresponding epoch.

This is the formal companion to `distributed_causality`: given a global frontier
assembled from per-agent epochs, any timestamp covered by it satisfies the causal
dominance condition at **every** slot simultaneously.
-/
theorem globalFrontier_covers_iff (n : Nat) (epochs : VecTimestamp n) (t : VecTimestamp n) :
    (FederatedState.globalFrontier n epochs).covers t = true ↔ ∀ i : Fin n, t i ≤ epochs i := by
  simp [FederatedState.globalFrontier, Leancremental.Frontier.covers]
  exact vec_le_iff n t epochs

end Federation
end Proof
end Leancremental
