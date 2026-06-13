import Leancremental.Core.Internal

/-!
Proof-oriented invariants for the stabilization correctness bugs fixed in round 3.

This module models the three concrete invariants that were violated and then
repaired:

1. completed stabilizations must apply deferred mutations before refreshing
   observers;
2. deferred mutations must not apply across mismatched stabilization epochs;
3. cancelling an incomplete stabilization must clear the deferred queue.

The model is intentionally small. It avoids re-proving executable runtime
behavior over `IO.Ref` state and instead gives precise, total propositions and
lemmas that future changes can reuse as proof obligations.
-/

namespace Leancremental
namespace Proof
namespace Stabilization

/-- The observable phases of one completed stabilization. -/
inductive StabilizationPhase where
  | heapDrained
  | deferredApplied
  | observersRefreshed
deriving Repr, BEq, DecidableEq

/-- The intended phase order for a completed stabilization pass. -/
def completedPhaseOrder : List StabilizationPhase :=
  [.heapDrained, .deferredApplied, .observersRefreshed]

/-- A small precedence relation capturing the allowed order between phases. -/
inductive PhasePrecedes : StabilizationPhase -> StabilizationPhase -> Prop where
  | heap_before_deferred : PhasePrecedes .heapDrained .deferredApplied
  | heap_before_observers : PhasePrecedes .heapDrained .observersRefreshed
  | deferred_before_observers : PhasePrecedes .deferredApplied .observersRefreshed

/-- Completed stabilizations drain the heap before applying deferred mutations. -/
theorem heap_drained_before_deferred :
    PhasePrecedes .heapDrained .deferredApplied :=
  .heap_before_deferred

/-- Completed stabilizations apply deferred mutations before refreshing observers. -/
theorem deferred_before_observers :
    PhasePrecedes .deferredApplied .observersRefreshed :=
  .deferred_before_observers

/-- The incorrect order from the round-2 bug is excluded. -/
theorem observers_do_not_precede_deferred :
    ¬ PhasePrecedes .observersRefreshed .deferredApplied := by
  intro h
  cases h

/-- The canonical completed phase order is the intended one. -/
theorem completedPhaseOrder_correct :
    completedPhaseOrder = [.heapDrained, .deferredApplied, .observersRefreshed] := rfl

/-- Effect of one deferred mutation on one logical node snapshot. -/
def applyMutationEffect (info : NodeInfo) (op : DeferredMutation) : NodeInfo :=
  match op with
  | .markStale _ _ _ =>
      { info with stale := true }
  | .invalidate _ _ _ =>
      { info with stale := true, valid := false, computedAt := none }

/-- Target node id of one deferred mutation. -/
def mutationNodeId (op : DeferredMutation) : Nat :=
  match op with
  | .markStale id _ _ => id
  | .invalidate id _ _ => id

/-- Stored epoch of one deferred mutation, if any. -/
def mutationStoredEpoch (op : DeferredMutation) : Option Nat :=
  match op with
  | .markStale _ _ epoch => epoch
  | .invalidate _ _ epoch => epoch

/-- Boolean epoch gate used by the pure proof model. -/
def storedEpochMatches (op : DeferredMutation) (currentEpoch : Nat) : Bool :=
  match mutationStoredEpoch op with
  | none => true
  | some storedEpoch => storedEpoch == currentEpoch

/-- Pure model of applying a deferred mutation to one logical node. -/
def applyMutationToNode
    (info : NodeInfo)
    (nodeId : Nat)
    (op : DeferredMutation)
    (currentEpoch : Nat) : NodeInfo :=
  if _hNode : mutationNodeId op = nodeId then
    if storedEpochMatches op currentEpoch then
      applyMutationEffect info op
    else
      info
  else
    info

/-- A mutation for a different node is a no-op on this node snapshot. -/
theorem applyMutationToNode_other_id
    (info : NodeInfo)
    (nodeId : Nat)
    (op : DeferredMutation)
    (currentEpoch : Nat)
    (hne : mutationNodeId op ≠ nodeId) :
    applyMutationToNode info nodeId op currentEpoch = info := by
  simp [applyMutationToNode, hne]

/-- A stored epoch mismatch makes the mutation a no-op even on its own node. -/
theorem applyMutationToNode_wrong_epoch
    (info : NodeInfo)
    (op : DeferredMutation)
    (storedEpoch currentEpoch : Nat)
    (hStored : mutationStoredEpoch op = some storedEpoch)
    (hne : storedEpoch ≠ currentEpoch) :
    applyMutationToNode info (mutationNodeId op) op currentEpoch = info := by
  have hbeq : (storedEpoch == currentEpoch) = false := beq_eq_false_iff_ne.mpr hne
  simp [applyMutationToNode, storedEpochMatches, hStored, hbeq]

/-- A same-epoch `markStale` mutation sets `stale := true`. -/
theorem applyMutationToNode_markStale_same_epoch
    (info : NodeInfo)
    (nodeId : Nat)
    (reason : Option String)
    (epoch : Nat) :
    applyMutationToNode info nodeId (.markStale nodeId reason (some epoch)) epoch =
      { info with stale := true } := by
  simp [applyMutationToNode, mutationNodeId, mutationStoredEpoch, storedEpochMatches, applyMutationEffect]

/-- A same-epoch `invalidate` mutation clears validity and `computedAt`. -/
theorem applyMutationToNode_invalidate_same_epoch
    (info : NodeInfo)
    (nodeId : Nat)
    (reason : Option String)
    (epoch : Nat) :
    applyMutationToNode info nodeId (.invalidate nodeId reason (some epoch)) epoch =
      { info with stale := true, valid := false, computedAt := none } := by
  simp [applyMutationToNode, mutationNodeId, mutationStoredEpoch, storedEpochMatches, applyMutationEffect]

/-- Applying a no-epoch mutation to its own node always takes effect. -/
theorem applyMutationToNode_none_epoch_applies
    (info : NodeInfo)
    (op : DeferredMutation)
    (currentEpoch : Nat)
    (hNone : mutationStoredEpoch op = none) :
    applyMutationToNode info (mutationNodeId op) op currentEpoch = applyMutationEffect info op := by
  simp [applyMutationToNode, storedEpochMatches, hNone]

/-- Pure model of applying a whole deferred queue to one logical node. -/
def applyDeferredQueueToNode
    (info : NodeInfo)
    (nodeId : Nat)
    (ops : Array DeferredMutation)
    (currentEpoch : Nat) : NodeInfo :=
  ops.foldl (fun acc op => applyMutationToNode acc nodeId op currentEpoch) info

/-- Pure model of cancellation: the deferred queue is cleared. -/
def cancelDeferredQueue (_ : Array DeferredMutation) : Array DeferredMutation := #[]

/-- Cancelling always empties the deferred queue. -/
theorem cancelDeferredQueue_empty (ops : Array DeferredMutation) :
    cancelDeferredQueue ops = #[] := rfl

/-- Applying a cancelled queue is a no-op. -/
theorem applyCancelledQueue_noop
    (info : NodeInfo)
    (nodeId : Nat)
    (ops : Array DeferredMutation)
    (currentEpoch : Nat) :
    applyDeferredQueueToNode info nodeId (cancelDeferredQueue ops) currentEpoch = info := by
  simp [applyDeferredQueueToNode, cancelDeferredQueue]

/-- Cancellation removes every pending deferred mutation from the model. -/
theorem cancel_clears_all_pending_mutations
    (ops : Array DeferredMutation) :
    (cancelDeferredQueue ops).isEmpty = true := by
  simp [cancelDeferredQueue, Array.isEmpty]

/-!
P7-style cancellation/work-restoration model.

The runtime path restores remaining recompute-heap roots back into
`pendingDirtyRef` via `recordPendingDirty`, which itself is based on
`Internal.pushIfMissing`. We model exactly that helper-level behavior here.
-/

@[simp] theorem containsNat_pushIfMissing_self (xs : Array Nat) (x : Nat) :
    Internal.containsNat (Internal.pushIfMissing xs x) x = true := by
  by_cases h : Internal.containsNat xs x = true
  · simp [Internal.pushIfMissing, h]
  · have hfalse : Internal.containsNat xs x = false := Bool.eq_false_iff.mpr h
    have hPush : Internal.containsNat (xs.push x) x = true := by
      have hMem : x ∈ xs.push x := (Array.mem_push).2 (Or.inr rfl)
      rw [Internal.containsNat, Array.any_eq_true]
      rcases (Array.mem_iff_getElem.mp hMem) with ⟨i, hi, hEq⟩
      refine ⟨i, hi, ?_⟩
      simp [hEq]
    simpa [Internal.pushIfMissing, hfalse] using hPush

theorem containsNat_pushIfMissing_of_contains
    (xs : Array Nat)
    (inserted query : Nat)
    (h : Internal.containsNat xs query = true) :
    Internal.containsNat (Internal.pushIfMissing xs inserted) query = true := by
  by_cases hInsert : Internal.containsNat xs inserted = true
  · simpa [Internal.pushIfMissing, hInsert] using h
  · have hfalse : Internal.containsNat xs inserted = false := Bool.eq_false_iff.mpr hInsert
    have hMem : query ∈ xs := by
      rw [Array.mem_iff_getElem]
      rw [Internal.containsNat, Array.any_eq_true] at h
      rcases h with ⟨i, hi, hMatch⟩
      exact ⟨i, hi, eq_of_beq hMatch⟩
    have hPush : Internal.containsNat (xs.push inserted) query = true := by
      have hMemPush : query ∈ xs.push inserted := (Array.mem_push).2 (Or.inl hMem)
      rw [Internal.containsNat, Array.any_eq_true]
      rcases (Array.mem_iff_getElem.mp hMemPush) with ⟨i, hi, hEq⟩
      refine ⟨i, hi, ?_⟩
      simp [hEq]
    simpa [Internal.pushIfMissing, hfalse] using hPush

theorem pushIfMissing_idempotent (xs : Array Nat) (id : Nat) :
    Internal.pushIfMissing (Internal.pushIfMissing xs id) id =
      Internal.pushIfMissing xs id := by
  by_cases h : Internal.containsNat xs id = true
  · simp [Internal.pushIfMissing, h]
  · have hfalse : Internal.containsNat xs id = false := Bool.eq_false_iff.mpr h
    have hPush : Internal.containsNat (xs.push id) id = true := by
      have hMem : id ∈ xs.push id := (Array.mem_push).2 (Or.inr rfl)
      rw [Internal.containsNat, Array.any_eq_true]
      rcases (Array.mem_iff_getElem.mp hMem) with ⟨i, hi, hEq⟩
      exact ⟨i, hi, by simp [hEq]⟩
    simp [Internal.pushIfMissing, hfalse, hPush]

/-- Pure model of restoring queued recompute ids into pending dirty ids. -/
def restoreQueuedWorkToPendingDirtyList
    (pending : Array Nat)
    (queued : List Nat) : Array Nat :=
  queued.foldl Internal.pushIfMissing pending

/-- Array-facing wrapper for `restoreQueuedWorkToPendingDirtyList`. -/
def restoreQueuedWorkToPendingDirty
    (pending queued : Array Nat) : Array Nat :=
  restoreQueuedWorkToPendingDirtyList pending queued.toList

theorem restoreQueuedWorkToPendingDirtyList_preserves_existing
    (pending : Array Nat)
    (queued : List Nat)
    (id : Nat)
    (hPending : Internal.containsNat pending id = true) :
    Internal.containsNat (restoreQueuedWorkToPendingDirtyList pending queued) id = true := by
  induction queued generalizing pending with
  | nil =>
      simpa [restoreQueuedWorkToPendingDirtyList] using hPending
  | cons head tail ih =>
      simpa [restoreQueuedWorkToPendingDirtyList] using
        ih (pending := Internal.pushIfMissing pending head)
          (hPending := containsNat_pushIfMissing_of_contains pending head id hPending)

/-- Existing pending dirty work is preserved by restoration. -/
theorem restoreQueuedWork_preserves_existing_pending
    (pending queued : Array Nat)
    (id : Nat)
    (hPending : Internal.containsNat pending id = true) :
    Internal.containsNat (restoreQueuedWorkToPendingDirty pending queued) id = true := by
  simpa [restoreQueuedWorkToPendingDirty] using
    restoreQueuedWorkToPendingDirtyList_preserves_existing pending queued.toList id hPending

theorem restoreQueuedWorkToPendingDirtyList_contains_of_mem
    (pending : Array Nat)
    (queued : List Nat)
    (id : Nat)
    (hQueued : id ∈ queued) :
    Internal.containsNat (restoreQueuedWorkToPendingDirtyList pending queued) id = true := by
  induction queued generalizing pending with
  | nil =>
      cases hQueued
  | cons head tail ih =>
      simp at hQueued
      rcases hQueued with hEq | hTail
      · cases hEq
        have hInserted :
            Internal.containsNat (Internal.pushIfMissing pending id) id = true :=
          containsNat_pushIfMissing_self pending id
        simpa [restoreQueuedWorkToPendingDirtyList] using
          restoreQueuedWorkToPendingDirtyList_preserves_existing
            (pending := Internal.pushIfMissing pending id)
            (queued := tail)
            (id := id)
            (hPending := hInserted)
      · simpa [restoreQueuedWorkToPendingDirtyList] using
          ih (pending := Internal.pushIfMissing pending head) hTail

/-- Every queued recompute id appears in pending dirty work after restoration. -/
theorem restoreQueuedWork_contains_restored_id
    (pending queued : Array Nat)
    (id : Nat)
    (hQueued : id ∈ queued.toList) :
    Internal.containsNat (restoreQueuedWorkToPendingDirty pending queued) id = true := by
  simpa [restoreQueuedWorkToPendingDirty] using
    restoreQueuedWorkToPendingDirtyList_contains_of_mem pending queued.toList id hQueued

/-- Duplicating one queued id does not change restoration output. -/
theorem restoreQueuedWork_duplicate_idempotent
    (pending : Array Nat)
    (id : Nat) :
    restoreQueuedWorkToPendingDirty pending #[id, id] =
      restoreQueuedWorkToPendingDirty pending #[id] := by
  simp [restoreQueuedWorkToPendingDirty, restoreQueuedWorkToPendingDirtyList, pushIfMissing_idempotent]

end Stabilization
end Proof
end Leancremental
