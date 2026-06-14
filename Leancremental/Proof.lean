import Leancremental.Core
import Leancremental.Proof.Invariant
import Leancremental.Proof.Metadata
import Leancremental.Proof.Stabilization
import Leancremental.Proof.PureShape
import Leancremental.Proof.Query
import Leancremental.Proof.Memo
import Leancremental.Proof.Scheduler
import Leancremental.Proof.Parallel
import Leancremental.Proof.Timestamp
import Leancremental.Proof.Frontier
import Leancremental.Proof.Federation

/-! Basic proof lemmas for the executable Leancremental API. -/

namespace Leancremental

/-! Cutoff simplification lemmas. -/
namespace Cutoff

/-- A cutoff is sound for relation `R` when every cutoff implies `R`. -/
def Sound (cutoff : Cutoff α) (R : α -> α -> Prop) : Prop :=
    ∀ oldValue newValue,
        cutoff.shouldCutoff oldValue newValue = true -> R oldValue newValue

/-- `Cutoff.never` never cuts off propagation. -/
@[simp] theorem never_apply (oldValue newValue : α) :
    (Cutoff.never : Cutoff α).shouldCutoff oldValue newValue = false := rfl

/-- `Cutoff.always` always cuts off propagation. -/
@[simp] theorem always_apply (oldValue newValue : α) :
    (Cutoff.always : Cutoff α).shouldCutoff oldValue newValue = true := rfl

/-- `Cutoff.never` always propagates. -/
@[simp] theorem shouldPropagate_never (oldValue newValue : α) :
    (Cutoff.never : Cutoff α).shouldPropagate oldValue newValue = true := rfl

/-- `Cutoff.always` never propagates. -/
@[simp] theorem shouldPropagate_always (oldValue newValue : α) :
    (Cutoff.always : Cutoff α).shouldPropagate oldValue newValue = false := rfl

/-- Decidable equality cutoffs return `true` exactly when the values are equal. -/
theorem ofDecidableEq_cuts_off_iff [DecidableEq α] (oldValue newValue : α) :
    (Cutoff.ofDecidableEq : Cutoff α).shouldCutoff oldValue newValue = true <-> oldValue = newValue := by
  simp [Cutoff.ofDecidableEq]

/-- `Cutoff.never` is sound for equality. -/
theorem never_sound : (Cutoff.never : Cutoff α).Sound Eq := by
    intro oldValue newValue hCutoff
    cases hCutoff

/-- `Cutoff.ofEq` is sound for equality when `BEq` is lawful. -/
theorem ofEq_sound [BEq α] [LawfulBEq α] :
        (Cutoff.ofEq : Cutoff α).Sound Eq := by
    intro oldValue newValue hCutoff
    exact eq_of_beq (by simpa [Cutoff.ofEq] using hCutoff)

/-- `Cutoff.ofDecidableEq` is sound for equality. -/
theorem ofDecidableEq_sound [DecidableEq α] :
        (Cutoff.ofDecidableEq : Cutoff α).Sound Eq := by
    intro oldValue newValue hCutoff
    exact (ofDecidableEq_cuts_off_iff (oldValue := oldValue) (newValue := newValue)).1 hCutoff

/-- `Cutoff.ofHash` is sound for equality when `BEq` is lawful. -/
theorem ofHash_sound [Hashable α] [BEq α] [LawfulBEq α] :
        (Cutoff.ofHash : Cutoff α).Sound Eq := by
    intro oldValue newValue hCutoff
    simp [Cutoff.ofHash] at hCutoff
    exact hCutoff.2

/-- `Cutoff.ofHash` is sound for hash-equality. -/
theorem ofHash_sound_hashEq [Hashable α] [BEq α] :
        (Cutoff.ofHash : Cutoff α).Sound (fun oldValue newValue => hash oldValue = hash newValue) := by
    intro oldValue newValue hCutoff
    simp [Cutoff.ofHash] at hCutoff
    exact hCutoff.1

/-- `Cutoff.ofHashUnchecked` is sound for hash-equality. -/
theorem ofHashUnchecked_sound_hashEq [Hashable α] :
        (Cutoff.ofHashUnchecked : Cutoff α).Sound (fun oldValue newValue => hash oldValue = hash newValue) := by
    intro oldValue newValue hCutoff
    exact eq_of_beq (by simpa [Cutoff.ofHashUnchecked] using hCutoff)

/-- A concrete hash collision witness refutes `Cutoff.ofHashUnchecked` soundness for `Eq`. -/
theorem ofHashUnchecked_not_sound_Eq_of_collision [Hashable α]
        {oldValue newValue : α}
        (collision : hash oldValue = hash newValue)
        (different : oldValue ≠ newValue) :
        ¬(Cutoff.ofHashUnchecked : Cutoff α).Sound Eq := by
    intro hSound
    have hCutoff : (Cutoff.ofHashUnchecked : Cutoff α).shouldCutoff oldValue newValue = true := by
        simp [Cutoff.ofHashUnchecked, collision]
    exact different (hSound oldValue newValue hCutoff)

end Cutoff

end Leancremental
