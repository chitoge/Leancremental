import Leancremental.Core
import Leancremental.Proof.Invariant
import Leancremental.Proof.Metadata
import Leancremental.Proof.PureShape
import Leancremental.Proof.Query

/-! Basic proof lemmas for the executable Leancremental API. -/

namespace Leancremental

/-! Cutoff simplification lemmas. -/
namespace Cutoff

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

end Cutoff

end Leancremental
