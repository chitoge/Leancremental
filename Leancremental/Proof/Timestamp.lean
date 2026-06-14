import Leancremental.Core.Types

/-!
Law verification for `Timestamp Nat` and `LatticeTimestamp Nat` (Phase 1).

These are sanity-checks that the concrete `Nat` instance satisfies every law
declared in the `Timestamp` and `LatticeTimestamp` typeclasses.  They also
serve as the canonical model proof obligations that Phase 5 (`VecTimestamp`)
must replicate.
-/

namespace Leancremental
namespace Proof
namespace Timestamp

open Leancremental

/-! ## Timestamp Nat laws -/

theorem nat_le_refl (t : Nat) : (Timestamp.le (T := Nat)) t t = true :=
  Timestamp.le_refl t

theorem nat_le_antisymm (a b : Nat)
    (hab : (Timestamp.le (T := Nat)) a b = true)
    (hba : (Timestamp.le (T := Nat)) b a = true) : a = b :=
  Timestamp.le_antisymm a b hab hba

theorem nat_le_trans (a b c : Nat)
    (hab : (Timestamp.le (T := Nat)) a b = true)
    (hbc : (Timestamp.le (T := Nat)) b c = true) :
    (Timestamp.le (T := Nat)) a c = true :=
  Timestamp.le_trans a b c hab hbc

-- le_total and succ_gt are Nat-specific (not in the general Timestamp class).
-- Vector clocks have a partial order, so le_total doesn't generalize.

theorem nat_le_total (a b : Nat) :
    (Timestamp.le (T := Nat)) a b = true ∨ (Timestamp.le (T := Nat)) b a = true := by
  rcases Nat.le_or_le a b with h | h
  · exact Or.inl (Nat.ble_eq_true_of_le h)
  · exact Or.inr (Nat.ble_eq_true_of_le h)

theorem nat_zero_le (t : Nat) : (Timestamp.le (T := Nat)) 0 t = true :=
  Timestamp.zero_le t

theorem nat_succ_gt (t : Nat) :
    (Timestamp.le (T := Nat)) t (t + 1) = true ∧
    (Timestamp.le (T := Nat)) (t + 1) t = false :=
  ⟨Nat.ble_eq_true_of_le (Nat.le_succ t),
   by show Nat.ble (t + 1) t = false
      cases h : (t + 1).ble t
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_succ_le_self t)⟩

/-- `Timestamp.le` for `Nat` agrees with `Nat.ble`. -/
theorem nat_timestamp_le_eq_ble (a b : Nat) :
    (Timestamp.le (T := Nat)) a b = Nat.ble a b := rfl

/-! ## LatticeTimestamp Nat laws -/

theorem nat_join_ge_left (a b : Nat) :
    (Timestamp.le (T := Nat)) a (LatticeTimestamp.join (T := Nat) a b) = true :=
  LatticeTimestamp.join_ge_left a b

theorem nat_join_ge_right (a b : Nat) :
    (Timestamp.le (T := Nat)) b (LatticeTimestamp.join (T := Nat) a b) = true :=
  LatticeTimestamp.join_ge_right a b

theorem nat_join_le (a b c : Nat)
    (hac : (Timestamp.le (T := Nat)) a c = true)
    (hbc : (Timestamp.le (T := Nat)) b c = true) :
    (Timestamp.le (T := Nat)) (LatticeTimestamp.join (T := Nat) a b) c = true :=
  LatticeTimestamp.join_le a b c hac hbc

/-- `LatticeTimestamp.join` for `Nat` is `Nat.max`. -/
theorem nat_join_eq_max (a b : Nat) :
    LatticeTimestamp.join (T := Nat) a b = Nat.max a b := rfl

end Timestamp
end Proof
end Leancremental
