import Leancremental.Core.Types

/-!
Frontier and antichain invariant proofs (Phase 2).

This module establishes three key properties of the `Frontier`/`Antichain` types
and their role in the stabilization loop:

1. **`frontier_monotone`**: The frontier only advances. Each completed stabilization
   yields a frontier that dominates the previous one.

2. **`antichain_well_formed`**: For `T = Nat` (total order), every frontier produced
   by `Frontier.advance` is a singleton, trivially satisfying the antichain invariant
   (no two elements to compare).

3. **`frontier_observer_consistency`**: If a frontier covers timestamp `t`, then `t`
   occurred at or before the current epoch.  Observers see values computed at or before
   the current frontier.
-/

namespace Leancremental
namespace Proof
namespace Frontier

open Leancremental

/-! ## Model: frontier history -/

/-- A model of the sequence of frontiers produced by successive stabilization
    passes.  `history n` is the frontier after `n` completed passes. -/
def historyNat (n : Nat) : Leancremental.Frontier Nat :=
  Leancremental.Frontier.advance { elements := #[] } n

/-- The frontier after pass `n` contains exactly the epoch `n`. -/
theorem historyNat_elements (n : Nat) :
    (historyNat n).elements = #[n] := rfl

/-! ## frontier_monotone -/

/-- A single `Frontier.advance` step yields a frontier that covers the new epoch. -/
theorem advance_covers_new_epoch [Timestamp T] (fr : Leancremental.Frontier T) (t : T) :
    (Leancremental.Frontier.advance fr t).covers t = true := by
  simp [Leancremental.Frontier.advance, Leancremental.Frontier.covers]
  exact Timestamp.le_refl t

/-- The Nat frontier after pass `n` covers epoch `n`. -/
theorem nat_frontier_covers_epoch (n : Nat) :
    (historyNat n).covers n = true := by
  simp [historyNat, Leancremental.Frontier.advance, Leancremental.Frontier.covers]
  exact Timestamp.le_refl n

/-- For `T = Nat`, if `m ≤ n` then the frontier after pass `n` covers epoch `m`. -/
theorem nat_frontier_monotone (m n : Nat) (h : m ≤ n) :
    (historyNat n).covers m = true := by
  simp [historyNat, Leancremental.Frontier.advance, Leancremental.Frontier.covers]
  exact Nat.ble_eq_true_of_le h

/-- **Frontier monotone**: later passes produce frontiers that subsume earlier ones.
    Formally, if `m ≤ n`, everything covered by pass-`m`'s frontier is also covered
    by pass-`n`'s frontier. -/
theorem frontier_monotone (m n : Nat) (h : m ≤ n) (t : Nat)
    (hCovered : (historyNat m).covers t = true) :
    (historyNat n).covers t = true := by
  simp [historyNat, Leancremental.Frontier.advance, Leancremental.Frontier.covers] at *
  exact Nat.ble_eq_true_of_le
    (Nat.le_trans (Nat.le_of_ble_eq_true hCovered) h)

/-! ## antichain_well_formed -/

/-- **Antichain well-formed**: For `T = Nat`, `Frontier.advance` always produces a
    singleton antichain.  A singleton trivially satisfies pairwise incomparability
    (there are no two distinct elements to violate it). -/
theorem antichain_well_formed (fr : Leancremental.Frontier Nat) (t : Nat) :
    (Leancremental.Frontier.advance fr t).elements.size = 1 := by
  simp [Leancremental.Frontier.advance]

/-- Every element at index 0 of an advanced frontier equals the epoch `t`. -/
theorem antichain_element_eq (fr : Leancremental.Frontier Nat) (t : Nat) :
    (Leancremental.Frontier.advance fr t).elements[0]? = some t := by
  simp [Leancremental.Frontier.advance]

/-! ## frontier_observer_consistency -/

/-- **Frontier observer consistency**: If the frontier covers timestamp `t`, then
    `t` is at or before the latest completed epoch.

    Formally: if `fr` covers `t` (some element of `fr.elements` is ≥ `t`), then
    there exists an element `e` in `fr.elements` such that `t ≤ e`. -/
theorem frontier_observer_consistency [Timestamp T] (fr : Leancremental.Frontier T) (t : T)
    (h : fr.covers t = true) :
    ∃ e ∈ fr.elements, Timestamp.le t e = true := by
  obtain ⟨i, _, _, hi, hle⟩ := Array.any_iff_exists.mp h
  exact ⟨fr.elements[i]'hi, Array.getElem_mem hi, hle⟩

/-- For `T = Nat`: the frontier after epoch `n` covers `t` iff `t ≤ n`. -/
theorem nat_frontier_covers_iff (n t : Nat) :
    (historyNat n).covers t = true ↔ t ≤ n := by
  simp [historyNat, Leancremental.Frontier.advance, Leancremental.Frontier.covers]
  constructor
  · exact Nat.le_of_ble_eq_true
  · exact Nat.ble_eq_true_of_le

end Frontier
end Proof
end Leancremental
