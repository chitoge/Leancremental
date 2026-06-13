import Leancremental.Core.Memo
import Leancremental.Core.Aggregate
import Leancremental.Core.Result

/-!
Proof lemmas for the pure helpers behind query-oriented APIs.

The IO APIs in `MemoTable`, `MemoScope`, `IndexedAggregate`, and `IncrResult`
mutate or allocate runtime graph nodes. This module intentionally proves facts
only about the pure helper functions those APIs call, so the lemmas stay tied to
implementation code without pretending to prove IO-state preservation yet.
-/

namespace Leancremental
namespace Proof
namespace Query

/-- An empty memo-scope key array contains no key. -/
@[simp] theorem memoContainsKey_empty [BEq κ] (key : κ) :
    memoContainsKey (#[] : Array κ) key = false := by
  simp [memoContainsKey]

/-- Pushing a key makes it present in the memo-scope key array. -/
@[simp] theorem memoContainsKey_push_same [BEq κ] [ReflBEq κ]
    (keys : Array κ) (key : κ) :
    memoContainsKey (keys.push key) key = true := by
  simp [memoContainsKey]

/-- Pushing a different key leaves memo key lookup unchanged. -/
theorem memoContainsKey_push_other [BEq κ]
    (keys : Array κ) (inserted query : κ)
    (different : (inserted == query) = false) :
    memoContainsKey (keys.push inserted) query = memoContainsKey keys query := by
  simp [memoContainsKey, different]

/-- Conditionally inserting a key when missing guarantees that key is present. -/
theorem memoContainsKey_insertIfMissing_same [BEq κ] [ReflBEq κ]
    (keys : Array κ) (key : κ) :
    memoContainsKey (if memoContainsKey keys key then keys else keys.push key) key = true := by
  by_cases h : memoContainsKey keys key
  · simp [h]
  · simp [h, memoContainsKey_push_same]

/-- Boolean aggregate key lookup is equivalent to a matching indexed entry. -/
theorem aggregateContainsKey_eq_true [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ) :
    aggregateContainsKey entries key = true ↔
      ∃ (index : Nat) (inBounds : index < entries.size),
        (entries[index].1 == key) = true := by
  simp [aggregateContainsKey]

/-- Boolean aggregate key lookup fails exactly when every indexed entry has a different key. -/
theorem aggregateContainsKey_eq_false [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ) :
    aggregateContainsKey entries key = false ↔
      ∀ (index : Nat) (inBounds : index < entries.size),
        (entries[index].1 == key) = false := by
  simp [aggregateContainsKey]

/-- Membership-oriented variant of `aggregateContainsKey_eq_false`. -/
theorem aggregateContainsKey_eq_false_mem [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ) :
    aggregateContainsKey entries key = false ↔
      ∀ entry, entry ∈ entries -> ¬(entry.1 == key) := by
  simpa [aggregateContainsKey] using
    (Array.any_eq_false' (p := fun entry : κ × Incr α => entry.1 == key) (as := entries))

/-- Inserting a missing aggregate key grows the entry array by one. -/
theorem aggregateUpsert_size_of_not_present [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ) (node : Incr α)
    (h : aggregateContainsKey entries key = false) :
    (aggregateUpsert entries key node).size = entries.size + 1 := by
  simp [aggregateUpsert, h]

/-- Replacing an existing aggregate key preserves the entry array size. -/
theorem aggregateUpsert_size_of_present [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ) (node : Incr α)
    (h : aggregateContainsKey entries key = true) :
    (aggregateUpsert entries key node).size = entries.size := by
  simp [aggregateUpsert, h]

/-- Upserting a key makes that key present in the aggregate entry array. -/
theorem aggregateContainsKey_upsert_same [BEq κ] [ReflBEq κ]
    (entries : Array (κ × Incr α)) (key : κ) (node : Incr α) :
    aggregateContainsKey (aggregateUpsert entries key node) key = true := by
  by_cases h : aggregateContainsKey entries key
  · have htrue : aggregateContainsKey entries key = true := by
      simpa using h
    simp [aggregateUpsert, h]
    rw [aggregateContainsKey_eq_true] at htrue ⊢
    rcases htrue with ⟨index, inBounds, key_match⟩
    refine ⟨index, by simpa using inBounds, ?_⟩
    simp [key_match]
  · have hfalse : aggregateContainsKey entries key = false := Bool.eq_false_iff.mpr h
    have upsert_eq : aggregateUpsert entries key node = entries.push (key, node) := by
      simp [aggregateUpsert, hfalse]
    rw [upsert_eq]
    simp [aggregateContainsKey]

/-- Appending a missing aggregate key leaves lookup for a different key unchanged. -/
theorem aggregateContainsKey_upsert_missing_other [BEq κ]
    (entries : Array (κ × Incr α)) (inserted query : κ) (node : Incr α)
    (missing : aggregateContainsKey entries inserted = false)
    (different : (inserted == query) = false) :
    aggregateContainsKey (aggregateUpsert entries inserted node) query =
      aggregateContainsKey entries query := by
  have upsert_eq : aggregateUpsert entries inserted node = entries.push (inserted, node) := by
    simp [aggregateUpsert, missing]
  rw [upsert_eq]
  simp [aggregateContainsKey, different]

/-- Replacing entries for `key` does not change whether an entry matches a different lawful key. -/
theorem aggregateUpsert_entry_lookup_other [BEq κ] [LawfulBEq κ]
    (entry : κ × Incr α) (key query : κ) (node : Incr α)
    (different : (key == query) = false) :
    ((if entry.1 == key then (key, node) else entry).1 == query) = (entry.1 == query) := by
  rcases entry with ⟨entryKey, entryNode⟩
  by_cases h : entryKey == key
  · have entry_eq : entryKey = key := eq_of_beq h
    subst entryKey
    simp [different]
  · have hfalse : (entryKey == key) = false := Bool.eq_false_iff.mpr h
    simp [hfalse]

/-- Upserting a key leaves lookup for a different lawful key unchanged. -/
theorem aggregateContainsKey_upsert_other [BEq κ] [LawfulBEq κ]
    (entries : Array (κ × Incr α)) (key query : κ) (node : Incr α)
    (different : (key == query) = false) :
    aggregateContainsKey (aggregateUpsert entries key node) query =
      aggregateContainsKey entries query := by
  by_cases h : aggregateContainsKey entries key
  · have htrue : aggregateContainsKey entries key = true := by
      simpa using h
    have upsert_eq :
        aggregateUpsert entries key node =
          entries.map (fun entry => if entry.1 == key then (key, node) else entry) := by
      simp [aggregateUpsert, htrue]
    rw [upsert_eq]
    unfold aggregateContainsKey
    rw [Array.any_map]
    apply Array.any_congr rfl
    · intro entry
      exact aggregateUpsert_entry_lookup_other entry key query node different
    · rfl
    · rfl
  · have hfalse : aggregateContainsKey entries key = false := Bool.eq_false_iff.mpr h
    exact aggregateContainsKey_upsert_missing_other entries key query node hfalse different

/-- Erasing aggregate entries for a key removes that key from the entry array. -/
theorem aggregateErase_not_contains [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ) :
    aggregateContainsKey (aggregateErase entries key) key = false := by
  rw [aggregateContainsKey_eq_false]
  intro index inBounds
  have kept : ((aggregateErase entries key)[index].1 != key) := by
    simpa [aggregateErase] using
      (Array.getElem_filter (xs := entries) (p := fun entry : κ × Incr α => entry.1 != key) inBounds)
  simpa [bne] using kept

/-- Erasing aggregate entries cannot grow the entry array. -/
theorem aggregateErase_size_le [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ) :
    (aggregateErase entries key).size ≤ entries.size := by
  simpa [aggregateErase] using
    (Array.size_filter_le (p := fun entry : κ × Incr α => entry.1 != key) (xs := entries))

/-- Erasing a missing aggregate key preserves the entry array size. -/
theorem aggregateErase_size_of_not_present [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ)
    (h : aggregateContainsKey entries key = false) :
    (aggregateErase entries key).size = entries.size := by
  simp [aggregateErase]
  intro entryKey entryNode entry_mem
  have key_ne : ¬(entryKey == key) :=
    (aggregateContainsKey_eq_false_mem entries key).mp h (entryKey, entryNode) entry_mem
  simpa [bne] using key_ne

/-- Erasing a present aggregate key strictly shrinks the entry array.

The shrink can be larger than one when multiple entries match the same `BEq` key. -/
theorem aggregateErase_size_lt_of_present [BEq κ]
    (entries : Array (κ × Incr α)) (key : κ)
    (h : aggregateContainsKey entries key = true) :
    (aggregateErase entries key).size < entries.size := by
  rw [aggregateContainsKey_eq_true] at h
  rcases h with ⟨index, inBounds, key_match⟩
  simp [aggregateErase]
  exact ⟨entries[index].1, ⟨entries[index].2, Array.getElem_mem inBounds⟩, by simp [bne, key_match]⟩

end Query
end Proof

namespace IncrResult

/-- Equality cutoffs compare successful result values with `BEq`. -/
@[simp] theorem cutoffOfEq_ok_ok [BEq ε] [BEq α] (oldValue newValue : α) :
    (cutoffOfEq (ε := ε) (α := α)).shouldCutoff (.ok oldValue) (.ok newValue) =
      (oldValue == newValue) := rfl

/-- Equality cutoffs compare error result values with `BEq`. -/
@[simp] theorem cutoffOfEq_error_error [BEq ε] [BEq α] (oldErr newErr : ε) :
    (cutoffOfEq (ε := ε) (α := α)).shouldCutoff (.error oldErr) (.error newErr) =
      (oldErr == newErr) := rfl

/-- Equality cutoffs never cut off when a success becomes an error. -/
@[simp] theorem cutoffOfEq_ok_error [BEq ε] [BEq α] (value : α) (err : ε) :
    (cutoffOfEq (ε := ε) (α := α)).shouldCutoff (.ok value) (.error err) = false := rfl

/-- Equality cutoffs never cut off when an error becomes a success. -/
@[simp] theorem cutoffOfEq_error_ok [BEq ε] [BEq α] (err : ε) (value : α) :
    (cutoffOfEq (ε := ε) (α := α)).shouldCutoff (.error err) (.ok value) = false := rfl

end IncrResult
end Leancremental
