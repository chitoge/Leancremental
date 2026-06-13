import Leancremental.Core.Memo

/-!
Pure lemmas for memo snapshot validation and preload accounting helpers.

These theorems target total helper functions used by the runtime APIs and avoid
claiming IO-state preservation.
-/

namespace Leancremental
namespace Proof
namespace Memo

namespace MemoSnapshotValidationPolicy

@[simp] theorem validate_empty_policy_ok
    (metadata : MemoSnapshotEnvelopeMetadata) :
    MemoSnapshotValidationPolicy.validate {} metadata = .ok () := by
  cases metadata
  simp [MemoSnapshotValidationPolicy.validate]
  rfl

@[simp] theorem validate_exact_match_ok
    (schema build digest : String)
    (timestamp : Nat) :
    MemoSnapshotValidationPolicy.validate
      { expectedSchema := some schema,
        expectedBuild := some build,
        expectedInputDigest := some digest,
        minTimestamp := some timestamp }
      { schema := schema,
        build := build,
        inputDigest := digest,
        timestamp := timestamp } = .ok () := by
  simp [MemoSnapshotValidationPolicy.validate]
  rfl

theorem validate_schema_mismatch
    (expected actual build digest : String)
    (timestamp : Nat)
  (mismatch : (actual == expected) = false) :
    MemoSnapshotValidationPolicy.validate
      { expectedSchema := some expected }
      { schema := actual,
        build := build,
        inputDigest := digest,
        timestamp := timestamp } =
      .error (.schemaMismatch expected actual) := by
  simp [MemoSnapshotValidationPolicy.validate, mismatch]

theorem validate_build_mismatch
    (schema expected actual digest : String)
    (timestamp : Nat)
  (mismatch : (actual == expected) = false) :
    MemoSnapshotValidationPolicy.validate
      { expectedSchema := some schema,
        expectedBuild := some expected }
      { schema := schema,
        build := actual,
        inputDigest := digest,
        timestamp := timestamp } =
      .error (.buildMismatch expected actual) := by
  simp [MemoSnapshotValidationPolicy.validate, mismatch]

theorem validate_input_digest_mismatch
    (schema build expected actual : String)
    (timestamp : Nat)
  (mismatch : (actual == expected) = false) :
    MemoSnapshotValidationPolicy.validate
      { expectedSchema := some schema,
        expectedBuild := some build,
        expectedInputDigest := some expected }
      { schema := schema,
        build := build,
        inputDigest := actual,
        timestamp := timestamp } =
      .error (.inputDigestMismatch expected actual) := by
  simp [MemoSnapshotValidationPolicy.validate, mismatch]

theorem validate_timestamp_too_old
    (schema build digest : String)
    (minimum actual : Nat)
  (tooOld : (minimum <= actual) = false) :
    MemoSnapshotValidationPolicy.validate
      { expectedSchema := some schema,
        expectedBuild := some build,
        expectedInputDigest := some digest,
        minTimestamp := some minimum }
      { schema := schema,
        build := build,
        inputDigest := digest,
        timestamp := actual } =
      .error (.timestampTooOld minimum actual) := by
  simp [MemoSnapshotValidationPolicy.validate, tooOld]

end MemoSnapshotValidationPolicy

namespace MemoSnapshotPreloadSummary

@[simp] theorem record_loaded
    (summary : MemoSnapshotPreloadSummary) :
  (MemoSnapshotPreloadSummary.record summary .loaded).loaded = summary.loaded + 1 := rfl

@[simp] theorem record_alreadyPresent
    (summary : MemoSnapshotPreloadSummary) :
  (MemoSnapshotPreloadSummary.record summary .alreadyPresent).alreadyPresent = summary.alreadyPresent + 1 := rfl

@[simp] theorem record_missing
    (summary : MemoSnapshotPreloadSummary) :
  (MemoSnapshotPreloadSummary.record summary .missing).missing = summary.missing + 1 := rfl

@[simp] theorem record_rejected
    (summary : MemoSnapshotPreloadSummary)
    (reason : MemoSnapshotRejectionReason) :
  (MemoSnapshotPreloadSummary.record summary (.rejected reason)).rejected = summary.rejected + 1 := rfl

@[simp] theorem record_decodeError
    (summary : MemoSnapshotPreloadSummary)
    (err : String) :
  (MemoSnapshotPreloadSummary.record summary (.decodeError err)).decodeError = summary.decodeError + 1 := rfl

end MemoSnapshotPreloadSummary

end Memo
end Proof
end Leancremental
