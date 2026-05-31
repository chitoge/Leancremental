import Leancremental

/-! Shared utilities for Leancremental's executable tests. -/

namespace Leancremental
namespace Tests

/-- Assert equality with a labelled error message. -/
def assertEq [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  if actual == expected then
    pure ()
  else
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

/-- Assert that an `Except` value is `ok expected`. -/
def assertOk [BEq α] [Repr ε] [Repr α] (label : String) (actual : Except ε α) (expected : α) : IO Unit := do
  match actual with
  | .ok value => assertEq label value expected
  | .error err => throw (IO.userError s!"{label}: expected ok {repr expected}, got error {repr err}")

/-- Assert that an `Except` value is `error expected`. -/
def assertError [BEq ε] [Repr ε] [Repr α] (label : String) (actual : Except ε α) (expected : ε) : IO Unit := do
  match actual with
  | .ok value => throw (IO.userError s!"{label}: expected error {repr expected}, got ok {repr value}")
  | .error err => assertEq label err expected

end Tests
end Leancremental
