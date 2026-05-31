import Leancremental.Core.Basic

/-!
Error-as-data combinators for incremental query results.

Compiler and LSP queries often fail normally: parsing can fail, elaboration can
produce diagnostics, and name resolution can miss. These helpers keep those
outcomes in the incremental value graph as `Except ε α` instead of using `IO`
exceptions for expected query results.
-/

namespace Leancremental
namespace IncrResult

/-- Successful incremental result. -/
def ok (state : State) (value : α) : IO (Incr (Except ε α)) :=
  const state (.ok value)

/-- Failed incremental result. -/
def error (state : State) (err : ε) : IO (Incr (Except ε α)) :=
  const state (.error err)

/-- Map over a successful incremental result, leaving errors unchanged. -/
def map (node : Incr (Except ε α)) (f : α -> β) : IO (Incr (Except ε β)) :=
  Leancremental.map node (fun
    | .ok value => .ok (f value)
    | .error err => .error err)

/-- Map over an error, leaving successful values unchanged. -/
def mapError (node : Incr (Except ε α)) (f : ε -> δ) : IO (Incr (Except δ α)) :=
  Leancremental.map node (fun
    | .ok value => .ok value
    | .error err => .error (f err))

/-- Binary map over successful results, returning the first error from left to right. -/
def map2 (left : Incr (Except ε α)) (right : Incr (Except ε β)) (f : α -> β -> γ) : IO (Incr (Except ε γ)) :=
  Leancremental.map2 left right (fun leftValue rightValue =>
    match leftValue, rightValue with
    | .ok leftOk, .ok rightOk => .ok (f leftOk rightOk)
    | .error err, _ => .error err
    | _, .error err => .error err)

/-- Bind successful results into another incremental result, propagating errors. -/
def bind (node : Incr (Except ε α)) (f : α -> IO (Incr (Except ε β))) : IO (Incr (Except ε β)) :=
  Leancremental.bind node (fun
    | .ok value => f value
    | .error err => error node.state err)

/-- Replace an error with another incremental result. -/
def recover (node : Incr (Except ε α)) (f : ε -> IO (Incr (Except ε α))) : IO (Incr (Except ε α)) :=
  Leancremental.bind node (fun
    | .ok value => ok node.state value
    | .error err => f err)

/-- Project a successful value to `some`, or errors to `none`. -/
def value? (node : Incr (Except ε α)) : IO (Incr (Option α)) :=
  Leancremental.map node (fun
    | .ok value => some value
    | .error _ => none)

/-- Project an error to `some`, or successful values to `none`. -/
def error? (node : Incr (Except ε α)) : IO (Incr (Option ε)) :=
  Leancremental.map node (fun
    | .ok _ => none
    | .error err => some err)

/-- Equality cutoff for incremental results whose error and value types have `BEq`. -/
def cutoffOfEq [BEq ε] [BEq α] : Cutoff (Except ε α) :=
  { shouldCutoff := fun oldValue newValue =>
      match oldValue, newValue with
      | .ok oldOk, .ok newOk => oldOk == newOk
      | .error oldErr, .error newErr => oldErr == newErr
      | _, _ => false }

end IncrResult
end Leancremental