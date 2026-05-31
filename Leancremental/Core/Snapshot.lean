import Leancremental.Core.Observer
import Leancremental.Pure

/-!
Bridge from the executable core to the pure proof model.

The mutable runtime remains layered underneath `Pure`, but the public
`Leancremental.Core` umbrella imports this module so stable executable values can
be reflected into proof-friendly pure models once they have been read from `IO`.
-/

namespace Leancremental

namespace CoreSnapshot

/--
Compile a pure expression into an executable incremental graph.

This is the strongest current connection between `Pure` and `Core`: the same
`Pure.Expr` that proofs simplify is also the recipe used to allocate executable
`const`, `map`, and `map2` nodes.
-/
def compile (state : State) : Pure.Expr α -> IO (Incr α)
  | .const value => Leancremental.const state value
  | .map expr f => do
      let node <- compile state expr
      Leancremental.map node f
  | .map2 left right f => do
      let leftNode <- compile state left
      let rightNode <- compile state right
      Leancremental.map2 leftNode rightNode f

/-- Compile an array of pure expressions and fold them with an executable `arrayFold` node. -/
def compileFoldArray (state : State) (exprs : Array (Pure.Expr α)) (init : β) (f : β -> α -> β) : IO (Incr β) := do
  let mut nodes := #[]
  for expr in exprs do
    nodes := nodes.push (← compile state expr)
  Leancremental.arrayFold state nodes init f

/-- Compile and observe a pure fold expression using an executable `arrayFold` node. -/
def observeFoldArray (state : State) (exprs : Array (Pure.Expr α)) (init : β) (f : β -> α -> β) : IO (Observer β) := do
  let node <- compileFoldArray state exprs init f
  Leancremental.observe node

/-- Compile a pure expression, observe it, and return the executable observer. -/
def observeExpr (state : State) (expr : Pure.Expr α) : IO (Observer α) := do
  let node <- compile state expr
  Leancremental.observe node

/-- The pure value that `compile` is intended to implement. -/
def expectedValue (expr : Pure.Expr α) : α :=
  Pure.eval expr

/-- The pure value that `compileFoldArray` is intended to implement. -/
def expectedFoldValue (exprs : Array (Pure.Expr α)) (init : β) (f : β -> α -> β) : β :=
  exprs.foldl (fun acc expr => f acc (Pure.eval expr)) init

/-- Evaluating the intended value of a compiled expression is just pure evaluation. -/
@[simp] theorem expectedValue_eq_eval (expr : Pure.Expr α) :
    expectedValue expr = Pure.eval expr := by
  rfl

/--
Certify an observed value against a pure expression.

This pure function is the proof-carrying half of the executable bridge: if a
runtime observation is equal to the expected pure value according to a lawful
`BEq`, it returns a `Pure.Snapshot` whose `sound` field proves the observed value
matches the pure model.
-/
def certifyValue [BEq α] [LawfulBEq α] (expr : Pure.Expr α) (value : α) : Except String (Pure.Snapshot α) :=
  let expected := expectedValue expr
  if h : value == expected then
    have value_eq_expected : value = expected := eq_of_beq h
    have sound : expr.eval = value := by
      rw [value_eq_expected]
      rfl
    .ok { model := expr, value := value, sound := sound }
  else
    .error "observed value did not match its pure model"

/-- Certify an observed fold value against the corresponding pure fold model. -/
def certifyFoldValue [BEq β] [LawfulBEq β]
    (exprs : Array (Pure.Expr α)) (init : β) (f : β -> α -> β) (value : β) : Except String (Pure.Snapshot β) :=
  let expected := expectedFoldValue exprs init f
  if h : value == expected then
    have value_eq_expected : value = expected := eq_of_beq h
    have sound : (Pure.Expr.foldArray exprs init f).eval = value := by
      rw [value_eq_expected]
      rfl
    .ok { model := Pure.Expr.foldArray exprs init f, value := value, sound := sound }
  else
    .error "observed fold value did not match its pure model"

/--
Compile, observe, stabilize, and check a pure expression against its pure model.

The returned value is an executable runtime observation. Use `certifyValue` on
that value to obtain a proof-carrying `Pure.Snapshot` in pure code.
Certification additionally requires a lawful `BEq` instance for `α`.
-/
def observeExprChecked [BEq α] (state : State) (expr : Pure.Expr α) : IO α := do
  let observer <- observeExpr state expr
  State.stabilize state
  let value <- Observer.value! observer
  if value == expectedValue expr then
    pure value
  else
    throw (IO.userError "compiled pure expression did not match its pure model")

/--
Compile, observe, stabilize, and check a pure fold against its pure model.

The returned value is an executable runtime observation. Use `certifyFoldValue`
on that value to obtain a proof-carrying `Pure.Snapshot` in pure code.
Certification additionally requires a lawful `BEq` instance for `β`.
-/
def observeFoldArrayChecked [BEq β]
    (state : State) (exprs : Array (Pure.Expr α)) (init : β) (f : β -> α -> β) : IO β := do
  let observer <- observeFoldArray state exprs init f
  State.stabilize state
  let value <- Observer.value! observer
  if value == expectedFoldValue exprs init f then
    pure value
  else
    throw (IO.userError "compiled pure fold did not match its pure model")

/-- Constant pure model for a stable value read from the executable core. -/
def stableValueModel (value : α) : Pure.Expr α :=
  Pure.const value

/--
Pure snapshot for a stable value read from the executable core.

This uses a trivial constant model; it does not relate the value to any
non-trivial computation graph.
-/
def stableValueSnapshot (value : α) : Pure.Snapshot α :=
  Pure.Snapshot.ofModel (stableValueModel value)

/-- The model built for a stable executable value evaluates back to that value. -/
@[simp] theorem stableValueModel_eval (value : α) :
    Pure.eval (stableValueModel value) = value := rfl

/-- The snapshot built for a stable executable value stores that value. -/
@[simp] theorem stableValueSnapshot_value (value : α) :
    (stableValueSnapshot value).value = value := rfl

end CoreSnapshot

end Leancremental
