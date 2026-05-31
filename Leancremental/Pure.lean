/-!
A small pure model for reasoning about stable incremental snapshots.

The executable engine in `Leancremental.Core` is intentionally `IO`-backed. This
module gives proofs a total, extensional expression language for the pure subset
of the API: constants, maps, binary maps, folds, and extensional bind.
-/

namespace Leancremental
namespace Pure

/-- A total expression language for the pure subset of Leancremental computations. -/
inductive Expr : Type -> Type 1 where
  /-- A constant expression. -/
  | const : α -> Expr α
  /-- A mapped expression. -/
  | map : Expr α -> (α -> β) -> Expr β
  /-- A binary mapped expression. -/
  | map2 : Expr α -> Expr β -> (α -> β -> γ) -> Expr γ

namespace Expr

/-- Evaluate a pure expression to its value. -/
def eval : Expr α -> α
  | .const value => value
  | .map expr f => f expr.eval
  | .map2 left right f => f left.eval right.eval

/-- Extensional bind for pure expressions. -/
def bind (expr : Expr α) (f : α -> Expr β) : Expr β :=
  f expr.eval

/-- Pair two pure expressions. -/
def both (left : Expr α) (right : Expr β) : Expr (α × β) :=
  .map2 left right (fun leftValue rightValue => (leftValue, rightValue))

/-- Fold an array of pure expressions into a constant expression. -/
def foldArray (exprs : Array (Expr α)) (init : β) (f : β -> α -> β) : Expr β :=
  .const (exprs.foldl (fun acc expr => f acc expr.eval) init)

/-- Collect the values of pure expressions into an array expression. -/
def all (exprs : Array (Expr α)) : Expr (Array α) :=
  foldArray exprs #[] (fun acc value => acc.push value)

/-- Return a pure expression that is true iff all input expressions evaluate to true. -/
def forAll (exprs : Array (Expr Bool)) : Expr Bool :=
  foldArray exprs true (fun acc value => acc && value)

/-- Return a pure expression that is true iff any input expression evaluates to true. -/
def existsAny (exprs : Array (Expr Bool)) : Expr Bool :=
  foldArray exprs false (fun acc value => acc || value)

/-- Sum pure `Nat` expressions. -/
def sumNat (exprs : Array (Expr Nat)) : Expr Nat :=
  foldArray exprs 0 (fun acc value => acc + value)

/-- Evaluating a pure constant returns its value. -/
@[simp] theorem eval_const (value : α) :
    (Expr.const value).eval = value := rfl

/-- Evaluating `map` applies the mapped function to the evaluated input. -/
@[simp] theorem eval_map (expr : Expr α) (f : α -> β) :
    (Expr.map expr f).eval = f expr.eval := rfl

/-- Evaluating `map2` applies the mapped function to the evaluated inputs. -/
@[simp] theorem eval_map2 (left : Expr α) (right : Expr β) (f : α -> β -> γ) :
    (Expr.map2 left right f).eval = f left.eval right.eval := rfl

/-- Evaluating `foldArray` folds over the evaluated inputs. -/
@[simp] theorem eval_foldArray (exprs : Array (Expr α)) (init : β) (f : β -> α -> β) :
  (Expr.foldArray exprs init f).eval = exprs.foldl (fun acc expr => f acc expr.eval) init := rfl

/-- Evaluating pure bind evaluates the expression selected by the input value. -/
@[simp] theorem eval_bind (expr : Expr α) (f : α -> Expr β) :
    (expr.bind f).eval = (f expr.eval).eval := rfl

/-- Evaluating `both` returns the pair of evaluated inputs. -/
@[simp] theorem eval_both (left : Expr α) (right : Expr β) :
    (left.both right).eval = (left.eval, right.eval) := rfl

/-- Mapping twice evaluates like ordinary function composition. -/
theorem eval_map_comp (expr : Expr α) (f : α -> β) (g : β -> γ) :
    ((expr.map f).map g).eval = g (f expr.eval) := rfl

end Expr

/-- Create a pure constant expression. -/
def const (value : α) : Expr α :=
  Expr.const value

/-- Map a function over a pure expression. -/
def map (expr : Expr α) (f : α -> β) : Expr β :=
  Expr.map expr f

/-- Map a binary function over two pure expressions. -/
def map2 (left : Expr α) (right : Expr β) (f : α -> β -> γ) : Expr γ :=
  Expr.map2 left right f

/-- Evaluate a pure expression. -/
def eval (expr : Expr α) : α :=
  expr.eval

/-- A pure variable modelled as an explicit value. -/
structure Var (α : Type) where
  /-- The variable's current pure value. -/
  value : α

namespace Var

/-- Watch a pure variable as a constant expression. -/
def watch (var : Var α) : Expr α :=
  Expr.const var.value

/-- Return a new pure variable value. -/
def set (var : Var α) (value : α) : Var α :=
  { var with value := value }

end Var

/-- A stable pure snapshot carrying a proof that its value matches its model. -/
structure Snapshot (α : Type) where
  /-- The pure model expression. -/
  model : Expr α
  /-- The stored snapshot value. -/
  value : α
  /-- Soundness proof connecting `value` to `model.eval`. -/
  sound : model.eval = value

namespace Snapshot

/-- Snapshot a pure expression by evaluating it. -/
def ofModel (model : Expr α) : Snapshot α :=
  { model := model, value := model.eval, sound := rfl }

/-- The stored snapshot value is equal to evaluating its model. -/
theorem value_eq_eval (snapshot : Snapshot α) :
    snapshot.value = snapshot.model.eval := by
  exact snapshot.sound.symm

end Snapshot

end Pure
end Leancremental
