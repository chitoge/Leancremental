import Leancremental.Core.Snapshot

/-!
Pure expression shape facts for the spec-first compiler.

These lemmas give a small proof vocabulary for the constructors that
`CoreSnapshot.compile` mirrors in executable graph construction.
-/

namespace Leancremental
namespace Pure
namespace Expr

/-- Number of nodes in the pure expression tree. -/
def nodeCount : Expr α -> Nat
  | .const _ => 1
  | .map expr _ => expr.nodeCount + 1
  | .map2 left right _ => left.nodeCount + right.nodeCount + 1

/-- Node count for a runtime fold node over pure child expressions. -/
def foldNodeCount (exprs : Array (Expr α)) : Nat :=
  exprs.foldl (fun acc expr => acc + expr.nodeCount) 1

/-- Height of the pure expression tree. -/
def height : Expr α -> Nat
  | .const _ => 0
  | .map expr _ => expr.height + 1
  | .map2 left right _ => max left.height right.height + 1

/-- Height of a runtime fold node over pure child expressions. -/
def foldHeight (exprs : Array (Expr α)) : Nat :=
  if exprs.isEmpty then
    0
  else
    exprs.foldl (fun height expr => max height (expr.height + 1)) 0

/-- Constants have one pure expression node. -/
@[simp] theorem nodeCount_const (value : α) :
    (Expr.const value).nodeCount = 1 := rfl

/-- Mapping adds one pure expression node above its child. -/
@[simp] theorem nodeCount_map (expr : Expr α) (f : α -> β) :
    (Expr.map expr f).nodeCount = expr.nodeCount + 1 := rfl

/-- Binary mapping adds one pure expression node above both children. -/
@[simp] theorem nodeCount_map2 (left : Expr α) (right : Expr β) (f : α -> β -> γ) :
    (Expr.map2 left right f).nodeCount = left.nodeCount + right.nodeCount + 1 := rfl

/-- A runtime fold node count is one plus all child expression node counts. -/
@[simp] theorem foldNodeCount_eq (exprs : Array (Expr α)) :
  foldNodeCount exprs = exprs.foldl (fun acc expr => acc + expr.nodeCount) 1 := rfl

/-- Constants have pure expression height zero. -/
@[simp] theorem height_const (value : α) :
    (Expr.const value).height = 0 := rfl

/-- Mapping places the parent one level above its child. -/
@[simp] theorem height_map (expr : Expr α) (f : α -> β) :
    (Expr.map expr f).height = expr.height + 1 := rfl

/-- Binary mapping places the parent one level above the maximum child height. -/
@[simp] theorem height_map2 (left : Expr α) (right : Expr β) (f : α -> β -> γ) :
    (Expr.map2 left right f).height = max left.height right.height + 1 := rfl

/-- A runtime fold node has the height computed from its child expressions. -/
@[simp] theorem foldHeight_eq (exprs : Array (Expr α)) :
    foldHeight exprs = if exprs.isEmpty then 0 else exprs.foldl (fun height expr => max height (expr.height + 1)) 0 := by
  simp [foldHeight]

/-- Every pure expression contains at least one node. -/
theorem nodeCount_pos : ∀ (expr : Expr α), 0 < expr.nodeCount
  | .const _ => by simp [nodeCount]
  | .map expr _ => by simp [nodeCount]
  | .map2 left right _ => by simp [nodeCount]

/-- A mapped expression is higher than its child. -/
theorem height_map_child_lt (expr : Expr α) (f : α -> β) :
    expr.height < (Expr.map expr f).height := by
  simp [height]

/-- A binary mapped expression is higher than its left child. -/
theorem height_map2_left_lt (left : Expr α) (right : Expr β) (f : α -> β -> γ) :
    left.height < (Expr.map2 left right f).height := by
  simp [height]
  exact Nat.lt_succ_of_le (Nat.le_max_left left.height right.height)

/-- A binary mapped expression is higher than its right child. -/
theorem height_map2_right_lt (left : Expr α) (right : Expr β) (f : α -> β -> γ) :
    right.height < (Expr.map2 left right f).height := by
  simp [height]
  exact Nat.lt_succ_of_le (Nat.le_max_right left.height right.height)

end Expr
end Pure

namespace CoreSnapshot

/-- The expected value of a compiled constant is the constant. -/
@[simp] theorem expectedValue_const (value : α) :
    expectedValue (Pure.const value) = value := rfl

/-- The expected value of a compiled map is the mapped pure value. -/
@[simp] theorem expectedValue_map (expr : Pure.Expr α) (f : α -> β) :
    expectedValue (Pure.map expr f) = f (Pure.eval expr) := rfl

/-- The expected value of a compiled binary map is the mapped pair of pure values. -/
@[simp] theorem expectedValue_map2 (left : Pure.Expr α) (right : Pure.Expr β) (f : α -> β -> γ) :
    expectedValue (Pure.map2 left right f) = f (Pure.eval left) (Pure.eval right) := rfl

/-- The expected value of a compiled fold is the pure fold over evaluated inputs. -/
@[simp] theorem expectedFoldValue_eq (exprs : Array (Pure.Expr α)) (init : β) (f : β -> α -> β) :
  expectedFoldValue exprs init f = exprs.foldl (fun acc expr => f acc (Pure.eval expr)) init := rfl

/-- Certification succeeds for a value that is definitionally the expected pure value. -/
@[simp] theorem certifyValue_expected_isOk [BEq α] [LawfulBEq α] (expr : Pure.Expr α) :
    (certifyValue expr (expectedValue expr)).isOk = true := by
  simp [certifyValue, Except.isOk, Except.toBool]

/-- Fold certification succeeds for a value that is definitionally the expected pure fold value. -/
@[simp] theorem certifyFoldValue_expected_isOk [BEq β] [LawfulBEq β]
    (exprs : Array (Pure.Expr α)) (init : β) (f : β -> α -> β) :
    (certifyFoldValue exprs init f (expectedFoldValue exprs init f)).isOk = true := by
  simp [certifyFoldValue, Except.isOk, Except.toBool]

end CoreSnapshot
end Leancremental
