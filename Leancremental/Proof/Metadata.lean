import Leancremental.Core.Invariant

/-!
Pure metadata constructors used as proof targets for the executable graph builder.

These are not a replacement for the `IO.Ref` runtime. They are small, total
models of the metadata updates performed by node constructors, useful for proving
local preservation facts before lifting them to the executable state.
-/

namespace Leancremental
namespace Proof
namespace Metadata

/-- Minimal metadata for a node with explicitly supplied children and height. -/
def nodeInfo
    (id : Nat)
    (kind : NodeKind)
    (height : Nat)
    (children parents : Array Nat)
    (necessary stale : Bool) : NodeInfo :=
  { id := id,
    kind := kind,
    height := height,
    children := children,
    parents := parents,
    necessary := necessary,
    stale := stale,
    valid := true,
    computedAt := none,
    changedAt := none,
    visitingAt := none,
    lastAccessedAt := none,
    externalDirtyReason := none,
    tags := #[] }

/-- Metadata for a leaf node such as `const` or `var`. -/
def leaf (id : Nat) (kind : NodeKind) (necessary stale : Bool := false) : NodeInfo :=
  nodeInfo id kind 0 #[] #[] necessary stale

/-- Metadata for a unary node whose height is one above its child. -/
def unary
    (id : Nat)
    (kind : NodeKind)
    (childId : Nat)
    (child : NodeInfo)
    (necessary stale : Bool := false) : NodeInfo :=
  nodeInfo id kind (child.height + 1) #[childId] #[] necessary stale

/-- Metadata for a binary node whose height is one above the maximum child height. -/
def binary
    (id : Nat)
    (kind : NodeKind)
    (leftId rightId : Nat)
    (left right : NodeInfo)
    (necessary stale : Bool := false) : NodeInfo :=
  nodeInfo id kind (max left.height right.height + 1) #[leftId, rightId] #[] necessary stale

/-- Fresh metadata starts with ordered timestamps. -/
@[simp] theorem nodeInfo_timestampsOrdered
    (id height : Nat) (kind : NodeKind) (children parents : Array Nat)
    (necessary stale : Bool) :
    CoreInvariant.timestampsOrdered (nodeInfo id kind height children parents necessary stale) = true := rfl

/-- Leaf metadata has height zero. -/
@[simp] theorem leaf_height (id : Nat) (kind : NodeKind) (necessary stale : Bool) :
    (leaf id kind necessary stale).height = 0 := rfl

/-- Unary metadata is higher than its child. -/
theorem unary_child_height_lt
    (id childId : Nat) (kind : NodeKind) (child : NodeInfo)
    (necessary stale : Bool) :
    child.height < (unary id kind childId child necessary stale).height := by
  simp [unary, nodeInfo]

/-- Binary metadata is higher than its left child. -/
theorem binary_left_height_lt
    (id leftId rightId : Nat) (kind : NodeKind) (left right : NodeInfo)
    (necessary stale : Bool) :
    left.height < (binary id kind leftId rightId left right necessary stale).height := by
  simp [binary, nodeInfo]
  exact Nat.lt_succ_of_le (Nat.le_max_left left.height right.height)

/-- Binary metadata is higher than its right child. -/
theorem binary_right_height_lt
    (id leftId rightId : Nat) (kind : NodeKind) (left right : NodeInfo)
    (necessary stale : Bool) :
    right.height < (binary id kind leftId rightId left right necessary stale).height := by
  simp [binary, nodeInfo]
  exact Nat.lt_succ_of_le (Nat.le_max_right left.height right.height)

/-- Necessary unary metadata should only be formed over a necessary child. -/
def UnaryNecessaryPreserved (parent child : NodeInfo) : Prop :=
  parent.necessary = true -> child.necessary = true

/-- Necessary binary metadata should only be formed over necessary children. -/
def BinaryNecessaryPreserved (parent left right : NodeInfo) : Prop :=
  parent.necessary = true -> left.necessary = true ∧ right.necessary = true

/-- Unary construction preserves necessary closure when the child is already necessary. -/
theorem unary_necessary_preserved
    (id childId : Nat) (kind : NodeKind) (child : NodeInfo) (stale : Bool)
    (childNecessary : child.necessary = true) :
    UnaryNecessaryPreserved (unary id kind childId child true stale) child := by
  intro _
  exact childNecessary

/-- Binary construction preserves necessary closure when both children are already necessary. -/
theorem binary_necessary_preserved
    (id leftId rightId : Nat) (kind : NodeKind) (left right : NodeInfo) (stale : Bool)
    (leftNecessary : left.necessary = true)
    (rightNecessary : right.necessary = true) :
    BinaryNecessaryPreserved (binary id kind leftId rightId left right true stale) left right := by
  intro _
  exact ⟨leftNecessary, rightNecessary⟩

end Metadata
end Proof
end Leancremental
