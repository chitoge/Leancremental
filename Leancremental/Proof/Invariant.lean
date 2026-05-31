import Leancremental.Core.Invariant

/-!
Proof-oriented graph invariants for Leancremental metadata.

`Leancremental.Core.Invariant` provides executable checkers. This module gives
names to the corresponding proof concepts so later preservation theorems can talk
about graph metadata directly.
-/

namespace Leancremental
namespace Proof
namespace Invariant

/-- A child edge together with the metadata snapshots for both endpoints. -/
structure ChildEdge (infos : Array NodeInfo) (parent child : Nat) where
  /-- Metadata for the parent node. -/
  parentInfo : NodeInfo
  /-- Metadata for the child node. -/
  childInfo : NodeInfo
  /-- Lookup proof for the parent metadata. -/
  parent_lookup : infos[parent]? = some parentInfo
  /-- Lookup proof for the child metadata. -/
  child_lookup : infos[child]? = some childInfo
  /-- The child id occurs in the parent's child list. -/
  child_mem : child ∈ parentInfo.children.toList

/-- Prop-level graph invariants represented by Leancremental's current `NodeInfo`. -/
structure GraphInvariant (infos : Array NodeInfo) : Prop where
  /-- Node metadata ids agree with their array indices. -/
  ids_match : ∀ {id : Nat} {info : NodeInfo}, infos[id]? = some info -> info.id = id
  /-- Every child edge has the reverse parent edge. -/
  parent_child_symmetric :
    ∀ {parent child : Nat} (edge : ChildEdge infos parent child),
      CoreInvariant.containsId edge.childInfo.parents parent = true
  /-- Every recorded parent edge has the reverse child edge. -/
  child_parent_symmetric :
    ∀ {parent child : Nat} {parentInfo childInfo : NodeInfo},
      infos[parent]? = some parentInfo ->
      infos[child]? = some childInfo ->
      CoreInvariant.containsId childInfo.parents parent = true ->
      CoreInvariant.containsId parentInfo.children child = true
  /-- Every child is lower than its parent in the recomputation height order. -/
  height_ordered :
    ∀ {parent child : Nat} (edge : ChildEdge infos parent child),
      edge.childInfo.height < edge.parentInfo.height
  /-- Necessary parents make their children necessary. -/
  necessary_closed :
    ∀ {parent child : Nat} (edge : ChildEdge infos parent child),
      edge.parentInfo.necessary = true -> edge.childInfo.necessary = true
  /-- Change timestamps are not later than recomputation timestamps. -/
  timestamps_ordered :
    ∀ {id : Nat} {info : NodeInfo}, infos[id]? = some info ->
      CoreInvariant.timestampsOrdered info = true

/-- Stable graph invariants expected after a successful stabilization. -/
structure StableGraphInvariant (infos : Array NodeInfo) : Prop extends GraphInvariant infos where
  /-- Necessary nodes are not stale after stabilization. -/
  necessary_not_stale :
    ∀ {id : Nat} {info : NodeInfo}, infos[id]? = some info ->
      info.necessary = true -> info.stale = false

namespace GraphInvariant

/-- Child-edge height ordering as a standalone theorem. -/
theorem child_height_lt {infos : Array NodeInfo} (h : GraphInvariant infos)
    {parent child : Nat} (edge : ChildEdge infos parent child) :
    edge.childInfo.height < edge.parentInfo.height :=
  h.height_ordered edge

/-- Necessary parents have necessary children. -/
theorem child_necessary {infos : Array NodeInfo} (h : GraphInvariant infos)
    {parent child : Nat} (edge : ChildEdge infos parent child)
    (necessary : edge.parentInfo.necessary = true) :
    edge.childInfo.necessary = true :=
  h.necessary_closed edge necessary

/-- Metadata timestamps are ordered for any node lookup. -/
theorem timestamps {infos : Array NodeInfo} (h : GraphInvariant infos)
    {id : Nat} {info : NodeInfo} (lookup : infos[id]? = some info) :
    CoreInvariant.timestampsOrdered info = true :=
  h.timestamps_ordered lookup

end GraphInvariant

namespace StableGraphInvariant

/-- Necessary nodes are stable according to their stale flag. -/
theorem not_stale {infos : Array NodeInfo} (h : StableGraphInvariant infos)
    {id : Nat} {info : NodeInfo} (lookup : infos[id]? = some info)
    (necessary : info.necessary = true) :
    info.stale = false :=
  h.necessary_not_stale lookup necessary

end StableGraphInvariant

/-- A nonempty path following child edges. -/
inductive ChildPath (infos : Array NodeInfo) : Nat -> Nat -> Prop where
  /-- A single child edge is a path. -/
  | edge {parent child : Nat} : ChildEdge infos parent child -> ChildPath infos parent child
  /-- A child edge followed by a path is a path. -/
  | cons {parent mid child : Nat} :
      ChildEdge infos parent mid -> ChildPath infos mid child -> ChildPath infos parent child

namespace ChildPath

/-- Along any child path, the endpoint height is strictly smaller than the start height. -/
theorem height_lt {infos : Array NodeInfo} (h : GraphInvariant infos) :
    ∀ {parent child : Nat}, ChildPath infos parent child ->
      ∃ parentInfo childInfo,
        infos[parent]? = some parentInfo ∧
        infos[child]? = some childInfo ∧
        childInfo.height < parentInfo.height := by
  intro parent child path
  induction path with
  | edge edge =>
      exact ⟨edge.parentInfo, edge.childInfo, edge.parent_lookup, edge.child_lookup,
        h.height_ordered edge⟩
  | cons edge tail ih =>
      rcases ih with ⟨midInfo, childInfo, mid_lookup, child_lookup, child_lt_mid⟩
      have mid_eq : edge.childInfo = midInfo := by
        rw [edge.child_lookup] at mid_lookup
        injection mid_lookup
      have child_lt_edge_child : childInfo.height < edge.childInfo.height := by
        simpa [mid_eq] using child_lt_mid
      exact
        ⟨edge.parentInfo, childInfo, edge.parent_lookup, child_lookup,
          Nat.lt_trans child_lt_edge_child (h.height_ordered edge)⟩

end ChildPath

/-- Strict height ordering rules out child-edge cycles. -/
theorem no_child_cycle_of_height_order {infos : Array NodeInfo}
    (h : GraphInvariant infos) {id : Nat} (path : ChildPath infos id id) : False := by
  rcases ChildPath.height_lt h path with ⟨parentInfo, childInfo, parent_lookup, child_lookup, height_lt⟩
  have same_info : parentInfo = childInfo := by
    rw [parent_lookup] at child_lookup
    injection child_lookup
  have impossible : childInfo.height < childInfo.height := by
    cases same_info
    exact height_lt
  exact Nat.lt_irrefl childInfo.height impossible

/-- Boolean checker success means the executable basic violation list is empty. -/
theorem infoInvariant_no_violations {infos : Array NodeInfo}
    (h : CoreInvariant.infoInvariant infos = true) :
    (CoreInvariant.infoViolations false infos).isEmpty = true := by
  simpa [CoreInvariant.infoInvariant] using h

/-- Boolean checker success means the executable stable violation list is empty. -/
theorem stableInfoInvariant_no_violations {infos : Array NodeInfo}
    (h : CoreInvariant.stableInfoInvariant infos = true) :
    (CoreInvariant.infoViolations true infos).isEmpty = true := by
  simpa [CoreInvariant.stableInfoInvariant] using h

/-- If there is no change timestamp, timestamp ordering holds. -/
@[simp] theorem timestampsOrdered_changed_none (info : NodeInfo) :
    CoreInvariant.timestampsOrdered { info with changedAt := none } = true := by
  cases info.computedAt <;> rfl

/-- A present change timestamp without a recomputation timestamp violates ordering. -/
@[simp] theorem timestampsOrdered_some_none (info : NodeInfo) (changed : Nat) :
    CoreInvariant.timestampsOrdered { info with changedAt := some changed, computedAt := none } = false := rfl

/-- With both timestamps present, ordering is ordinary natural-number ordering. -/
theorem timestampsOrdered_some_some_iff (info : NodeInfo) (changed computed : Nat) :
    CoreInvariant.timestampsOrdered { info with changedAt := some changed, computedAt := some computed } = true ↔
      changed ≤ computed := by
  simp [CoreInvariant.timestampsOrdered]

end Invariant
end Proof
end Leancremental
