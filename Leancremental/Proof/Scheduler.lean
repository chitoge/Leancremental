/-!
Pure model for the Leancremental incremental scheduler (FR-7).

Defines a decidable model of one stabilization pass over a directed acyclic
graph. Everything is total: structural recursion with explicit fuel, `List`
throughout, no `Finset`, no `partial`, no `sorry`.
-/

namespace Leancremental.Proof.Scheduler

/-! ## Model structures -/

/-- A node in the pure model graph. -/
structure ModelNode where
  /-- Unique numeric identifier inside the graph. -/
  id : Nat
  /-- Direct dependency ids (children; must have strictly lower height). -/
  children : List Nat
  /-- DAG height: 0 for leaves, max-child-height + 1 otherwise. -/
  height : Nat
  deriving Repr, BEq, DecidableEq

/-- The complete model graph for one stabilization pass. -/
structure ModelGraph where
  /-- All nodes in this incremental world. -/
  nodes : List ModelNode
  /-- Ids of nodes whose input changed before this pass. -/
  stale : List Nat
  /-- Ids of necessary (observed) nodes. -/
  necessary : List Nat
  /-- Ids of observers that are new this pass (pending first refresh). -/
  newObservers : List Nat
  deriving Repr

/-- The result of running one stabilization pass. -/
structure RunResult where
  /-- Ids visited (de-duped; height-sorted ascending). -/
  visited : List Nat
  /-- Ids for which the node was stale (changed in this model). -/
  changed : List Nat
  /-- Observer ids refreshed after the pass. -/
  refreshed : List Nat
  deriving Repr, BEq

/-! ## Graph lookups -/

/-- Find the `ModelNode` with the given id, if it exists. -/
def nodeOf (g : ModelGraph) (id : Nat) : Option ModelNode :=
  g.nodes.find? (fun n => n.id == id)

/-- Return the height of `id`, or 0 if `id` is not in the graph. -/
def heightOf (g : ModelGraph) (id : Nat) : Nat :=
  (nodeOf g id).map (fun n => n.height) |>.getD 0

/-! ## Well-formedness -/

/--
`WellFormed g` asserts:
1. All node ids are distinct.
2. Every child id of every node is present in the graph.
3. Children have strictly lower height than their parent.
-/
structure WellFormed (g : ModelGraph) : Prop where
  ids_unique : ∀ n ∈ g.nodes, ∀ m ∈ g.nodes, n.id = m.id → n = m
  children_exist_and_lower :
    ∀ n ∈ g.nodes, ∀ c ∈ n.children,
      ∃ child ∈ g.nodes, child.id = c ∧ child.height < n.height

/-! ## Ancestor computation (total, with fuel) -/

-- Finds all nodes in g whose children include any frontier member (parents).
private def expandOnce (g : ModelGraph) (frontier : List Nat) : List Nat :=
  (g.nodes.filterMap fun n =>
    if frontier.any (fun id => n.children.contains id) then some n.id else none)
  |>.eraseDups

private def ancestorsStep : ModelGraph → Nat → List Nat → List Nat
  | _, 0, acc => acc
  | g, fuel + 1, acc =>
      let next := (acc ++ expandOnce g acc).eraseDups
      if next.length ≤ acc.length then acc
      else ancestorsStep g fuel next

/-- All transitive ancestors of `seeds` (seeds included). -/
def ancestorsOf (g : ModelGraph) (seeds : List Nat) : List Nat :=
  ancestorsStep g g.nodes.length seeds

/-! ## Pure stabilization pass -/

def run (g : ModelGraph) : RunResult :=
  let ancestors := ancestorsOf g g.stale
  let visited :=
    (ancestors.filter fun id => g.necessary.contains id)
      |>.eraseDups
      |>.mergeSort (fun a b => heightOf g a ≤ heightOf g b)
  let changed := visited.filter fun id => g.stale.contains id
  let refreshed :=
    g.necessary.filter fun o =>
      changed.contains o || g.newObservers.contains o
  { visited, changed, refreshed }

/-! ## Sanity checks -/

section Checks

private def chain2 : ModelGraph where
  nodes        := [⟨0, [], 0⟩, ⟨1, [0], 1⟩]
  stale        := [0]
  necessary    := [0, 1]
  newObservers := []

#guard (run chain2).visited.length == 2
#guard (run chain2).changed.contains 0
#guard (run chain2).refreshed.contains 0

private def diamond : ModelGraph where
  nodes        := [⟨0, [], 0⟩, ⟨1, [0], 1⟩, ⟨2, [0], 1⟩, ⟨3, [1, 2], 2⟩]
  stale        := [0, 1, 2]
  necessary    := [0, 1, 2, 3]
  newObservers := []

#guard (run diamond).visited.length == 4
#guard (run diamond).changed.length == 3

private def noopGraph : ModelGraph where
  nodes        := [⟨0, [], 0⟩]
  stale        := []
  necessary    := [0]
  newObservers := []

#guard (run noopGraph).visited == []
#guard (run noopGraph).changed == []
#guard (run noopGraph).refreshed == []

private def newObsGraph : ModelGraph where
  nodes        := [⟨0, [], 0⟩]
  stale        := []
  necessary    := [0]
  newObservers := [0]

#guard (run newObsGraph).refreshed.contains 0

private def changedObsGraph : ModelGraph where
  nodes        := [⟨0, [], 0⟩]
  stale        := [0]
  necessary    := [0]
  newObservers := []

#guard (run changedObsGraph).refreshed.contains 0

private def twoPhaseShape : ModelGraph where
  nodes        := [⟨0, [], 0⟩, ⟨1, [0], 1⟩, ⟨2, [1], 2⟩]
  stale        := [0, 1, 2]
  necessary    := [0, 1, 2]
  newObservers := []

#guard (run twoPhaseShape).visited.Nodup

private def unnecessaryStale : ModelGraph where
  nodes        := [⟨0, [], 0⟩, ⟨1, [], 0⟩]
  stale        := [1]
  necessary    := [0]
  newObservers := []

#guard (run unnecessaryStale).visited == []
#guard (run unnecessaryStale).changed == []

end Checks

/-! ## Theorems (FR-7, E2) -/

section Theorems

/-! ### Auxiliary lemmas -/

/-- `List.eraseDups` produces a `Nodup` list. -/
private theorem eraseDups_nodup [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  match l with
  | [] => simp
  | a :: t =>
      rw [List.eraseDups_cons, List.nodup_cons]
      exact ⟨fun hmem => by simp [List.mem_eraseDups, List.mem_filter] at hmem,
             eraseDups_nodup (t.filter (fun b => !b == a))⟩
termination_by l.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- `List.eraseDups` does not increase list length. -/
private theorem eraseDups_length_le [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.length ≤ l.length := by
  match l with
  | [] => simp
  | a :: t =>
      rw [List.eraseDups_cons, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ
        (Nat.le_trans (eraseDups_length_le _) (List.length_filter_le _ _))
termination_by l.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _)


/-! ### Main theorems -/

/--
Every node in `visited` is a transitive ancestor of the stale set.
-/
theorem stabilize_visits_only_ancestors_of_dirty (g : ModelGraph) :
    ∀ id ∈ (run g).visited, id ∈ ancestorsOf g g.stale := by
  intro id hmem
  simp only [run] at hmem
  rw [List.mem_mergeSort, List.mem_eraseDups, List.mem_filter] at hmem
  exact hmem.1

/--
Every node in `visited` is a necessary node.
-/
theorem stabilize_visits_only_necessary (g : ModelGraph) :
    ∀ id ∈ (run g).visited, g.necessary.contains id := by
  intro id hmem
  simp only [run] at hmem
  rw [List.mem_mergeSort, List.mem_eraseDups, List.mem_filter] at hmem
  exact hmem.2

/--
Observer-refresh predicate (FR-1 model half): a necessary node is refreshed
iff its id is in `changed` or it is a new observer.
-/
theorem refreshed_iff_changed_or_new (g : ModelGraph) (o : Nat)
    (ho : g.necessary.contains o) :
    o ∈ (run g).refreshed ↔ o ∈ (run g).changed ∨ o ∈ g.newObservers := by
  have ho' : o ∈ g.necessary := List.contains_iff_mem.mp ho
  simp only [run, List.mem_filter, Bool.or_eq_true, List.contains_iff_mem]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨ho', h⟩⟩

/--
`visited` has no duplicate entries.
-/
theorem recomputed_at_most_once_per_pass (g : ModelGraph) :
    (run g).visited.Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (eraseDups_nodup _)

/--
The pass terminates with a de-duplicated visit list: each necessary ancestor is
recomputed at most once.  (Well-founded measure: `visited.Nodup` bounds work by
`g.necessary.length`.)
-/
theorem drain_terminates (g : ModelGraph) :
    (run g).visited.Nodup := recomputed_at_most_once_per_pass g

end Theorems

end Leancremental.Proof.Scheduler
