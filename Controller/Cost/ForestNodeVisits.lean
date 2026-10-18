module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestGuardAccumulator
public import Mathlib.Data.List.Nodup

@[expose] public section

/-!
# Positional node visits, including shared terminals

The annotated unfolding supplies ghost witnesses only. Erasing its paths gives
an unannotated traversal specification. The list-count bounds do not assert that
runtime constructs annotated paths, or that nested flattening is a linear-time
RAM implementation.
-/
namespace Controller.Cost.ForestNodeVisits

open Controller.Decoder Controller.Cost.ForestOccurrences
open Controller.Cost.ForestGuardAccumulator

variable {n : ℕ}

/-- Root and child positions remain distinct even when endpoints coincide. -/
def walkGhost (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route) :
    List (NodeVisit graph) :=
  ⟨node, route, rooted⟩ ::
    (List.ofFn fun position : Fin (graph.node node).children.length =>
      walkGhost graph (graph.childIndex node ((graph.node node).children.get position))
        (.inr ⟨node, position⟩ :: route) (RootedPath.child node position route rooted)).flatten
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

theorem route_suffix (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (route : List graph.StoredOccurrence)
      (rooted : RootedPath graph node route) (visit : NodeVisit graph),
      visit ∈ walkGhost graph node route rooted → route <:+ visit.route := by
  have claim : ∀ rank : ℕ, ∀ (node : Fin graph.nodeCount), node.val = rank →
      ∀ (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
        (visit : NodeVisit graph),
        visit ∈ walkGhost graph node route rooted → route <:+ visit.route := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value route rooted visit present
      rw [walkGhost.eq_def] at present
      rcases List.mem_cons.mp present with equal | descendant
      · subst visit
        exact List.suffix_refl route
      · obtain ⟨block, blockPresent, visitPresent⟩ := List.mem_flatten.mp descendant
        obtain ⟨position, equal⟩ := List.mem_ofFn.mp blockPresent
        subst block
        have suffix := ih ((graph.node node).children.get position).val
          (by have earlier := graph.childIndex_lt node ((graph.node node).children.get position); omega)
          _ rfl _ _ visit visitPresent
        exact (List.suffix_cons _ route).trans suffix
  intro node route rooted visit present
  exact claim node.val node rfl route rooted visit present

private theorem equal_length_suffix {first second whole : List α}
    (firstSuffix : first <:+ whole) (secondSuffix : second <:+ whole)
    (lengths : first.length = second.length) : first = second :=
  (List.suffix_of_suffix_length_le firstSuffix secondSuffix lengths.le).eq_of_length lengths

def childrenGhost (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route) :
    List (NodeVisit graph) :=
  (List.ofFn fun position : Fin (graph.node node).children.length =>
    walkGhost graph (graph.childIndex node ((graph.node node).children.get position))
      (.inr ⟨node, position⟩ :: route) (RootedPath.child node position route rooted)).flatten

theorem own_not_mem_children (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route) :
    (⟨node, route, rooted⟩ : NodeVisit graph) ∉ childrenGhost graph node route rooted := by
  intro present
  obtain ⟨block, blockPresent, ownPresent⟩ := List.mem_flatten.mp present
  obtain ⟨position, equal⟩ := List.mem_ofFn.mp blockPresent
  subst block
  have suffix := route_suffix graph _ _ _ _ ownPresent
  have lengths := suffix.length_le
  simp only [List.length_cons] at lengths
  omega

theorem child_blocks_disjoint (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
    (first second : Fin (graph.node node).children.length) (different : first ≠ second) :
    List.Disjoint
      (walkGhost graph (graph.childIndex node ((graph.node node).children.get first))
        (.inr ⟨node, first⟩ :: route) (RootedPath.child node first route rooted))
      (walkGhost graph (graph.childIndex node ((graph.node node).children.get second))
        (.inr ⟨node, second⟩ :: route) (RootedPath.child node second route rooted)) := by
  apply List.disjoint_left.mpr
  intro visit firstPresent secondPresent
  have firstSuffix := route_suffix graph _ _ _ visit firstPresent
  have secondSuffix := route_suffix graph _ _ _ visit secondPresent
  have routes := equal_length_suffix firstSuffix secondSuffix rfl
  have heads := (List.cons.inj routes).1
  have positions : first = second := Fin.ext
    (congrArg (fun occurrence : graph.StoredOccurrence =>
      match occurrence with | .inl _ => 0 | .inr pair => pair.2.val) heads)
  exact different positions

theorem walk_nodup (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (route : List graph.StoredOccurrence)
      (rooted : RootedPath graph node route), (walkGhost graph node route rooted).Nodup := by
  classical
  have claim : ∀ rank : ℕ, ∀ (node : Fin graph.nodeCount), node.val = rank →
      ∀ (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route),
        (walkGhost graph node route rooted).Nodup := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value route rooted
      have childrenNodup : (childrenGhost graph node route rooted).Nodup := by
        apply List.nodup_flatten.mpr
        constructor
        · intro block blockPresent
          obtain ⟨position, equal⟩ := List.mem_ofFn.mp blockPresent
          subst block
          exact ih ((graph.node node).children.get position).val
            (by have earlier := graph.childIndex_lt node ((graph.node node).children.get position); omega)
            _ rfl _ _
        · apply List.pairwise_ofFn.mpr
          intro first second before
          exact child_blocks_disjoint graph node route rooted first second (ne_of_lt before)
      rw [walkGhost.eq_def]
      exact List.nodup_cons.mpr ⟨own_not_mem_children graph node route rooted, childrenNodup⟩
  intro node route rooted
  exact claim node.val node rfl route rooted

def rootGhost (graph : DAG n) : List (NodeVisit graph) :=
  (List.ofFn fun position : Fin graph.roots.length =>
    walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).flatten

theorem root_nodup (graph : DAG n) : (rootGhost graph).Nodup := by
  classical
  apply List.nodup_flatten.mpr
  constructor
  · intro block present
    obtain ⟨position, equal⟩ := List.mem_ofFn.mp present
    subst block
    exact walk_nodup graph _ _ _
  · apply List.pairwise_ofFn.mpr
    intro first second before
    apply List.disjoint_left.mpr
    intro visit firstPresent secondPresent
    have firstSuffix := route_suffix graph _ _ _ visit firstPresent
    have secondSuffix := route_suffix graph _ _ _ visit secondPresent
    have routes := equal_length_suffix firstSuffix secondSuffix rfl
    have positions : first = second := Sum.inl.inj (List.cons.inj routes).1
    exact (ne_of_lt before) positions

/-- All generated visits, including terminals, use the positional budget. -/
theorem root_length_le (graph : DAG n) (forest : graph.FormulaForest) :
    (rootGhost graph).length ≤ graph.roots.length + graph.childIncidences := by
  classical
  letI : Finite (NodeVisit graph) := Finite.of_injective
    (NodeVisit.incoming (graph := graph)) (incoming_injective graph forest)
  letI : Fintype (NodeVisit graph) := Fintype.ofFinite _
  have bound : (rootGhost graph).length ≤ Nat.card (NodeVisit graph) := by
    simpa only [Nat.card_eq_fintype_card] using (root_nodup graph).length_le_card
  exact bound.trans (node_visit_card_le graph forest)

/-- Unannotated node sequence; a specification, not an allocated runtime trace. -/
def walkNodes (graph : DAG n) (node : Fin graph.nodeCount) : List (Fin graph.nodeCount) :=
  node :: (graph.node node).children.flatMap (fun child =>
    walkNodes graph (graph.childIndex node child))
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

theorem walk_nodes (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (route : List graph.StoredOccurrence)
      (rooted : RootedPath graph node route),
      (walkGhost graph node route rooted).map NodeVisit.node = walkNodes graph node := by
  have claim : ∀ rank : ℕ, ∀ (node : Fin graph.nodeCount), node.val = rank →
      ∀ (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route),
        (walkGhost graph node route rooted).map NodeVisit.node = walkNodes graph node := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value route rooted
      rw [walkGhost.eq_def, walkNodes.eq_def, List.map_cons, List.map_flatten, List.map_ofFn]
      apply congrArg (List.cons node)
      have mapped : (List.ofFn fun position : Fin (graph.node node).children.length =>
          (walkGhost graph (graph.childIndex node ((graph.node node).children.get position))
            (.inr ⟨node, position⟩ :: route) (RootedPath.child node position route rooted)).map NodeVisit.node) =
          List.ofFn fun position : Fin (graph.node node).children.length =>
            walkNodes graph (graph.childIndex node ((graph.node node).children.get position)) := by
        apply congrArg List.ofFn
        funext position
        exact ih ((graph.node node).children.get position).val
          (by have earlier := graph.childIndex_lt node ((graph.node node).children.get position); omega)
          _ rfl _ _
      change (List.ofFn fun position : Fin (graph.node node).children.length =>
          (walkGhost graph (graph.childIndex node ((graph.node node).children.get position))
            (.inr ⟨node, position⟩ :: route) (RootedPath.child node position route rooted)).map NodeVisit.node).flatten = _
      rw [mapped]
      exact congrArg List.flatten (List.ofFn_getElem_eq_map (graph.node node).children
        (fun child => walkNodes graph (graph.childIndex node child)))
  intro node route rooted
  exact claim node.val node rfl route rooted

def rootNodes (graph : DAG n) : List (Fin graph.nodeCount) :=
  graph.roots.flatMap (walkNodes graph)

theorem root_nodes (graph : DAG n) : (rootGhost graph).map NodeVisit.node = rootNodes graph := by
  simp only [rootGhost, rootNodes, List.map_flatten, List.map_ofFn]
  have mapped : (List.ofFn fun position : Fin graph.roots.length =>
      (walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).map NodeVisit.node) =
      List.ofFn fun position : Fin graph.roots.length => walkNodes graph (graph.roots.get position) := by
    apply congrArg List.ofFn
    funext position
    exact walk_nodes graph _ _ _
  change (List.ofFn fun position : Fin graph.roots.length =>
      (walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).map NodeVisit.node).flatten = _
  rw [mapped]
  exact congrArg List.flatten (List.ofFn_getElem_eq_map graph.roots (walkNodes graph))

theorem root_node_count_le (graph : DAG n) (forest : graph.FormulaForest) :
    (rootNodes graph).length ≤ graph.roots.length + graph.childIncidences := by
  have counts := congrArg List.length (root_nodes graph)
  simp only [List.length_map] at counts
  rw [← counts]
  exact root_length_le graph forest

end Controller.Cost.ForestNodeVisits
