module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Forest
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Positional paths in internal-use forests

The forest promise counts incoming root and child positions. It gives uniqueness
of rooted paths to internal nodes, while allowing shared terminals and repeated
channel labels. These structural bounds do not constitute a machine traversal
cost theorem.
-/
namespace Controller.Cost.ForestOccurrences

open Controller.Decoder

variable {n : ℕ}

/-- Every active use of one internal node is the same positional occurrence. -/
theorem active_use_unique (graph : DAG n) (forest : graph.FormulaForest)
    (node : Fin graph.nodeCount) (internal : (graph.node node).isInternal = true)
    (first second : graph.ActiveUses (graph.cones graph.roots) node) : first = second := by
  have cardinality : Fintype.card (graph.ActiveUses (graph.cones graph.roots) node) ≤ 1 := by
    simpa only [Nat.card_eq_fintype_card] using forest.2 node internal
  letI : Subsingleton (graph.ActiveUses (graph.cones graph.roots) node) :=
    Fintype.card_le_one_iff_subsingleton.mp cardinality
  exact Subsingleton.elim first second

/-- Equality of the underlying positions, retaining repeated child incidences. -/
theorem active_occurrence_unique (graph : DAG n) (forest : graph.FormulaForest)
    (node : Fin graph.nodeCount) (internal : (graph.node node).isInternal = true)
    (first second : graph.StoredOccurrence)
    (firstActive : graph.parentRetained (graph.cones graph.roots) first)
    (secondActive : graph.parentRetained (graph.cones graph.roots) second)
    (firstRefers : graph.refers first = node) (secondRefers : graph.refers second = node) :
    first = second := by
  have equal := active_use_unique graph forest node internal
    ⟨first, firstActive, firstRefers⟩ ⟨second, secondActive, secondRefers⟩
  exact congrArg Subtype.val equal

/-- A represented parent with a child position must be internal. -/
theorem parent_internal (graph : DAG n) (parent : Fin graph.nodeCount)
    (position : Fin (graph.node parent).children.length) :
    (graph.node parent).isInternal = true := by
  have valid := position.isLt
  cases equation : graph.node parent <;>
    simp_all [Gate.children, Gate.isInternal]

/-- A reversed list of stored positions from a root to the specified endpoint. -/
inductive RootedPath (graph : DAG n) :
    Fin graph.nodeCount → List graph.StoredOccurrence → Prop where
  | root (position : Fin graph.roots.length) :
      RootedPath graph (graph.roots.get position) [.inl position]
  | child (parent : Fin graph.nodeCount)
      (position : Fin (graph.node parent).children.length)
      (ancestorRoute : List graph.StoredOccurrence) (path : RootedPath graph parent ancestorRoute) :
      RootedPath graph (graph.childIndex parent ((graph.node parent).children.get position))
        (.inr ⟨parent, position⟩ :: ancestorRoute)

namespace RootedPath

theorem endpoint_mem_cones {graph : DAG n} {node : Fin graph.nodeCount}
    {route : List graph.StoredOccurrence} (path : RootedPath graph node route) :
    node ∈ graph.cones graph.roots := by
  induction path with
  | root position => exact graph.root_mem_cones graph.roots _ (List.get_mem _ _)
  | child parent position ancestorRoute path ih =>
      exact graph.cones_childClosed graph.roots parent ih _ (List.get_mem _ _)

theorem nonempty {graph : DAG n} {node : Fin graph.nodeCount}
    {route : List graph.StoredOccurrence} (path : RootedPath graph node route) :
    route ≠ [] := by
  cases path <;> simp

/-- Internal endpoints have one rooted positional path over all output roots. -/
theorem unique_internal (graph : DAG n) (forest : graph.FormulaForest) :
    ∀ (node : Fin graph.nodeCount) (first second : List graph.StoredOccurrence),
      (graph.node node).isInternal = true →
      RootedPath graph node first → RootedPath graph node second → first = second := by
  have claim : ∀ rank : ℕ, ∀ (firstNode secondNode : Fin graph.nodeCount),
      graph.nodeCount - firstNode.val = rank → firstNode = secondNode →
      ∀ (first second : List graph.StoredOccurrence),
        (graph.node firstNode).isInternal = true →
        RootedPath graph firstNode first → RootedPath graph secondNode second → first = second := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro firstNode secondNode rankEquation endpointEqual first second internal firstPath secondPath
      cases firstPath with
      | root firstPosition =>
        cases secondPath with
        | root secondPosition =>
          have positions := active_occurrence_unique graph forest _ internal
            (.inl firstPosition) (.inl secondPosition) trivial trivial rfl endpointEqual.symm
          have equal := Sum.inl.inj positions
          cases equal
          rfl
        | child parent position ancestorRoute path =>
          have positions := active_occurrence_unique graph forest _ internal
            (.inl firstPosition) (.inr ⟨parent, position⟩) trivial
            (path.endpoint_mem_cones) rfl endpointEqual.symm
          cases positions
      | child firstParent firstPosition firstPrefix firstPath =>
        cases secondPath with
        | root secondPosition =>
          have positions := active_occurrence_unique graph forest _ internal
            (.inr ⟨firstParent, firstPosition⟩) (.inl secondPosition)
            firstPath.endpoint_mem_cones trivial rfl endpointEqual.symm
          cases positions
        | child secondParent secondPosition secondPrefix secondPath =>
          have positions := active_occurrence_unique graph forest _ internal
            (.inr ⟨firstParent, firstPosition⟩) (.inr ⟨secondParent, secondPosition⟩)
            firstPath.endpoint_mem_cones secondPath.endpoint_mem_cones rfl endpointEqual.symm
          have parentEqual : firstParent = secondParent :=
            congrArg Sigma.fst (Sum.inr.inj positions)
          subst secondParent
          have positionEqual : firstPosition = secondPosition := by
            exact congrArg (fun pair : graph.ParentOccurrence => pair.2.val)
              (Sum.inr.inj positions) |> Fin.ext
          subst secondPosition
          have decrease : graph.nodeCount - firstParent.val < rank := by
            have earlier := graph.childIndex_lt firstParent
              ((graph.node firstParent).children.get firstPosition)
            omega
          have prefixes := ih _ decrease firstParent firstParent rfl rfl firstPrefix secondPrefix
            (parent_internal graph firstParent firstPosition) firstPath secondPath
          exact congrArg (List.cons (.inr ⟨firstParent, firstPosition⟩)) prefixes
  intro node first second internal firstPath secondPath
  exact claim _ node node rfl rfl first second internal firstPath secondPath

/-- The cardinality bound is structural; it does not charge an execution. -/
theorem internal_route_card_le_one (graph : DAG n) (forest : graph.FormulaForest)
    (node : Fin graph.nodeCount) (internal : (graph.node node).isInternal = true) :
    Nat.card {route : List graph.StoredOccurrence // RootedPath graph node route} ≤ 1 := by
  letI : Subsingleton {route : List graph.StoredOccurrence // RootedPath graph node route} :=
    ⟨fun first second => Subtype.ext
      (unique_internal graph forest node first.val second.val internal first.property second.property)⟩
  letI : Fintype {route : List graph.StoredOccurrence // RootedPath graph node route} :=
    Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_le_one_iff_subsingleton.mpr (inferInstance :
      Subsingleton {route : List graph.StoredOccurrence // RootedPath graph node route}))

end RootedPath
end Controller.Cost.ForestOccurrences
