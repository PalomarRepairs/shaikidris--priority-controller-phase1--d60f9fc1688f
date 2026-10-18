module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestOccurrences
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Guard-position charging in formula forests

A visit carries its rooted positional path, its stored guard-label position and
its entry/exit phase. Distinct positions are retained when channel labels repeat.
Projection to stored positions bounds the universe of possible visits; a
complete traversal resource theorem also needs its generated-list refinement.
-/
namespace Controller.Cost.ForestGuardCharging

open Controller.Decoder Controller.Cost.ForestOccurrences

variable {n : ℕ}

abbrev GuardPosition (graph : DAG n) :=
  Σ node : Fin graph.nodeCount, Fin (graph.node node).guardLabels.length

abbrev GuardKey (graph : DAG n) := GuardPosition graph × Bool

instance guardKeyFintype (graph : DAG n) : Fintype (GuardKey graph) := by
  dsimp [GuardKey, GuardPosition]
  infer_instance

structure GuardVisit (graph : DAG n) where
  node : Fin graph.nodeCount
  route : List graph.StoredOccurrence
  rooted : RootedPath graph node route
  position : Fin (graph.node node).guardLabels.length
  phase : Bool

/-- A guard position certifies that its stored node is internal. -/
theorem guard_internal (graph : DAG n) (node : Fin graph.nodeCount)
    (position : Fin (graph.node node).guardLabels.length) :
    (graph.node node).isInternal = true := by
  have valid := position.isLt
  cases equation : graph.node node <;> simp_all [Gate.guardLabels, Gate.isInternal]

def GuardVisit.key {graph : DAG n} (visit : GuardVisit graph) : GuardKey graph :=
  (⟨visit.node, visit.position⟩, visit.phase)

/-- Repeated labels keep separate positions, and entry and exit remain separate. -/
theorem key_injective (graph : DAG n) (forest : graph.FormulaForest) :
    Function.Injective (GuardVisit.key (graph := graph)) := by
  intro first second equal
  cases first with
  | mk firstNode firstRoute firstPath firstPosition firstPhase =>
    cases second with
    | mk secondNode secondRoute secondPath secondPosition secondPhase =>
      have nodes : firstNode = secondNode := congrArg
        (fun key : GuardKey graph => key.1.1) equal
      subst secondNode
      have positions : firstPosition = secondPosition := Fin.ext
        (congrArg (fun key : GuardKey graph => key.1.2.val) equal)
      subst secondPosition
      have phases : firstPhase = secondPhase := congrArg (fun key : GuardKey graph => key.2) equal
      subst secondPhase
      have routes := RootedPath.unique_internal graph forest firstNode firstRoute secondRoute
        (guard_internal graph firstNode firstPosition) firstPath secondPath
      subst secondRoute
      rfl

/-- One key for each stored label incidence and each of the two phases. -/
theorem key_card (graph : DAG n) : Nat.card (GuardKey graph) = 2 * graph.guardIncidences := by
  simp only [GuardKey, GuardPosition, Nat.card_prod, Nat.card_sigma, Nat.card_fin,
    Nat.card_eq_fintype_card, Fintype.card_bool]
  simp [DAG.guardIncidences, List.sum_ofFn, Nat.mul_comm]

/-- An abstract positional charging bound; no execution cost is inferred here. -/
theorem visit_card_le (graph : DAG n) (forest : graph.FormulaForest) :
    Nat.card (GuardVisit graph) ≤ 2 * graph.guardIncidences := by
  have bounded := Nat.card_le_card_of_injective (GuardVisit.key (graph := graph))
    (key_injective graph forest)
  exact bounded.trans_eq (key_card graph)

end Controller.Cost.ForestGuardCharging
