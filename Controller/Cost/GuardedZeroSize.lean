module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Detect
public import Controller.Cost.Horn

@[expose] public section

/-! Every queried zero system has linear row, literal and variable counts.
Repeated children and guards are charged as incidences, and fixed assignments
retain both their true and false units. -/
namespace Controller.Cost.GuardedZeroSize
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Decoder.ZeroSystem

variable {n : Nat}

def literalCount (rows : List (Clause α)) : Nat := (rows.map List.length).sum

@[simp] theorem literalCount_append (left right : List (Clause α)) :
    literalCount (left ++ right) = literalCount left + literalCount right := by
  simp [literalCount, List.map_append, List.sum_append]

theorem node_bounds (graph : DAG n) (index : Fin graph.nodeCount) :
    (graph.nodeClauses index).length ≤ 2 + (graph.node index).children.length ∧
    literalCount (graph.nodeClauses index) ≤ 4 + 2 * (graph.node index).children.length +
      (graph.node index).guardLabels.length := by
  cases gate : graph.node index <;>
    simp [DAG.nodeClauses, gate, Gate.children, Gate.guardLabels, literalCount,
      implicationClause, positiveClause, List.map_map, Function.comp_def] <;> omega

private theorem indexed_bounds (graph : DAG n) (indices : List (Fin graph.nodeCount)) :
    (indices.flatMap graph.nodeClauses).length ≤ 2 * indices.length +
      (indices.map (fun index => (graph.node index).children.length)).sum ∧
    literalCount (indices.flatMap graph.nodeClauses) ≤ 4 * indices.length +
      2 * (indices.map (fun index => (graph.node index).children.length)).sum +
      (indices.map (fun index => (graph.node index).guardLabels.length)).sum := by
  induction indices with
  | nil => simp [literalCount]
  | cons index rest ih =>
    have current := node_bounds graph index
    simp only [List.flatMap_cons, List.length_append, literalCount_append,
      List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem forward_bounds (graph : DAG n) :
    graph.forwardClauses.length ≤ 2 * graph.nodeCount + graph.childIncidences ∧
    literalCount graph.forwardClauses ≤ 4 * graph.nodeCount + 2 * graph.childIncidences +
      graph.guardIncidences := by
  simpa only [DAG.forwardClauses, DAG.childIncidences, DAG.guardIncidences,
    List.ofFn_eq_map, List.length_finRange] using indexed_bounds graph (List.finRange graph.nodeCount)

private theorem units_count (indices : List β) (unit : β → Clause α)
    (one : ∀ index, (unit index).length = 1) : literalCount (indices.map unit) = indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [literalCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.length_cons, one] at *
    omega

theorem fixed_unit_bounds (graph : DAG n) (T F : Finset (Channel n)) :
    (graph.trueUnitClauses T).length ≤ n ∧ (graph.falseUnitClauses F).length ≤ n ∧
    literalCount (graph.trueUnitClauses T) = (graph.trueUnitClauses T).length ∧
    literalCount (graph.falseUnitClauses F) = (graph.falseUnitClauses F).length := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [DAG.trueUnitClauses, List.length_map]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange)
  · simp only [DAG.falseUnitClauses, List.length_map]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange)
  · unfold DAG.trueUnitClauses
    rw [units_count _ _ (by intro index; simp [positiveClause]), List.length_map]
  · unfold DAG.falseUnitClauses
    rw [units_count _ _ (by intro index; simp [implicationClause, positiveClause]), List.length_map]

theorem channel_bounds (graph : DAG n) (b : Nat) (target : Channel n)
    (T F : Finset (Channel n)) :
    (graph.channelClauses b target T F).length ≤ 2 * n + 2 ∧
    literalCount (graph.channelClauses b target T F) ≤ 3 * n + 1 := by
  have fixed := fixed_unit_bounds graph T F
  by_cases one : b = 1 <;>
    simp only [DAG.channelClauses, one, ite_true, ite_false, List.length_append,
      List.length_cons, List.length_nil, literalCount_append, literalCount, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, positiveClause,
      List.length_map, List.length_finRange] at * <;> omega

theorem zero_system_bounds (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    (graph.zeroSystem b target root T F).clauses.size ≤
      2 * graph.nodeCount + graph.childIncidences + 2 * n + 3 ∧
    literalCount (graph.zeroSystem b target root T F).clauses.toList ≤
      4 * graph.nodeCount + 2 * graph.childIncidences + graph.guardIncidences + 3 * n + 2 := by
  have forward := forward_bounds graph
  have channel := channel_bounds graph b target T F
  simp only [DAG.zeroSystem, CNF.ofClauses, List.size_toArray, List.toList_toArray,
    List.length_append, List.length_cons, List.length_nil, literalCount_append,
    literalCount, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    implicationClause, positiveClause] at *
  omega

theorem finite_input_size (graph : DAG n) (b : Nat) (target : Channel n)
    (root : Fin graph.nodeCount) (T F : Finset (Channel n)) :
    Horn.inputSize (graph.finiteZeroSystem b target root T F) ≤
      8 * (n + graph.nodeCount + graph.childIncidences + graph.guardIncidences + 1) := by
  have bounds := zero_system_bounds graph b target root T F
  simp only [DAG.finiteZeroSystem, Horn.inputSize, CNF.relabel,
    Controller.CNF.OrderedFormula.relabel, Array.size_map, Array.toList_map,
    List.map_map, Controller.CNF.OrderedFormula.Clause.relabel, List.length_map, Function.comp_def]
  change 1 + (n + graph.nodeCount) + (graph.zeroSystem b target root T F).clauses.size +
    literalCount (graph.zeroSystem b target root T F).clauses.toList ≤ _
  omega

end Controller.Cost.GuardedZeroSize
