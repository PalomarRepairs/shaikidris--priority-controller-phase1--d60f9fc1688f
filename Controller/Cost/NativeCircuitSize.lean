module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeCircuitExecution
public import Controller.Basic.Sizes

@[expose] public section

/-! Native circuit execution is charged to its actual variables, defining rows
and literal occurrences. No channel-by-bus size assumption is required. -/
namespace Controller.Cost.NativeCircuitSize
open Controller.CNF Controller.Cost.NativeCircuitExecution

def literalCount (formula : Formula α) : Nat := (formula.clauses.toList.map List.length).sum

def selectedSize (circuit : AcyclicCircuit rootCount variableCount) : NativeSize where
  variableCount := variableCount
  clauses := circuit.formula.clauses.size
  literals := literalCount circuit.formula

theorem gate_has_row (gate : Gate α) (output : Literal α) :
    1 ≤ (gate.clauses output).length := by
  cases gate <;> simp [Gate.clauses]

theorem gate_inputs_le_literals (gate : Gate α) (output : Literal α) :
    gate.inputs.length ≤ ((gate.clauses output).map List.length).sum := by
  cases gate <;> simp [Gate.inputs, Gate.clauses, List.map_append, List.sum_append,
    List.map_map, Function.comp_def] <;> omega

theorem relabel_input_length (gate : Gate α) (rename : α → β) :
    (gate.relabel rename).inputs.length = gate.inputs.length := by
  cases gate <;> simp [Gate.relabel, Gate.inputs]

theorem literalCount_relabel (formula : Formula α) (rename : α → β) :
    literalCount (CNF.relabel rename formula) = literalCount formula := by
  simp [literalCount, CNF.relabel, Controller.CNF.OrderedFormula.relabel, Array.toList_map,
    List.map_map, Controller.CNF.OrderedFormula.Clause.relabel, Function.comp_def]

theorem literalCount_append (left right : Formula α) :
    literalCount (left ++ right) = literalCount left + literalCount right := by
  change (((left.clauses ++ right.clauses).toList).map List.length).sum = _
  simp [literalCount, Array.toList_append, List.map_append, List.sum_append]

theorem gate_count_le_rows (circuit : AcyclicCircuit rootCount variableCount) :
    circuit.gateCount ≤ circuit.formula.clauses.size := by
  induction circuit with
  | roots => simp [AcyclicCircuit.gateCount, AcyclicCircuit.formula, Controller.CNF.OrderedFormula.empty]
  | @snoc variableCount previous gate phase ih =>
    have current := gate_has_row (gate.relabel Fin.castSucc) (Fin.last variableCount, phase)
    simp only [AcyclicCircuit.gateCount, AcyclicCircuit.formula_snoc_rows,
      Array.size_append, Array.size_map, Gate.block, CNF.ofClauses, List.size_toArray]
    omega

theorem input_occurrences_le_literals (circuit : AcyclicCircuit rootCount variableCount) :
    inputOccurrences circuit ≤ literalCount circuit.formula := by
  induction circuit with
  | roots => simp [inputOccurrences, AcyclicCircuit.formula, literalCount, Controller.CNF.OrderedFormula.empty]
  | @snoc variableCount previous gate phase ih =>
    have current := gate_inputs_le_literals (gate.relabel Fin.castSucc) (Fin.last variableCount, phase)
    rw [relabel_input_length] at current
    simp only [inputOccurrences, AcyclicCircuit.formula, literalCount_append, literalCount_relabel]
    have blockCount : literalCount ((gate.relabel Fin.castSucc).block (Fin.last variableCount, phase)) =
        (((gate.relabel Fin.castSucc).clauses (Fin.last variableCount, phase)).map List.length).sum := by
      simp [literalCount, Gate.block, CNF.ofClauses]
    rw [blockCount]
    omega

theorem code_length_le_selected (width base entry : Nat)
    (circuit : AcyclicCircuit rootCount variableCount) :
    (NativeCircuitExecution.code width base entry circuit).length ≤ 13 * (selectedSize circuit).total := by
  have raw := NativeCircuitExecution.code_length_le width base entry circuit
  have gates := gate_count_le_rows circuit
  have inputs := input_occurrences_le_literals circuit
  simp only [selectedSize, NativeSize.total]
  omega

end Controller.Cost.NativeCircuitSize
