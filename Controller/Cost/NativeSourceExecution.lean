module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeCircuitSize
public import Controller.Native.SourceLift

@[expose] public section

/-! The source assignment constructor is executed by the native circuit code.
Its cost is bounded by the selected source formula's variables, rows and literal
occurrences, including the retained assertion rows. -/
namespace Controller.Cost.NativeSourceExecution
open Controller.CNF Controller.Native Controller.Native.SourceController
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution

abbrev sourceCircuit (parameters : Parameters) := (compile parameters).toState.circuit

def selectedSize (parameters : Parameters) : NativeSize where
  variableCount := (compile parameters).toState.count
  clauses := (formula parameters).clauses.size
  literals := NativeCircuitSize.literalCount (formula parameters)

theorem equation_rows (parameters : Parameters) :
    (sourceCircuit parameters).formula.clauses.size = (equationFormula parameters).clauses.size := by
  have rows := congrArg (fun f : Formula Nat => f.clauses.size)
    (compile_source_rows_unconditional parameters)
  simpa only [CNF.relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map] using rows

theorem equation_literals (parameters : Parameters) :
    NativeCircuitSize.literalCount (sourceCircuit parameters).formula =
      NativeCircuitSize.literalCount (equationFormula parameters) := by
  rw [← compile_source_rows_unconditional parameters, NativeCircuitSize.literalCount_relabel]

theorem equation_rows_le (parameters : Parameters) :
    (equationFormula parameters).clauses.size ≤ (formula parameters).clauses.size := by
  change (equationFormula parameters).clauses.size ≤
    ((equationFormula parameters).clauses ++
      (CNF.ofClauses ((assertions parameters).map fun literal => [literal])).clauses).size
  simp only [Array.size_append]
  omega

theorem equation_literals_le (parameters : Parameters) :
    NativeCircuitSize.literalCount (equationFormula parameters) ≤
      NativeCircuitSize.literalCount (formula parameters) := by
  rw [formula, NativeCircuitSize.literalCount_append]
  omega

theorem code_length_le (parameters : Parameters) (width base entry : Nat) :
    (NativeCircuitExecution.code width base entry (sourceCircuit parameters)).length ≤
      13 * (selectedSize parameters).total := by
  have bounded := NativeCircuitSize.code_length_le_selected width base entry (sourceCircuit parameters)
  have rows := equation_rows parameters
  have literals := equation_literals parameters
  have rowsLe := equation_rows_le parameters
  have literalsLe := equation_literals_le parameters
  simp only [NativeCircuitSize.selectedSize, selectedSize, NativeSize.total] at bounded ⊢
  rw [rows, literals] at bounded
  omega

set_option maxHeartbeats 3000000 in
theorem execution (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (resident : Program width 4) (state : State width 4) (base entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (NativeCircuitExecution.code width base entry (sourceCircuit parameters)).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width) (tableRoom : base + (compile parameters).toState.count < 2 ^ width)
    (stored : TableStored state.heap base (sourcePhysicalRoots parameters input))
    (physical : BlockAt resident entry (NativeCircuitExecution.code width base entry (sourceCircuit parameters))) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 13 * (selectedSize parameters).total ∧
      peak ≤ state.liveWords + (selectedSize parameters).total ∧
      TableStored final.heap base (SourceLift.finite parameters input) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (NativeCircuitExecution.code width base entry (sourceCircuit parameters)).length) ∧
      final.halted = false := by
  obtain ⟨final, ticks, trace, bound, table, stack, output, pc, running⟩ :=
    NativeCircuitExecution.execution resident state (sourceCircuit parameters) (sourcePhysicalRoots parameters input)
      base entry position running room boolFits tableRoom stored physical
  have gates := (sourceCircuit parameters).variable_count
  refine ⟨final, ticks, state.liveWords + (sourceCircuit parameters).gateCount, trace,
    bound.trans (code_length_le parameters width base entry), ?_, table, stack, output, pc, running⟩
  simp only [selectedSize, NativeSize.total]
  omega

end Controller.Cost.NativeSourceExecution
