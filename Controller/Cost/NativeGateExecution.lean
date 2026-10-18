module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateUnary
public import Controller.Cost.NativeGateXor
public import Controller.Cost.NativeGateScan

@[expose] public section

/-! Every native gate kind has a fetched execution that extends the stored
assignment by its correctly phased value. Costs count every input occurrence. -/
namespace Controller.Cost.NativeGateExecution
open Controller.Cost.GateProgram Controller.CNF

def code (width base entry : Nat) (phase : Bool) : Gate (Fin variableCount) → List (Instruction width 4)
  | .and inputs => NativeGateScan.code width base entry (inputs.map negate) true false phase
  | .or inputs => NativeGateScan.code width base entry inputs false true phase
  | .xor left right => NativeGateXor.code width base left right phase
  | .alias literal => NativeGateUnary.code width base literal phase
  | .not literal => NativeGateUnary.code width base (negate literal) phase
  | .constant value => NativeGateScan.code (variableCount := variableCount) width base entry [] value false phase

theorem code_length_le (width base entry : Nat) (phase : Bool) (gate : Gate (Fin variableCount)) :
    (code width base entry phase gate).length ≤ 13 * (1 + gate.inputs.length) := by
  cases gate <;> simp [code, Gate.inputs] <;> omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (gate : Gate (Fin variableCount)) (phase : Bool)
    (base entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (code width base entry phase gate).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (stored : NativeGateFold.Stored state.heap values base gate.inputs)
    (physical : BlockAt resident entry (code width base entry phase gate)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + 1) ∧
      ticks ≤ (code width base entry phase gate).length ∧
      final.heap = state.heap.push (boolWord width (gate.eval values == phase)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (code width base entry phase gate).length) ∧ final.halted = false := by
  cases gate with
  | and inputs =>
    simpa only [code, NativeGateScan.code_length, List.length_map, Gate.eval, Nat.add_assoc] using
      NativeGateScan.and_execution resident state values inputs phase base entry position running
        (by simpa only [code, NativeGateScan.code_length, List.length_map, Nat.add_assoc] using room)
        boolFits heapFits stored physical
  | or inputs =>
    simpa only [code, NativeGateScan.code_length, Gate.eval, Nat.add_assoc] using
      NativeGateScan.or_execution resident state values inputs phase base entry position running
        (by simpa only [code, NativeGateScan.code_length, Nat.add_assoc] using room)
        boolFits heapFits stored physical
  | xor left right =>
    obtain ⟨leftValid, leftCell⟩ := stored left (by simp [Gate.inputs])
    obtain ⟨rightValid, rightCell⟩ := stored right (by simp [Gate.inputs])
    obtain ⟨final, trace, heap, stack, output, pc, running⟩ :=
      NativeGateXor.execution resident state values left right phase base entry position running
        (by simpa only [code, NativeGateXor.code_length] using room) boolFits heapFits
        leftValid rightValid leftCell rightCell physical
    refine ⟨final, 13, trace, ?_, heap, stack, output, ?_, running⟩ <;>
      simp only [code, NativeGateXor.code_length, le_refl, pc]
  | «alias» literal =>
    obtain ⟨valid, cell⟩ := stored literal (by simp [Gate.inputs])
    obtain ⟨final, trace, heap, stack, output, pc, running⟩ :=
      NativeGateUnary.execution resident state values literal phase base entry position running
        (by simpa only [code, NativeGateUnary.code_length] using room) boolFits heapFits valid cell physical
    refine ⟨final, 8, trace, ?_, heap, stack, output, ?_, running⟩ <;>
      simp only [code, NativeGateUnary.code_length, le_refl, pc]
  | «not» literal =>
    obtain ⟨valid, cell⟩ := stored literal (by simp [Gate.inputs])
    obtain ⟨final, trace, heap, stack, output, pc, running⟩ :=
      NativeGateUnary.not_execution resident state values literal phase base entry position running
        (by simpa only [code, NativeGateUnary.code_length] using room) boolFits heapFits valid cell physical
    refine ⟨final, 8, trace, ?_, heap, stack, output, ?_, running⟩ <;>
      simp only [code, NativeGateUnary.code_length, le_refl, pc]
  | constant value =>
    have emptyStored : NativeGateFold.Stored state.heap values base ([] : List (Literal (Fin variableCount))) := by
      intro literal membership
      cases membership
    simpa only [code, NativeGateScan.code_length, List.length_nil, Nat.mul_zero, Nat.zero_add,
      Gate.eval, NativeGateFold.result] using
      NativeGateScan.execution resident state values [] value false phase base entry position running
        (by simpa only [code, NativeGateScan.code_length, List.length_nil, Nat.mul_zero, Nat.zero_add,
          Nat.add_zero] using room) boolFits heapFits emptyStored physical

end Controller.Cost.NativeGateExecution
