module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationWorkingTrace
public import Controller.Cost.EnumerationCanonicalEmit

@[expose] public section

/-! Canonical emission has constant working space throughout its trace. A
nonallocating view preserves every emitter instruction and replaces allocating
heap/stack instructions elsewhere with halt. Running traces lift to the actual
containing program. -/
namespace Controller.Cost.EnumerationSafeEmit
open Controller.Decoder Controller.Native Controller.Cost.GateProgram
open Controller.Cost.EnumerationStreamEmit Controller.Cost.EnumerationWorkingTrace

def safeInstruction : Instruction width 8 → Instruction width 8
  | .allocate _ | .push _ => .halt
  | instruction => instruction

def safe (program : Program width 8) : Program width 8 := program.map safeInstruction

private theorem safe_step_working (instruction : Instruction width 8) (state next : State width 8)
    (transition : step (safeInstruction instruction) state = some next) : workingWords next ≤ workingWords state := by
  cases instruction <;> simp only [safeInstruction, step] at transition
  all_goals
    repeat' first | split at transition | cases transition
    all_goals simp_all [workingWords, State.advance, State.put]

theorem safe_transition_working (program : Program width 8) (state next : State width 8)
    (transition : programStep (safe program) state = some next) : workingWords next ≤ workingWords state := by
  cases fetched : program[state.pc.val]? with
  | none => simp [safe, programStep, Array.getElem?_map, fetched] at transition
  | some instruction =>
    have actual : step (safeInstruction instruction) state = some next := by
      simpa [safe, programStep, Array.getElem?_map, fetched] using transition
    exact safe_step_working instruction state next actual

theorem transition_running (program : Program width 8) (state next : State width 8)
    (transition : programStep program state = some next) : state.halted = false := by
  cases fetched : program[state.pc.val]? with
  | none => simp [programStep, fetched] at transition
  | some instruction =>
    have actual : step instruction state = some next := by simpa [programStep, fetched] using transition
    cases active : state.halted with
    | false => rfl
    | true => simp [step, active] at actual

theorem working_initial_running {program : Program width 8} {state final : State width 8} {ticks peak : Nat}
    (trace : WorkingExecution program state final ticks peak) (running : final.halted = false) : state.halted = false := by
  cases trace with
  | refl => exact running
  | cons transition rest => exact transition_running _ _ _ transition

theorem lift_transition (program : Program width 8) (state next : State width 8)
    (transition : programStep (safe program) state = some next) (running : next.halted = false) :
    programStep program state = some next := by
  cases fetched : program[state.pc.val]? with
  | none => simp [safe, programStep, Array.getElem?_map, fetched] at transition
  | some instruction =>
    have actual : step (safeInstruction instruction) state = some next := by
      simpa [safe, programStep, Array.getElem?_map, fetched] using transition
    have original : step instruction state = some next := by
      cases instruction <;> simp only [safeInstruction] at actual
      all_goals first
        | exact actual
        | (
            simp only [step] at actual
            split at actual
            · cases actual
            · simp only [Option.some.injEq] at actual
              cases actual
              simp at running)
    simpa [programStep, fetched] using original

theorem lift_working {program : Program width 8} {state final : State width 8} {ticks peak : Nat}
    (trace : WorkingExecution (safe program) state final ticks peak) (running : final.halted = false) :
    WorkingExecution program state final ticks peak := by
  induction trace with
  | refl state => exact WorkingExecution.refl state
  | cons transition rest ih =>
    exact WorkingExecution.cons (lift_transition _ _ _ transition (working_initial_running rest running)) (ih running)

theorem safe_working {program : Program width 8} {state final : State width 8} {ticks peak : Nat}
    (trace : Execution (safe program) state final ticks peak) :
    ∃ workingPeak, WorkingExecution (safe program) state final ticks workingPeak ∧ workingPeak ≤ workingWords state := by
  induction trace with
  | refl state => exact ⟨workingWords state, WorkingExecution.refl state, Nat.le_refl _⟩
  | cons transition rest ih =>
    obtain ⟨workingPeak, workingTrace, bound⟩ := ih
    exact ⟨max (workingWords _) workingPeak, WorkingExecution.cons transition workingTrace,
      max_le (Nat.le_refl _) (bound.trans (safe_transition_working _ _ _ transition))⟩

theorem safe_block (program : Program width 8) (entry : Nat) (code : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry code) (fixed : code.map safeInstruction = code) :
    SharedRootRead.BlockAt (safe program) entry code := by
  intro offset lower
  have instruction := present offset lower
  have fixedAt := congrArg (fun instructions : List (Instruction width 8) => instructions[offset]?) fixed
  have selected : safeInstruction code[offset] = code[offset] := by
    simpa only [List.getElem?_map, List.getElem?_eq_getElem lower, Option.map_some, Option.some.injEq] using fixedAt
  simp only [safe, Array.getElem?_map, instruction, Option.map_some, selected, List.getElem?_eq_getElem lower]

private theorem operands_fixed (width entry : Nat) (operands : List EnumerationEmissionOperands.Operand) :
    (EnumerationEmissionOperands.code width entry operands).map safeInstruction = EnumerationEmissionOperands.code width entry operands := by
  induction operands generalizing entry with
  | nil => rfl
  | cons operand rest ih =>
    rw [EnumerationEmissionOperands.code, List.map_append, ih]
    congr 1
    cases operand <;> rfl

theorem code_fixed (parameters : Parameters) (width entry base : Nat) :
    (EnumerationCanonicalEmit.code parameters width entry base).map safeInstruction =
      EnumerationCanonicalEmit.code parameters width entry base := by
  rw [EnumerationCanonicalEmit.code, List.map_append, operands_fixed]
  rfl

set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry base : Nat) (K : Finset (Fin parameters.channels))
    (stored : EnumerationCanonicalCoordinates.Stored parameters state.heap base K)
    (position : state.pc = word width entry) (running : state.halted = false)
    (widthPositive : 0 < width) (room : entry + (EnumerationCanonicalEmit.code parameters width entry base).length < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (maskRoom : base + parameters.channels ≤ state.heap.size)
    (present : SharedRootRead.BlockAt program entry (EnumerationCanonicalEmit.code parameters width entry base)) :
    ∃ final ticks workingPeak, WorkingExecution program state final ticks workingPeak ∧
      workingPeak ≤ workingWords state ∧ ticks ≤ 3 + 4 * EnumerationCanonicalEmit.Coordinates parameters ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (EnumerationCanonicalEmit.words parameters width K).reverse ++ state.output ∧
      final.pc = word width (entry + (EnumerationCanonicalEmit.code parameters width entry base).length) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 → register ≠ 7 → final.reg register = state.reg register) := by
  obtain ⟨final, ticks, trace, time, heap, stack, output, pc, active, working, frame⟩ :=
    EnumerationCanonicalEmit.execution parameters (safe program) state entry base K stored position running widthPositive room heapFits maskRoom
      (safe_block program entry _ present (code_fixed parameters width entry base))
  obtain ⟨workingPeak, workingTrace, bound⟩ := safe_working trace
  exact ⟨final, ticks, workingPeak, lift_working workingTrace active, bound, time, heap, stack, output, pc, active, frame⟩

end Controller.Cost.EnumerationSafeEmit
