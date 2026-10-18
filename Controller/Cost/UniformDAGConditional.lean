module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGRead

@[expose] public section

/-! Uniform OR and negative-guard incidence processing. A represented source
identifier is read indirectly; a true stored value changes the accumulator to
the fixed replacement. The instruction operands contain no source identifier. -/
namespace Controller.Cost.UniformDAGConditional
open Controller.Cost.GateProgram

def branchCode (width base : ℕ) (replacement : Bool) : Code width :=
  [.branchZero 1 (word width (base + 2)), .constant 2 (boolWord width replacement)]
def code (width base : ℕ) (replacement : Bool) : Code width :=
  UniformDAGRead.code width ++ branchCode width (base + 3) replacement
@[simp] theorem code_length : (code width base replacement).length = 5 := rfl

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance (s : State width 4) (base : ℕ)
    (pc : s.pc = word width base) (fits : base < 2 ^ width) :
    s.advance.pc = word width (base + 1) := by
  simp only [State.advance, pc]
  rw [show (word width base).val = base from Nat.mod_eq_of_lt fits]

theorem branch_execution (program : Program width 4) (s : State width 4)
    (base : ℕ) (value replacement : Bool)
    (loaded : s.reg 1 = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 2 < 2 ^ width) (block : BlockAt program base (branchCode width base replacement)) :
    ∃ final, Execution program s final (if value then 2 else 1) s.liveWords ∧
      final.reg 0 = s.reg 0 ∧ final.reg 1 = s.reg 1 ∧
      final.reg 2 = (if value then boolWord width replacement else s.reg 2) ∧
      final.reg 3 = s.reg 3 ∧ final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = s.output ∧ final.pc = word width (base + 2) ∧ final.halted = false := by
  cases value with
  | false =>
      let final := { s with pc := word width (base + 2) }
      have transition : programStep program s = some final := by
        rw [fetched program s base (.branchZero 1 (word width (base + 2))) pc (by omega)
          (by simpa [branchCode] using block 0 (by simp [branchCode]))]
        simp [step, running, loaded, boolWord, word, final, State.advance]
      refine ⟨final, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, running⟩
      have trace := Execution.cons transition (Execution.refl final)
      simpa [final, State.liveWords] using trace
  | true =>
      let middle := s.advance
      let final := middle.advance.put 2 (boolWord width replacement)
      have trueVal : (boolWord width true).val = 1 := by
        simp [boolWord, word, Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)]
      have middlePC : middle.pc = word width (base + 1) := advance s base pc (by omega)
      have finalPC : final.pc = word width (base + 2) := by
        simpa [final, State.put, Nat.add_assoc] using advance middle (base + 1) middlePC (by omega)
      have first : programStep program s = some middle := by
        rw [fetched program s base (.branchZero 1 (word width (base + 2))) pc (by omega)
          (by simpa [branchCode] using block 0 (by simp [branchCode]))]
        simp [step, running, loaded, trueVal, middle]
      have second : programStep program middle = some final := by
        rw [fetched program middle (base + 1) (.constant 2 (boolWord width replacement))
          middlePC (by omega) (by simpa [branchCode] using block 1 (by simp [branchCode]))]
        simp [step, middle, final, State.advance, running]
      have middleLive : middle.liveWords = s.liveWords := rfl
      have finalLive : final.liveWords = s.liveWords := rfl
      refine ⟨final, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, finalPC, running⟩
      · have trace := Execution.cons first (Execution.cons second (Execution.refl final))
        simpa [middleLive, finalLive] using trace
      all_goals simp [final, middle, State.advance, State.put]

/-- A source incidence takes five fetched steps when true and four when false. -/
theorem execution (program : Program width 4) (s : State width 4)
    (cursor valueBase index base : ℕ) (value replacement : Bool)
    (cursorHeld : s.reg 3 = word width cursor) (baseHeld : s.reg 1 = word width valueBase)
    (cursorBound : cursor < s.heap.size) (cursorFits : cursor < 2 ^ width)
    (source : s.heap[cursor]'cursorBound = word width index)
    (valueBound : valueBase + index < s.heap.size) (valueFits : valueBase + index < 2 ^ width)
    (stored : s.heap[valueBase + index]'valueBound = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 5 < 2 ^ width) (block : BlockAt program base (code width base replacement)) :
    ∃ final, Execution program s final (if value then 5 else 4) s.liveWords ∧
      final.reg 0 = word width (valueBase + index) ∧ final.reg 1 = boolWord width value ∧
      final.reg 2 = (if value then boolWord width replacement else s.reg 2) ∧
      final.reg 3 = s.reg 3 ∧ final.heap = s.heap ∧ final.stack = s.stack ∧
      final.output = s.output ∧ final.pc = word width (base + 5) ∧ final.halted = false := by
  have firstBlock := BlockAt.prefix program base (UniformDAGRead.code width)
    (branchCode width (base + 3) replacement) block
  have secondBlock : BlockAt program (base + 3) (branchCode width (base + 3) replacement) := by
    simpa using BlockAt.suffix program base (UniformDAGRead.code width)
      (branchCode width (base + 3) replacement) block
  obtain ⟨ready, readTrace, address, loaded, accumulator, cursorFrame, heap, stack, output, position, active⟩ :=
    UniformDAGRead.execution program s cursor valueBase index base value cursorHeld baseHeld
      cursorBound cursorFits source valueBound valueFits stored pc running (by omega) firstBlock
  obtain ⟨final, branchTrace, finalAddress, finalLoaded, finalAccumulator, finalCursor,
    finalHeap, finalStack, finalOutput, finalPC, finalActive⟩ :=
    branch_execution program ready (base + 3) value replacement loaded position active (by omega) secondBlock
  have readyLive : ready.liveWords = s.liveWords := by simp [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, finalAddress.trans address, finalLoaded.trans loaded, ?_,
    finalCursor.trans cursorFrame, finalHeap.trans heap, finalStack.trans stack,
    finalOutput.trans output, ?_, finalActive⟩
  · have trace := readTrace.append branchTrace
    rw [readyLive] at trace
    cases value <;> simpa using trace
  · simpa [accumulator] using finalAccumulator
  · simpa [Nat.add_assoc] using finalPC
end Controller.Cost.UniformDAGConditional
