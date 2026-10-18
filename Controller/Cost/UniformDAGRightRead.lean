module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGAndFinish

@[expose] public section

/-! A fixed runtime read locates the original right-child occurrence through
its cached stream base. The left accumulator and value-table base survive. -/
namespace Controller.Cost.UniformDAGRightRead
open Controller.Cost.GateProgram

def code (width sourceBase : ℕ) : Code width :=
  [.constant 0 (word width sourceBase), .add 0 0 3, .load 3 0,
   .constant 0 (word width 1), .add 3 3 0,
   .load 0 3, .add 0 0 1, .load 0 0]
@[simp] theorem code_length : (code width sourceBase).length = 8 := rfl

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

theorem execution (program : Program width 4) (s : State width 4)
    (base sourceBase valueBase offset cursor identifier : ℕ) (value : Bool)
    (offsetHeld : s.reg 3 = word width offset) (valueHeld : s.reg 1 = word width valueBase)
    (sourceFits : sourceBase + offset < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width)
    (sourceBound : sourceBase + offset < s.heap.size)
    (cursorBound : cursor + 1 < s.heap.size)
    (valueBound : valueBase + identifier < s.heap.size)
    (source : s.heap[sourceBase + offset]'sourceBound = word width cursor)
    (occurrence : s.heap[cursor + 1]'cursorBound = word width identifier)
    (stored : s.heap[valueBase + identifier]'valueBound = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 8 < 2 ^ width)
    (block : BlockAt program base (code width sourceBase)) :
    ∃ ready, Execution program s ready 8 s.liveWords ∧
      ready.reg 0 = boolWord width value ∧ ready.reg 1 = s.reg 1 ∧
      ready.reg 2 = s.reg 2 ∧ ready.reg 3 = word width (cursor + 1) ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 8) ∧ ready.halted = false := by
  let one := s.advance.put 0 (word width sourceBase)
  let two := one.advance.put 0 (word width (sourceBase + offset))
  let three := two.advance.put 3 (word width cursor)
  let four := three.advance.put 0 (word width 1)
  let five := four.advance.put 3 (word width (cursor + 1))
  let six := five.advance.put 0 (word width identifier)
  let seven := six.advance.put 0 (word width (valueBase + identifier))
  let ready := seven.advance.put 0 (boolWord width value)
  have sb : (word width sourceBase).val = sourceBase := Nat.mod_eq_of_lt (by omega)
  have off : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have sp : (word width (sourceBase + offset)).val = sourceBase + offset := Nat.mod_eq_of_lt sourceFits
  have cv : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have cp : (word width (cursor + 1)).val = cursor + 1 := Nat.mod_eq_of_lt cursorFits
  have ov : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have vb : (word width valueBase).val = valueBase := Nat.mod_eq_of_lt (by omega)
  have iv : (word width identifier).val = identifier := Nat.mod_eq_of_lt (by omega)
  have vp : (word width (valueBase + identifier)).val = valueBase + identifier := Nat.mod_eq_of_lt valueFits
  have p1 : one.pc = word width (base + 1) := by
    simpa [one, State.put] using advance s base pc (by omega)
  have p2 : two.pc = word width (base + 2) := by
    simpa [two, State.put, Nat.add_assoc] using advance one (base + 1) p1 (by omega)
  have p3 : three.pc = word width (base + 3) := by
    simpa [three, State.put, Nat.add_assoc] using advance two (base + 2) p2 (by omega)
  have p4 : four.pc = word width (base + 4) := by
    simpa [four, State.put, Nat.add_assoc] using advance three (base + 3) p3 (by omega)
  have p5 : five.pc = word width (base + 5) := by
    simpa [five, State.put, Nat.add_assoc] using advance four (base + 4) p4 (by omega)
  have p6 : six.pc = word width (base + 6) := by
    simpa [six, State.put, Nat.add_assoc] using advance five (base + 5) p5 (by omega)
  have p7 : seven.pc = word width (base + 7) := by
    simpa [seven, State.put, Nat.add_assoc] using advance six (base + 6) p6 (by omega)
  have p8 : ready.pc = word width (base + 8) := by
    simpa [ready, State.put, Nat.add_assoc] using advance seven (base + 7) p7 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetched program s base (.constant 0 (word width sourceBase)) pc (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    simp [step, one, State.advance, State.put, running, offsetHeld, valueHeld, sb, off, sp, cv, cp, ov, vb, iv, vp, sourceBound, cursorBound, valueBound, source, occurrence, stored, Nat.add_comm]
  have step1 : programStep program one = some two := by
    rw [fetched program one (base + 1) (.add 0 0 3) p1 (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    simp [step, one, two, State.advance, State.put, running, offsetHeld, valueHeld, sb, off, sp, cv, cp, ov, vb, iv, vp, sourceBound, cursorBound, valueBound, source, occurrence, stored, Nat.add_comm]
  have step2 : programStep program two = some three := by
    rw [fetched program two (base + 2) (.load 3 0) p2 (by omega)
      (by simpa [code] using block 2 (by simp [code]))]
    simp [step, one, two, three, State.advance, State.put, running, offsetHeld, valueHeld, sb, off, sp, cv, cp, ov, vb, iv, vp, sourceBound, cursorBound, valueBound, source, occurrence, stored, Nat.add_comm]
  have step3 : programStep program three = some four := by
    rw [fetched program three (base + 3) (.constant 0 (word width 1)) p3 (by omega)
      (by simpa [code] using block 3 (by simp [code]))]
    simp [step, one, two, three, four, State.advance, State.put, running, offsetHeld, valueHeld, sb, off, sp, cv, cp, ov, vb, iv, vp, sourceBound, cursorBound, valueBound, source, occurrence, stored, Nat.add_comm]
  have step4 : programStep program four = some five := by
    rw [fetched program four (base + 4) (.add 3 3 0) p4 (by omega)
      (by simpa [code] using block 4 (by simp [code]))]
    simp [step, one, two, three, four, five, State.advance, State.put, running, offsetHeld, valueHeld, sb, off, sp, cv, cp, ov, vb, iv, vp, sourceBound, cursorBound, valueBound, source, occurrence, stored, Nat.add_comm]
  have step5 : programStep program five = some six := by
    rw [fetched program five (base + 5) (.load 0 3) p5 (by omega)
      (by simpa [code] using block 5 (by simp [code]))]
    simp [step, one, two, three, four, five, six, State.advance, State.put, running, offsetHeld, valueHeld, sb, off, sp, cv, cp, ov, vb, iv, vp, sourceBound, cursorBound, valueBound, source, occurrence, stored, Nat.add_comm]
  have step6 : programStep program six = some seven := by
    rw [fetched program six (base + 6) (.add 0 0 1) p6 (by omega)
      (by simpa [code] using block 6 (by simp [code]))]
    simp [step, one, two, three, four, five, six, seven, State.advance, State.put, running, offsetHeld, valueHeld, sb, off, sp, cv, cp, ov, vb, iv, vp, sourceBound, cursorBound, valueBound, source, occurrence, stored, Nat.add_comm]
  have step7 : programStep program seven = some ready := by
    rw [fetched program seven (base + 7) (.load 0 0) p7 (by omega)
      (by simpa [code] using block 7 (by simp [code]))]
    simp [step, one, two, three, four, five, six, seven, ready, State.advance, State.put, running, offsetHeld, valueHeld, sb, off, sp, cv, cp, ov, vb, iv, vp, sourceBound, cursorBound, valueBound, source, occurrence, stored, Nat.add_comm]
  have l1 : one.liveWords = s.liveWords := rfl
  have l2 : two.liveWords = s.liveWords := rfl
  have l3 : three.liveWords = s.liveWords := rfl
  have l4 : four.liveWords = s.liveWords := rfl
  have l5 : five.liveWords = s.liveWords := rfl
  have l6 : six.liveWords = s.liveWords := rfl
  have l7 : seven.liveWords = s.liveWords := rfl
  have l8 : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, p8, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.cons step6 (Execution.cons step7 (Execution.refl ready))))))))
    simpa only [l1, l2, l3, l4, l5, l6, l7, l8, Nat.max_self] using trace
  all_goals simp [ready, seven, six, five, four, three, two, one, State.advance, State.put, running]

end Controller.Cost.UniformDAGRightRead
