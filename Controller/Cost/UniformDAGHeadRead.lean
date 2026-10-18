module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGGateScan

@[expose] public section

/-! A fixed runtime row-head read for input channels and guard children.
The row offset remains in register three. The actual cached head identifier
selects its actual stored Boolean value; register one retains the value base. -/
namespace Controller.Cost.UniformDAGHeadRead
open Controller.Cost.GateProgram

def code (width headBase : ℕ) : Code width :=
  [.constant 0 (word width headBase), .add 0 0 3, .load 0 0, .add 0 0 1, .load 2 0]
@[simp] theorem code_length : (code width headBase).length = 5 := rfl

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

/-- Five fetched instructions, no extra allocation and no encoded head ID. -/
theorem execution (program : Program width 4) (s : State width 4)
    (base headBase valueBase offset identifier : ℕ) (value : Bool)
    (offsetHeld : s.reg 3 = word width offset) (valueHeld : s.reg 1 = word width valueBase)
    (headFits : headBase + offset < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width)
    (headBound : headBase + offset < s.heap.size)
    (valueBound : valueBase + identifier < s.heap.size)
    (source : s.heap[headBase + offset]'headBound = word width identifier)
    (stored : s.heap[valueBase + identifier]'valueBound = boolWord width value)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 5 < 2 ^ width)
    (block : BlockAt program base (code width headBase)) :
    ∃ ready, Execution program s ready 5 s.liveWords ∧
      ready.reg 0 = word width (valueBase + identifier) ∧ ready.reg 1 = s.reg 1 ∧
      ready.reg 2 = boolWord width value ∧ ready.reg 3 = s.reg 3 ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 5) ∧ ready.halted = false := by
  let one := s.advance.put 0 (word width headBase)
  let two := one.advance.put 0 (word width (headBase + offset))
  let three := two.advance.put 0 (word width identifier)
  let four := three.advance.put 0 (word width (valueBase + identifier))
  let ready := four.advance.put 2 (boolWord width value)
  have hb : (word width headBase).val = headBase := Nat.mod_eq_of_lt (by omega)
  have off : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have hp : (word width (headBase + offset)).val = headBase + offset := Nat.mod_eq_of_lt headFits
  have vb : (word width valueBase).val = valueBase := Nat.mod_eq_of_lt (by omega)
  have idv : (word width identifier).val = identifier := Nat.mod_eq_of_lt (by omega)
  have vp : (word width (valueBase + identifier)).val = valueBase + identifier := Nat.mod_eq_of_lt valueFits
  have p1 : one.pc = word width (base + 1) := by simpa [one, State.put] using advance s base pc (by omega)
  have p2 : two.pc = word width (base + 2) := by simpa [two, State.put, Nat.add_assoc] using advance one (base + 1) p1 (by omega)
  have p3 : three.pc = word width (base + 3) := by simpa [three, State.put, Nat.add_assoc] using advance two (base + 2) p2 (by omega)
  have p4 : four.pc = word width (base + 4) := by simpa [four, State.put, Nat.add_assoc] using advance three (base + 3) p3 (by omega)
  have p5 : ready.pc = word width (base + 5) := by simpa [ready, State.put, Nat.add_assoc] using advance four (base + 4) p4 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetched program s base (.constant 0 (word width headBase)) pc (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    simp [step, one, running]
  have step1 : programStep program one = some two := by
    rw [fetched program one (base + 1) (.add 0 0 3) p1 (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    simp [step, one, two, State.advance, State.put, running, offsetHeld, hb, off]
  have step2 : programStep program two = some three := by
    rw [fetched program two (base + 2) (.load 0 0) p2 (by omega)
      (by simpa [code] using block 2 (by simp [code]))]
    simp [step, one, two, three, State.advance, State.put, running, hp, headBound, source]
  have step3 : programStep program three = some four := by
    rw [fetched program three (base + 3) (.add 0 0 1) p3 (by omega)
      (by simpa [code] using block 3 (by simp [code]))]
    simp [step, one, two, three, four, State.advance, State.put, running, valueHeld, vb, idv, Nat.add_comm]
  have step4 : programStep program four = some ready := by
    rw [fetched program four (base + 4) (.load 2 0) p4 (by omega)
      (by simpa [code] using block 4 (by simp [code]))]
    simp [step, one, two, three, four, ready, State.advance, State.put, running, vp, valueBound, stored]
  have l1 : one.liveWords = s.liveWords := rfl
  have l2 : two.liveWords = s.liveWords := rfl
  have l3 : three.liveWords = s.liveWords := rfl
  have l4 : four.liveWords = s.liveWords := rfl
  have lr : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, p5, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2
      (Execution.cons step3 (Execution.cons step4 (Execution.refl ready)))))
    simpa only [l1, l2, l3, l4, lr, Nat.max_self] using trace
  all_goals simp [ready, four, three, two, one, State.advance, State.put, running]

end Controller.Cost.UniformDAGHeadRead
