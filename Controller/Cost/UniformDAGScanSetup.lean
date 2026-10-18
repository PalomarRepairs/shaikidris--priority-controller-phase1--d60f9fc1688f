module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGScanLoop

@[expose] public section

/-! The fixed setup reads an arity and an incidence-stream base from actual
cache cells indexed by the runtime row offset. The arity is pushed as the loop
counter. No source incidence identifier or arity is encoded in instructions. -/
namespace Controller.Cost.UniformDAGScanSetup
open Controller.Cost.GateProgram

def code (width arityBase sourceBase : ℕ) : Code width :=
  [.constant 0 (word width arityBase), .add 0 0 3, .load 0 0, .push 0,
   .constant 0 (word width sourceBase), .add 0 0 3, .load 3 0]
@[simp] theorem code_length : (code width arityBase sourceBase).length = 7 := rfl

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

/-- Seven actual fetched steps prepare the saved loop count and source cursor;
the one extra saved word is included in the exact peak. -/
theorem execution (program : Program width 4) (s : State width 4)
    (base arityBase sourceBase offset count cursor : ℕ)
    (offsetHeld : s.reg 3 = word width offset)
    (arityFits : arityBase + offset < 2 ^ width)
    (sourceFits : sourceBase + offset < 2 ^ width)
    (arityBound : arityBase + offset < s.heap.size)
    (sourceBound : sourceBase + offset < s.heap.size)
    (arityCell : s.heap[arityBase + offset]'arityBound = word width count)
    (sourceCell : s.heap[sourceBase + offset]'sourceBound = word width cursor)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 7 < 2 ^ width)
    (block : BlockAt program base (code width arityBase sourceBase)) :
    ∃ ready, Execution program s ready 7 (s.liveWords + 1) ∧
      ready.reg 0 = word width (sourceBase + offset) ∧
      ready.reg 1 = s.reg 1 ∧ ready.reg 2 = s.reg 2 ∧
      ready.reg 3 = word width cursor ∧ ready.heap = s.heap ∧
      ready.stack = word width count :: s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 7) ∧ ready.halted = false := by
  let one := s.advance.put 0 (word width arityBase)
  let two := one.advance.put 0 (word width (arityBase + offset))
  let three := two.advance.put 0 (word width count)
  let four := { three.advance with stack := word width count :: s.stack }
  let five := four.advance.put 0 (word width sourceBase)
  let six := five.advance.put 0 (word width (sourceBase + offset))
  let ready := six.advance.put 3 (word width cursor)
  have av : (word width arityBase).val = arityBase := Nat.mod_eq_of_lt (by omega)
  have sv : (word width sourceBase).val = sourceBase := Nat.mod_eq_of_lt (by omega)
  have ov : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have ap : (word width (arityBase + offset)).val = arityBase + offset := Nat.mod_eq_of_lt arityFits
  have sp : (word width (sourceBase + offset)).val = sourceBase + offset := Nat.mod_eq_of_lt sourceFits
  have p1 : one.pc = word width (base + 1) := by simpa [one, State.put] using advance s base pc (by omega)
  have p2 : two.pc = word width (base + 2) := by simpa [two, State.put, Nat.add_assoc] using advance one (base + 1) p1 (by omega)
  have p3 : three.pc = word width (base + 3) := by simpa [three, State.put, Nat.add_assoc] using advance two (base + 2) p2 (by omega)
  have p4 : four.pc = word width (base + 4) := by simpa [four, Nat.add_assoc] using advance three (base + 3) p3 (by omega)
  have p5 : five.pc = word width (base + 5) := by simpa [five, State.put, Nat.add_assoc] using advance four (base + 4) p4 (by omega)
  have p6 : six.pc = word width (base + 6) := by simpa [six, State.put, Nat.add_assoc] using advance five (base + 5) p5 (by omega)
  have p7 : ready.pc = word width (base + 7) := by simpa [ready, State.put, Nat.add_assoc] using advance six (base + 6) p6 (by omega)
  have step0 : programStep program s = some one := by
    rw [fetched program s base (.constant 0 (word width arityBase)) pc (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    simp [step, one, running]
  have step1 : programStep program one = some two := by
    rw [fetched program one (base + 1) (.add 0 0 3) p1 (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    simp [step, one, two, State.advance, State.put, running, offsetHeld, av, ov]
  have step2 : programStep program two = some three := by
    rw [fetched program two (base + 2) (.load 0 0) p2 (by omega)
      (by simpa [code] using block 2 (by simp [code]))]
    simp [step, one, two, three, State.advance, State.put, running, ap, arityBound, arityCell]
  have step3 : programStep program three = some four := by
    rw [fetched program three (base + 3) (.push 0) p3 (by omega)
      (by simpa [code] using block 3 (by simp [code]))]
    simp [step, one, two, three, four, State.advance, State.put, running]
  have step4 : programStep program four = some five := by
    rw [fetched program four (base + 4) (.constant 0 (word width sourceBase)) p4 (by omega)
      (by simpa [code] using block 4 (by simp [code]))]
    simp [step, one, two, three, four, five, State.advance, State.put, running]
  have step5 : programStep program five = some six := by
    rw [fetched program five (base + 5) (.add 0 0 3) p5 (by omega)
      (by simpa [code] using block 5 (by simp [code]))]
    simp [step, one, two, three, four, five, six, State.advance, State.put, running, offsetHeld, sv, ov]
  have step6 : programStep program six = some ready := by
    rw [fetched program six (base + 6) (.load 3 0) p6 (by omega)
      (by simpa [code] using block 6 (by simp [code]))]
    simp [step, one, two, three, four, five, six, ready, State.advance, State.put, running, sp, sourceBound, sourceCell]
  have l1 : one.liveWords = s.liveWords := rfl
  have l2 : two.liveWords = s.liveWords := rfl
  have l3 : three.liveWords = s.liveWords := rfl
  have l4 : four.liveWords = s.liveWords + 1 := by simp [four, three, two, one, State.liveWords, State.advance, State.put]; omega
  have l5 : five.liveWords = s.liveWords + 1 := by exact l4
  have l6 : six.liveWords = s.liveWords + 1 := by exact l5
  have l7 : ready.liveWords = s.liveWords + 1 := by exact l6
  refine ⟨ready, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, p7, ?_⟩
  · have trace := Execution.cons step0 (Execution.cons step1 (Execution.cons step2
      (Execution.cons step3 (Execution.cons step4 (Execution.cons step5
        (Execution.cons step6 (Execution.refl ready)))))))
    simpa only [l1, l2, l3, l4, l5, l6, l7, Nat.max_self,
      Nat.max_eq_right (Nat.le_succ s.liveWords)] using trace
  all_goals simp [ready, six, five, four, three, two, one, State.advance, State.put, running]

end Controller.Cost.UniformDAGScanSetup
