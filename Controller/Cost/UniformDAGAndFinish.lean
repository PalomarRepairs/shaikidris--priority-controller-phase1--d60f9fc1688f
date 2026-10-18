module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGInputGate

@[expose] public section

/-! The live-AND finish branches on the stored left value, copies the stored
right value only when needed, and allocates the actual conjunction result. -/
namespace Controller.Cost.UniformDAGAndFinish
open Controller.Cost.GateProgram

def code (width base : ℕ) : Code width :=
  [.branchZero 2 (word width (base + 2)), .copy 2 0, .allocate 2]
@[simp] theorem code_length : (code width base).length = 3 := rfl

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- Both branches charge the result word and preserve the source heap prefix. -/
theorem execution (program : Program width 4) (s : State width 4)
    (base : ℕ) (left right : Bool)
    (leftHeld : s.reg 2 = boolWord width left)
    (rightHeld : s.reg 0 = boolWord width right)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 3 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    ∃ final, Execution program s final (if left then 3 else 2) (s.liveWords + 1) ∧
      final.reg 2 = boolWord width (left && right) ∧ final.reg 3 = s.reg 3 ∧
      final.heap = s.heap.push (boolWord width (left && right)) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 3) ∧ final.halted = false := by
  cases left with
  | false =>
      let ready := { s with pc := word width (base + 2) }
      let final := { ready.advance with heap := s.heap.push (boolWord width false) }
      have first : programStep program s = some ready := by
        rw [fetched program s base (.branchZero 2 (word width (base + 2))) pc (by omega)
          (by simpa [code] using block 0 (by simp [code]))]
        simp [step, running, leftHeld, boolWord, word, ready, State.advance]
      have readyPC : ready.pc = word width (base + 2) := rfl
      have readyVal : ready.pc.val = base + 2 := Nat.mod_eq_of_lt (by omega)
      have last : programStep program ready = some final := by
        rw [fetched program ready (base + 2) (.allocate 2) readyPC (by omega)
          (by simpa [code] using block 2 (by simp [code]))]
        simp [step, ready, final, State.advance, running, room, leftHeld]
      refine ⟨final, ?_, ?_, rfl, ?_, rfl, rfl, ?_, running⟩
      · change Execution program s final 2 (s.liveWords + 1)
        have trace := Execution.cons first (Execution.cons last (Execution.refl final))
        have rlive : ready.liveWords = s.liveWords := rfl
        have flive : final.liveWords = s.liveWords + 1 := by
          simp [final, ready, State.advance, State.liveWords]; omega
        simpa only [rlive, flive, Nat.max_self,
          Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using trace
      · simpa [final, ready, State.advance] using leftHeld
      · simp [final]
      · simp [final, State.advance, readyVal, Nat.add_assoc]
  | true =>
      let middle := s.advance
      let ready := middle.advance.put 2 (boolWord width right)
      let final := { ready.advance with heap := s.heap.push (boolWord width right) }
      have trueVal : (boolWord width true).val = 1 := by
        simp [boolWord, word, Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)]
      have middlePC : middle.pc = word width (base + 1) := by
        change word width (s.pc.val + 1) = word width (base + 1)
        rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
      have middleVal : middle.pc.val = base + 1 := by
        rw [middlePC]; exact Nat.mod_eq_of_lt (by omega)
      have readyPC : ready.pc = word width (base + 2) := by
        simp [ready, State.put, State.advance, middleVal, Nat.add_assoc]
      have readyVal : ready.pc.val = base + 2 := by
        rw [readyPC]; exact Nat.mod_eq_of_lt (by omega)
      have first : programStep program s = some middle := by
        rw [fetched program s base (.branchZero 2 (word width (base + 2))) pc (by omega)
          (by simpa [code] using block 0 (by simp [code]))]
        simp [step, running, leftHeld, trueVal, middle]
      have second : programStep program middle = some ready := by
        rw [fetched program middle (base + 1) (.copy 2 0) middlePC (by omega)
          (by simpa [code] using block 1 (by simp [code]))]
        simp [step, middle, ready, State.advance, running, rightHeld]
      have last : programStep program ready = some final := by
        rw [fetched program ready (base + 2) (.allocate 2) readyPC (by omega)
          (by simpa [code] using block 2 (by simp [code]))]
        simp [step, middle, ready, final, State.put, State.advance, running, room]
      refine ⟨final, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
      · change Execution program s final 3 (s.liveWords + 1)
        have trace := Execution.cons first (Execution.cons second (Execution.cons last (Execution.refl final)))
        have mlive : middle.liveWords = s.liveWords := rfl
        have rlive : ready.liveWords = s.liveWords := rfl
        have flive : final.liveWords = s.liveWords + 1 := by
          simp [final, ready, middle, State.put, State.advance, State.liveWords]; omega
        simpa only [mlive, rlive, flive, Nat.max_self,
          Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using trace
      · simp [final, ready, State.advance, State.put]
      · simp [final, ready, middle, State.advance, State.put]
      · simp [final]
      · simp [final, State.advance, readyVal, Nat.add_assoc]
      · simp [final, ready, middle, State.advance, State.put, running]

end Controller.Cost.UniformDAGAndFinish
