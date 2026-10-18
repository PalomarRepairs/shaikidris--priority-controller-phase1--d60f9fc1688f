module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGInputGate

@[expose] public section

/-! The zero gate appends a false result through two fetched instructions,
preserving the caller stack, output and source heap prefix. -/
namespace Controller.Cost.UniformDAGZeroGate
open Controller.Cost.GateProgram

def code (width : ℕ) : Code width :=
  [.constant 2 (boolWord width false), .allocate 2]
@[simp] theorem code_length : (code width).length = 2 := rfl

theorem execution (program : Program width 4) (s : State width 4)
    (base : ℕ) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 2 < 2 ^ width) (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base (code width)) :
    ∃ final, Execution program s final 2 (s.liveWords + 1) ∧
      final.reg 2 = boolWord width false ∧ final.reg 3 = s.reg 3 ∧
      final.heap = s.heap.push (boolWord width false) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 2) ∧ final.halted = false := by
  let ready := s.advance.put 2 (boolWord width false)
  let final := { ready.advance with heap := s.heap.push (boolWord width false) }
  have pcVal : s.pc.val = base := by
    rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have readyPC : ready.pc = word width (base + 1) := by
    simp [ready, State.put, State.advance, pcVal]
  have readyVal : ready.pc.val = base + 1 := by
    rw [readyPC]; exact Nat.mod_eq_of_lt (by omega)
  have first : programStep program s = some ready := by
    unfold programStep
    rw [pcVal, show program[base]? = some (.constant 2 (boolWord width false)) from
      by simpa [code] using block 0 (by simp [code])]
    simp [step, ready, running]
  have last : programStep program ready = some final := by
    unfold programStep
    rw [readyVal, show program[base + 1]? = some (.allocate 2) from
      by simpa [code] using block 1 (by simp [code])]
    simp [step, ready, final, State.put, State.advance, running, room]
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · have trace := Execution.cons first (Execution.cons last (Execution.refl final))
    have rlive : ready.liveWords = s.liveWords := rfl
    have flive : final.liveWords = s.liveWords + 1 := by
      simp [final, ready, State.put, State.advance, State.liveWords]; omega
    simpa only [rlive, flive, Nat.max_self,
      Nat.max_eq_right (by omega : s.liveWords ≤ s.liveWords + 1)] using trace
  · simp [final, ready, State.advance, State.put]
  · simp [final, ready, State.advance, State.put]
  · simp [final, State.advance, readyVal, Nat.add_assoc]
  · simp [final, ready, State.advance, State.put, running]

end Controller.Cost.UniformDAGZeroGate
