module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSteps
public import Controller.Cost.SharedTagCompare

@[expose] public section

/-! Fixed depth/cursor updates for the mutable-prefix enumeration driver. -/
namespace Controller.Cost.EnumerationCounter
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width delta : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width delta), .add 3 3 0]

@[simp] theorem code_length : (code width delta).length = 2 := rfl

theorem shift_execution (program : Program width 8) (state : State width 8)
    (entry delta : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (present : SharedRootRead.BlockAt program entry (code width delta)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.reg 3 = word width ((state.reg 3).val + (word width delta).val) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → final.reg register = state.reg register) := by
  obtain ⟨loaded, t0, pc0, held0, heap0, stack0, output0, running0, frame0⟩ :=
    SharedEvaluationReclaim.constant_execution program entry delta 0 state position running (by omega)
      (by simpa [code] using present 0 (by simp))
  obtain ⟨final, t1, pc1, held1, heap1, stack1, output1, running1, frame1⟩ :=
    EnumerationSteps.add_execution (program := program) loaded (entry + 1) 3 3 0 pc0 running0 (by omega)
      (by simpa [code] using present 1 (by simp))
  have loadedLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, heap0, stack0, output0]
  refine ⟨final, ?_, ?_, heap1.trans heap0, stack1.trans stack0, output1.trans output0, ?_, running1, ?_⟩
  · simpa only [loadedLive, Nat.max_self, Nat.reduceAdd] using t0.append t1
  · rw [held1, held0, frame0 3 (by decide)]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using pc1
  · intro register notZero notThree; rw [frame1 register notThree, frame0 register notZero]

theorem increment_execution (program : Program width 8) (state : State width 8)
    (entry depth : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width depth) (fits : depth + 1 < 2 ^ width)
    (room : entry + 2 < 2 ^ width) (present : SharedRootRead.BlockAt program entry (code width 1)) :
    ∃ final, Execution program state final 2 state.liveWords ∧ final.reg 3 = word width (depth + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → final.reg register = state.reg register) := by
  obtain ⟨final, trace, value, heap, stack, output, pc, live, frame⟩ := shift_execution program state entry 1 position running room present
  refine ⟨final, trace, ?_, heap, stack, output, pc, live, frame⟩
  simpa only [held, word, Nat.mod_eq_of_lt (by omega : depth < 2 ^ width),
    Nat.mod_eq_of_lt (by omega : 1 < 2 ^ width)] using value

theorem decrement_execution (program : Program width 8) (state : State width 8)
    (entry depth : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (held : state.reg 3 = word width (depth + 1)) (fits : depth + 1 < 2 ^ width)
    (room : entry + 2 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width (2 ^ width - 1))) :
    ∃ final, Execution program state final 2 state.liveWords ∧ final.reg 3 = word width depth ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → final.reg register = state.reg register) := by
  obtain ⟨final, trace, value, heap, stack, output, pc, live, frame⟩ := shift_execution program state entry (2 ^ width - 1) position running room present
  refine ⟨final, trace, ?_, heap, stack, output, pc, live, frame⟩
  have maskFit : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  rw [held, show (word width (depth + 1)).val = depth + 1 from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt maskFit,
    decrement_word] at value
  exact value

end Controller.Cost.EnumerationCounter
