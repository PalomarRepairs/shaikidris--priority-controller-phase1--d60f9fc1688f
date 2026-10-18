module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationStreamEmit

@[expose] public section

/-! Fetched constant output words on the enumeration machine. Constants encode
fixed primary-input coordinates, while runtime coordinates use heap reads. -/
namespace Controller.Cost.EnumerationLiteralEmit
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width : Nat) (value : Bool) : List (Instruction width 8) :=
  [.constant 1 (boolWord width value), .emit 1]

@[simp] theorem code_length : (code width value).length = 2 := rfl

theorem execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (value : Bool) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 2 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width value)) :
    ∃ final, Execution program state final 2 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = boolWord width value :: state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 1 → final.reg register = state.reg register) := by
  obtain ⟨loaded, first, pc, held, heap, stack, output, live, frame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry (if value then 1 else 0) 1 state
      position running (by omega) (by simpa [code, boolWord] using present 0 (by simp))
  obtain ⟨final, second, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame, finalLive⟩ :=
    EnumerationSteps.emit_execution (program := program) loaded (entry + 1) 1 pc live (by omega)
      (by simpa [code] using present 1 (by simp))
  have sameLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, finalHeap.trans heap, finalStack.trans stack, ?_, ?_, finalRunning, ?_⟩
  · simpa only [sameLive, Nat.max_eq_right (Nat.le_succ _)] using first.append second
  · rw [finalOutput, held, output]; rfl
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · intro register other; rw [finalFrame, frame register other]

end Controller.Cost.EnumerationLiteralEmit
