module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationLiteralEmit

@[expose] public section

/-! Conditional primary-request emission reads a result coordinate only when
register two says that the target is absent. All branch targets are fixed. -/
namespace Controller.Cost.EnumerationMaskedEmit
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width entry address : Nat) : List (Instruction width 8) :=
  [.branchZero 2 (word width (entry + 3)), .constant 1 (boolWord width false),
    .branchZero 7 (word width (entry + 5)), .constant 0 (word width address),
    .load 1 0, .emit 1]

@[simp] theorem code_length : (code width entry address).length = 6 := rfl

private theorem prepare (program : Program width 8) (state : State width 8)
    (entry address : Nat) (targetPresent : Bool) (value : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (flag : state.reg 2 = boolWord width targetPresent) (zero : state.reg 7 = word width 0)
    (widthPositive : 0 < width) (room : entry + 6 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (valid : address < state.heap.size)
    (cell : state.heap[address]? = some value)
    (present : SharedRootRead.BlockAt program entry (code width entry address)) :
    ∃ loaded, Execution program state loaded 3 state.liveWords ∧
      loaded.heap = state.heap ∧ loaded.stack = state.stack ∧ loaded.output = state.output ∧
      loaded.pc = word width (entry + 5) ∧ loaded.halted = false ∧
      loaded.reg 1 = (if targetPresent then boolWord width false else value) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → loaded.reg register = state.reg register) := by
  have oneFits : 1 < 2 ^ width := Nat.one_lt_two_pow_iff.mpr (by omega)
  cases targetPresent with
  | false =>
    obtain ⟨branched, t0, pc0, heap0, stack0, output0, running0, frame0⟩ :=
      EnumerationSteps.branch_taken (program := program) state entry (entry + 3) 2 position running (by omega)
        (by rw [flag]; simp [boolWord, word]) (by simpa [code] using present 0 (by simp))
    obtain ⟨addressed, t1, pc1, held1, heap1, stack1, output1, running1, frame1⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 3) address 0 branched pc0 running0 (by omega)
        (by simpa [code] using present 3 (by simp))
    have actualAddress : (addressed.reg 0).val = address := by rw [held1]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨loaded, t2, pc2, held2, heap2, stack2, output2, running2, frame2⟩ :=
      EnumerationSteps.load_execution (program := program) addressed (entry + 3 + 1) 1 0 pc1 running1 (by omega)
        (by rw [actualAddress, heap1, heap0]; exact valid)
        (by simpa [code, Nat.add_assoc] using present 4 (by simp))
    have live0 : branched.liveWords = state.liveWords := by simp only [State.liveWords, heap0, stack0, output0]
    have live1 : addressed.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, output1, heap0, stack0, output0]
    refine ⟨loaded, ?_, heap2.trans (heap1.trans heap0), stack2.trans (stack1.trans stack0),
      output2.trans (output1.trans output0), ?_, running2, ?_, ?_⟩
    · simpa only [live0, live1, Nat.max_self, Nat.reduceAdd] using t0.append (t1.append t2)
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using pc2
    · rw [held2]
      have actualCell : addressed.heap[(addressed.reg 0).val]? = some value := by
        simpa only [actualAddress, heap1, heap0] using cell
      simpa using (Array.getElem?_eq_some_iff.mp actualCell).2
    · intro register notZero notOne
      rw [frame2 register notOne, frame1 register notZero, frame0]
  | true =>
    obtain ⟨branched, t0, pc0, heap0, stack0, output0, running0, frame0⟩ :=
      EnumerationSteps.branch_skipped (program := program) state entry (entry + 3) 2 position running (by omega)
        (by rw [flag]; simp [boolWord, word, Nat.mod_eq_of_lt oneFits])
        (by simpa [code] using present 0 (by simp))
    obtain ⟨cleared, t1, pc1, held1, heap1, stack1, output1, running1, frame1⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 1) 0 1 branched pc0 running0 (by omega)
        (by simpa [code, boolWord] using present 1 (by simp))
    obtain ⟨loaded, t2, pc2, heap2, stack2, output2, running2, frame2⟩ :=
      EnumerationSteps.branch_taken (program := program) cleared (entry + 1 + 1) (entry + 5) 7 pc1 running1 (by omega)
        (by rw [frame1 7 (by decide), frame0, zero]; simp [word])
        (by simpa [code, Nat.add_assoc] using present 2 (by simp))
    have live0 : branched.liveWords = state.liveWords := by simp only [State.liveWords, heap0, stack0, output0]
    have live1 : cleared.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, output1, heap0, stack0, output0]
    refine ⟨loaded, ?_, heap2.trans (heap1.trans heap0), stack2.trans (stack1.trans stack0),
      output2.trans (output1.trans output0), pc2, running2, ?_, ?_⟩
    · simpa only [live0, live1, Nat.max_self, Nat.reduceAdd] using t0.append (t1.append t2)
    · rw [frame2, held1]; rfl
    · intro register notZero notOne
      rw [frame2, frame1 register notOne, frame0]

theorem execution (program : Program width 8) (state : State width 8)
    (entry address : Nat) (targetPresent : Bool) (value : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (flag : state.reg 2 = boolWord width targetPresent) (zero : state.reg 7 = word width 0)
    (widthPositive : 0 < width) (room : entry + 6 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (valid : address < state.heap.size)
    (cell : state.heap[address]? = some value)
    (present : SharedRootRead.BlockAt program entry (code width entry address)) :
    ∃ final, Execution program state final 4 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (if targetPresent then boolWord width false else value) :: state.output ∧
      final.pc = word width (entry + 6) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  obtain ⟨loaded, prelude, heap, stack, output, pc, live, held, frame⟩ :=
    prepare program state entry address targetPresent value position running flag zero widthPositive room heapFits valid cell present
  obtain ⟨final, last, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame, finalLive⟩ :=
    EnumerationSteps.emit_execution (program := program) loaded (entry + 5) 1 pc live (by omega)
      (by simpa [code] using present 5 (by simp))
  have sameLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, finalHeap.trans heap, finalStack.trans stack, ?_, ?_, finalRunning, ?_⟩
  · simpa only [sameLive, Nat.max_eq_right (Nat.le_succ _), Nat.reduceAdd] using prelude.append last
  · rw [finalOutput, held, output]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · intro register notZero notOne; rw [finalFrame, frame register notZero notOne]

end Controller.Cost.EnumerationMaskedEmit
