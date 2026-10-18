module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverControl

@[expose] public section

/-! Actual initialization and drive-zero exhaustion of the enumeration driver. -/
namespace Controller.Cost.EnumerationDriverInitial
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def code (width : Nat) (drive : Bool) (masks : List (Word width)) (call halt : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width (if drive then 1 else 0)), .branchZero 0 (word width halt)] ++
    (EnumerationDriverCode.allocateWords masks ++
    ([.constant 3 (word width 0)] ++ EnumerationDriverControl.modeCode width 0 call))

@[simp] theorem code_length : (code width drive masks call halt).length = 2 * masks.length + 6 := by
  simp [code, EnumerationDriverCode.allocateWords_length]

theorem drive_false (program : Program width 8) (state : State width 8)
    (entry call halt : Nat) (masks : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (haltFits : halt + 1 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width false masks call halt))
    (haltAt : program[halt]? = some .halt) :
    ∃ final, Execution program state final 3 state.liveWords ∧ final.halted = true ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output := by
  obtain ⟨cleared, t0, pc0, held0, heap0, stack0, output0, running0, frame0⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 0 0 state position running (by omega)
      (by simpa [code] using present 0 (by simp [code]))
  obtain ⟨branched, t1, pc1, heap1, stack1, output1, running1, frame1⟩ :=
    EnumerationSteps.branch_taken (program := program) cleared (entry + 1) halt 0 pc0 running0 (by omega)
      (by rw [held0]; simp [word]) (by simpa [code] using present 1 (by simp [code]))
  obtain ⟨final, t2, halted, heap2, stack2, output2⟩ :=
    EnumerationSteps.halt_execution (program := program) branched halt pc1 running1 haltFits haltAt
  have live0 : cleared.liveWords = state.liveWords := by simp only [State.liveWords, heap0, stack0, output0]
  have live1 : branched.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, output1, heap0, stack0, output0]
  refine ⟨final, ?_, halted, heap2.trans (heap1.trans heap0), stack2.trans (stack1.trans stack0), output2.trans (output1.trans output0)⟩
  simpa only [live0, live1, Nat.max_self, Nat.reduceAdd] using t0.append (t1.append t2)

theorem drive_true (program : Program width 8) (state : State width 8)
    (entry call halt : Nat) (masks : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (widthPositive : 0 < width) (room : entry + 2 * masks.length + 6 < 2 ^ width)
    (heapFits : state.heap.size + masks.length ≤ 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width true masks call halt)) :
    ∃ final, Execution program state final (2 * masks.length + 6) (state.liveWords + masks.length) ∧
      final.heap = state.heap ++ masks.toArray ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width call ∧ final.halted = false ∧
      final.reg 3 = word width 0 ∧ final.reg 5 = word width 0 := by
  have oneFits : 1 < 2 ^ width := Nat.one_lt_two_pow_iff.mpr (by omega)
  obtain ⟨flagged, t0, pc0, held0, heap0, stack0, output0, running0, frame0⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 1 0 state position running (by omega)
      (by simpa [code] using present 0 (by simp [code]))
  obtain ⟨branched, t1, pc1, heap1, stack1, output1, running1, frame1⟩ :=
    EnumerationSteps.branch_skipped (program := program) flagged (entry + 1) halt 0 pc0 running0 (by omega)
      (by rw [held0]; simp [word, Nat.mod_eq_of_lt oneFits]) (by simpa [code] using present 1 (by simp [code]))
  have afterFlag := block_right program entry
    [.constant 0 (word width 1), .branchZero 0 (word width halt)]
    (EnumerationDriverCode.allocateWords masks ++ [.constant 3 (word width 0)] ++ EnumerationDriverControl.modeCode width 0 call) (by simpa [code, List.append_assoc] using present)
  simp only [List.length_cons, List.length_nil, List.append_assoc] at afterFlag
  have allocAt := block_left program (entry + 2) (EnumerationDriverCode.allocateWords masks)
    ([.constant 3 (word width 0)] ++ EnumerationDriverControl.modeCode width 0 call) afterFlag
  have allocTail := block_right program (entry + 2) (EnumerationDriverCode.allocateWords masks)
    ([.constant 3 (word width 0)] ++ EnumerationDriverControl.modeCode width 0 call) afterFlag
  simp only [EnumerationDriverCode.allocateWords_length] at allocTail
  obtain ⟨allocated, t2, allocHeap, allocStack, allocOutput, allocPC, allocRunning, allocFrame⟩ :=
    EnumerationDriverAllocate.execution program branched (entry + 2) masks
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc1) running1 (by omega)
      (by rw [heap1, heap0]; exact heapFits) allocAt
  obtain ⟨counter, t3, counterPC, counterValue, counterHeap, counterStack, counterOutput, counterRunning, counterFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 2 + 2 * masks.length) 0 3 allocated allocPC allocRunning (by omega)
      (by simpa only [List.singleton_append, List.getElem?_cons_zero, Nat.add_zero] using allocTail 0 (by simp [EnumerationDriverControl.modeCode]))
  have modeAt : SharedRootRead.BlockAt program (entry + 2 + 2 * masks.length + 1) (EnumerationDriverControl.modeCode width 0 call) := by
    simpa using block_right program (entry + 2 + 2 * masks.length) [.constant 3 (word width 0)]
      (EnumerationDriverControl.modeCode width 0 call) allocTail
  obtain ⟨final, t4, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalMode, finalFrame⟩ :=
    EnumerationDriverControl.mode_execution program counter (entry + 2 + 2 * masks.length + 1) 0 call counterPC counterRunning (by omega) modeAt
  have live0 : flagged.liveWords = state.liveWords := by simp only [State.liveWords, heap0, stack0, output0]
  have live1 : branched.liveWords = state.liveWords := by simp only [State.liveWords, heap1, stack1, output1, heap0, stack0, output0]
  have live2 : allocated.liveWords = state.liveWords + masks.length := by
    simp only [State.liveWords, allocHeap, allocStack, allocOutput, heap1, stack1, output1, heap0, stack0, output0,
      Array.size_append, List.size_toArray]; omega
  have live3 : counter.liveWords = state.liveWords + masks.length := by
    simp only [State.liveWords, counterHeap, counterStack, counterOutput] at live2 ⊢; exact live2
  have joined := t0.append (t1.append (t2.append (t3.append t4)))
  refine ⟨final, ?_, ?_, finalStack.trans (counterStack.trans (allocStack.trans (stack1.trans stack0))),
    finalOutput.trans (counterOutput.trans (allocOutput.trans (output1.trans output0))), finalPC, finalRunning,
    (finalFrame 3 (by decide) (by decide)).trans counterValue, finalMode⟩
  · rw [live0, live1, live2, live3] at joined
    have peak : max state.liveWords (max state.liveWords (max (state.liveWords + masks.length)
        (max (state.liveWords + masks.length) (state.liveWords + masks.length)))) = state.liveWords + masks.length := by omega
    rw [peak] at joined
    convert joined using 1; omega
  · rw [finalHeap, counterHeap, allocHeap, heap1, heap0]

end Controller.Cost.EnumerationDriverInitial
