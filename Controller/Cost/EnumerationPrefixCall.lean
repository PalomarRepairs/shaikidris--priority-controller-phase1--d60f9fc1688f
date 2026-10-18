module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationPrefixReturn
public import Controller.Cost.RetainedSuffixReclaim

@[expose] public section

/-! A single fixed caller block saves depth/mode, copies the mutable prefix to
the oracle stack, reclaims the prefix heap region and enters the shared oracle. -/
namespace Controller.Cost.EnumerationPrefixCall
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width entry oracle target base count : Nat) : List (Instruction width 8) :=
  [.push 5, .push 3] ++
  ((SharedWitnessCopy.code width (entry + 2) (entry + 12) base count).toList ++
  ((SharedEvaluationReclaim.code width (entry + 12) (entry + 19) count).toList ++
  [.constant 4 (word width target), .constant 0 (word width 0), .branchZero 0 (word width oracle)]))

@[simp] theorem code_length : (code width entry oracle target base count).length = 22 := by
  simp [code, SharedWitnessCopy.code_size, SharedEvaluationReclaim.code_size]

private theorem left_at (program : Program width 8) (entry : Nat)
    (first rest : List (Instruction width 8)) (present : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program entry first := by
  intro offset below
  have whole := present offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left below] at whole
  exact whole

private theorem right_at (program : Program width 8) (entry : Nat)
    (first rest : List (Instruction width 8)) (present : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program (entry + first.length) rest := by
  intro offset below
  have whole := present (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at whole
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using whole

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (entry oracle target : Nat) (packet : Array (Word width)) (masks : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = packet ++ masks.toArray) (positive : 0 < packet.size)
    (room : entry + 22 < 2 ^ width) (heapFits : packet.size + masks.length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width entry oracle target packet.size masks.length)) :
    ∃ final peak, Execution program state final (10 * masks.length + 14) peak ∧
      peak ≤ state.liveWords + masks.length + 2 ∧
      final.heap = packet ∧ final.stack = masks ++ state.reg 3 :: state.reg 5 :: state.stack ∧
      final.output = state.output ∧ final.pc = word width oracle ∧ final.halted = false ∧
      final.reg 4 = word width target := by
  unfold code at present
  have saveAt := left_at program entry _ _ present
  have rest0 := right_at program entry _ _ present
  simp only [List.length_cons, List.length_nil] at rest0
  have copyAt := left_at program (entry + 2) _ _ rest0
  have rest1 := right_at program (entry + 2) _ _ rest0
  simp only [Array.length_toList, SharedWitnessCopy.code_size, Nat.add_assoc, Nat.reduceAdd] at rest1
  have releaseAt := left_at program (entry + 12) _ _ rest1
  have rest2 := right_at program (entry + 12) _ _ rest1
  simp only [Array.length_toList, SharedEvaluationReclaim.code_size, Nat.add_assoc, Nat.reduceAdd] at rest2
  obtain ⟨savedMode, t0, pc0, heap0, stack0, output0, running0, frame0, live0⟩ :=
    EnumerationSteps.push_execution (program := program) state entry 5 position running (by omega)
      (by simpa using saveAt 0 (by simp))
  obtain ⟨saved, t1, pc1, heap1, stack1, output1, running1, frame1, live1⟩ :=
    EnumerationSteps.push_execution (program := program) savedMode (entry + 1) 3 pc0 running0 (by omega)
      (by simpa using saveAt 1 (by simp))
  have savedHeap : saved.heap = packet ++ masks.toArray := heap1.trans (heap0.trans heapStored)
  have savedStack : saved.stack = state.reg 3 :: state.reg 5 :: state.stack := by
    rw [stack1, frame0, stack0]
  have maskCells : ∀ index : Nat, ∀ below : index < masks.length,
      saved.heap[packet.size + index]? = some masks[index] := by
    intro index below
    rw [savedHeap]
    simp [below]
  obtain ⟨copied, copyPeak, t2, copySpace, copyHeap, copyStack, copyOutput, copyPC, copyRunning, copyHead⟩ :=
    SharedWitnessCopy.execution program saved packet.size masks (entry + 2) (entry + 12)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc1) running1 (by omega) positive heapFits maskCells
      (by intro phase; simpa only [Array.getElem?_toList] using copyAt phase.val (by simpa using phase.isLt))
  obtain ⟨reclaimed, t3, releaseHeap, releaseStack, releaseOutput, releasePC, releaseRunning,
      releaseZero, releaseSix, releaseSeven, releaseFrame⟩ :=
    RetainedSuffixReclaim.execution program copied (entry + 12) (entry + 19) packet masks copyPC copyRunning
      (by omega) (copyHeap.trans savedHeap) (by omega)
      (by intro phase; simpa only [Array.getElem?_toList] using releaseAt phase.val (by simpa using phase.isLt))
  obtain ⟨targeted, t4, targetPC, targetValue, targetHeap, targetStack, targetOutput, targetRunning, targetFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 19) target 4 reclaimed releasePC releaseRunning (by omega)
      (by simpa using rest2 0 (by simp))
  have jumpAt : SharedRootRead.BlockAt program (entry + 20)
      [.constant 0 (word width 0), .branchZero 0 (word width oracle)] := by
    have shifted := right_at program (entry + 19) [.constant 4 (word width target)]
      [.constant 0 (word width 0), .branchZero 0 (word width oracle)] rest2
    simpa using shifted
  obtain ⟨final, t5, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    EnumerationOracle.jump_execution program targeted (entry + 20) oracle
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using targetPC) targetRunning (by omega) jumpAt
  have savedLive : saved.liveWords = state.liveWords + 2 := by omega
  have copiedLive : copied.liveWords = state.liveWords + 2 + masks.length := by
    simp only [State.liveWords, copyHeap, copyStack, copyOutput, List.length_append] at savedLive ⊢
    omega
  have reclaimedLive : reclaimed.liveWords ≤ state.liveWords + 2 + masks.length := by
    simp only [State.liveWords, releaseHeap, releaseStack, releaseOutput, copyHeap, copyStack,
      copyOutput, savedHeap, Array.size_append, List.size_toArray] at copiedLive ⊢
    omega
  have targetedLive : targeted.liveWords = reclaimed.liveWords := by
    simp only [State.liveWords, targetHeap, targetStack, targetOutput]
  have joined := t0.append (t1.append (t2.append (t3.append (t4.append t5))))
  refine ⟨final, max (state.liveWords + 1) (max (savedMode.liveWords + 1)
    (max copyPeak (max copied.liveWords (max reclaimed.liveWords targeted.liveWords)))), ?_, ?_, finalHeap.trans (targetHeap.trans releaseHeap), ?_,
    finalOutput.trans (targetOutput.trans (releaseOutput.trans (copyOutput.trans (output1.trans output0)))),
    finalPC, finalRunning, (finalFrame 4 (by decide)).trans targetValue⟩
  · convert joined using 1; omega
  · rw [savedLive] at copySpace
    simp only [max_le_iff]
    omega
  · rw [finalStack, targetStack, releaseStack, copyStack, savedStack]

end Controller.Cost.EnumerationPrefixCall
