module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootAggregate

@[expose] public section

/-! Witnesses are restored to the caller stack and their temporary heap suffix is released. -/
namespace Controller.Cost.SharedWitnessRestore
open Controller.Cost.RawTransferLoops

def code (width entry done count : Nat) : Program width 8 :=
  reverseSaveCode width entry (entry + 6) ++
    SharedEvaluationReclaim.code width (entry + 6) done count

@[simp] theorem code_size (width entry done count : Nat) :
    (code width entry done count).size = 13 := by simp [code]

theorem execution (resident : Program width 8) (state : State width 8)
    (retained : Array (Word width)) (witnesses : List (Word width)) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 13 < 2 ^ width) (positive : 0 < retained.size)
    (heapFits : retained.size + witnesses.length < 2 ^ width)
    (heapStored : state.heap = retained ++ witnesses.toArray)
    (countReg : state.reg 0 = word width witnesses.length)
    (cursorReg : state.reg 1 = word width (retained.size + witnesses.length - 1))
    (maskReg : state.reg 7 = word width (2 ^ width - 1)) (zeroReg : state.reg 6 = word width 0)
    (physical : CodeAt resident entry (code width entry done witnesses.length)) :
    ∃ final, Execution resident state final (10 * witnesses.length + 5)
      (state.liveWords + witnesses.length) ∧
      final.heap = retained ∧ final.stack = witnesses ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = state.reg 4 ∧ final.reg 2 = state.reg 2 := by
  have all := physical
  unfold code at all
  have saveCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have releaseCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have cells : ∀ index : Nat, ∀ h : index < witnesses.length,
      state.heap[retained.size + index]? = some witnesses[index] := by
    intro index valid
    rw [heapStored]
    simp [Array.getElem?_append, valid]
  obtain ⟨ready, peak, saveTrace, saveBound, savedHeap, savedStack, savedOutput,
    savedPC, savedRunning, savedZero, savedFrame⟩ :=
    reverse_save_execution resident entry (entry + 6) retained.size witnesses state position running
      (by omega) positive (by omega) (by omega) countReg cursorReg maskReg zeroReg cells saveCode
  obtain ⟨final, releaseTrace, heap, stack, output, pc, active, zero, six, seven, frame⟩ :=
    SharedGraphReclaim.setup_execution resident ready (entry + 6) done retained witnesses
      savedPC savedRunning (by omega) (savedHeap.trans heapStored) (by omega)
      (by simpa only [reverseSaveCode_size] using releaseCode)
  have readyLive : ready.liveWords = state.liveWords + witnesses.length := by
    simp only [State.liveWords, savedHeap, savedStack, savedOutput, List.length_append]
    omega
  have peakEq : peak = state.liveWords + witnesses.length := by
    have finalBound := Execution.final_storage_le saveTrace
    omega
  have joined := saveTrace.append releaseTrace
  rw [peakEq, readyLive, Nat.max_self] at joined
  have timeEq : (6 * witnesses.length + 1) + (4 * witnesses.length + 4) =
      10 * witnesses.length + 5 := by omega
  rw [timeEq] at joined
  refine ⟨final, joined, heap, stack.trans savedStack, output.trans savedOutput, pc, active, ?_, ?_⟩
  · exact (frame 4 (by decide) (by decide) (by decide)).trans
      (savedFrame 4 (by decide) (by decide) (by decide))
  · exact (frame 2 (by decide) (by decide) (by decide)).trans
      (savedFrame 2 (by decide) (by decide) (by decide))


def preparedCode (width entry done retained count : Nat) : Program width 8 :=
  #[.constant 0 (word width count), .constant 1 (word width (retained + count - 1)),
    .constant 6 (word width 0), .constant 7 (word width (2 ^ width - 1))] ++
    code width (entry + 4) done count

@[simp] theorem preparedCode_size (width entry done retained count : Nat) :
    (preparedCode width entry done retained count).size = 17 := by simp [preparedCode]

theorem prepared_execution (resident : Program width 8) (state : State width 8)
    (retained : Array (Word width)) (witnesses : List (Word width)) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 17 < 2 ^ width) (positive : 0 < retained.size)
    (heapFits : retained.size + witnesses.length < 2 ^ width)
    (heapStored : state.heap = retained ++ witnesses.toArray)
    (physical : CodeAt resident entry
      (preparedCode width entry done retained.size witnesses.length)) :
    ∃ final, Execution resident state final (10 * witnesses.length + 9)
      (state.liveWords + witnesses.length) ∧
      final.heap = retained ∧ final.stack = witnesses ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = state.reg 4 ∧ final.reg 2 = state.reg 2 := by
  have all := physical
  unfold preparedCode at all
  have setup := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  obtain ⟨s1, t1, p1, v1, h1, k1, o1, a1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry witnesses.length 0 state position running (by omega)
      (by simpa using setup ⟨0, by simp⟩)
  obtain ⟨s2, t2, p2, v2, h2, k2, o2, a2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 1) (retained.size + witnesses.length - 1)
      1 s1 p1 a1 (by omega) (by simpa using setup ⟨1, by simp⟩)
  obtain ⟨s3, t3, p3, v3, h3, k3, o3, a3, f3⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 2) 0 6 s2
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p2) a2 (by omega)
      (by simpa using setup ⟨2, by simp⟩)
  obtain ⟨ready, t4, p4, v4, h4, k4, o4, a4, f4⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 3) (2 ^ width - 1) 7 s3
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p3) a3 (by omega)
      (by simpa using setup ⟨3, by simp⟩)
  obtain ⟨final, trace, heap, stack, output, pc, active, frame, frame2⟩ :=
    execution resident ready retained witnesses (entry + 4) done
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p4) a4 (by omega) positive heapFits
      (h4.trans (h3.trans (h2.trans (h1.trans heapStored))))
      (by rw [f4 0 (by decide), f3 0 (by decide), f2 0 (by decide)]; exact v1)
      (by rw [f4 1 (by decide), f3 1 (by decide)]; exact v2) v4
      (by rw [f4 6 (by decide)]; exact v3)
      (by simpa using tail)
  have live1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, k1, o1]
  have live2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, k2, o2, h1, k1, o1]
  have live3 : s3.liveWords = state.liveWords := by simp only [State.liveWords, h3, k3, o3, h2, k2, o2, h1, k1, o1]
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, h4, k4, o4, h3, k3, o3, h2, k2, o2, h1, k1, o1]
  have joined := t1.append (t2.append (t3.append (t4.append trace)))
  have timeEq : 1 + (1 + (1 + (1 + (10 * witnesses.length + 5)))) = 10 * witnesses.length + 9 := by omega
  have peakEq : max state.liveWords (max s1.liveWords (max s2.liveWords
      (max s3.liveWords (ready.liveWords + witnesses.length)))) = state.liveWords + witnesses.length := by
    rw [live1, live2, live3, readyLive]
    omega
  rw [timeEq, peakEq] at joined
  refine ⟨final, joined, heap, ?_, output.trans (o4.trans (o3.trans (o2.trans o1))), pc, active, ?_, ?_⟩
  · simpa only [k4, k3, k2, k1] using stack
  · exact frame.trans ((f4 4 (by decide)).trans ((f3 4 (by decide)).trans
      ((f2 4 (by decide)).trans (f1 4 (by decide)))))
  · exact frame2.trans ((f4 2 (by decide)).trans ((f3 2 (by decide)).trans
      ((f2 2 (by decide)).trans (f1 2 (by decide)))))

end Controller.Cost.SharedWitnessRestore
