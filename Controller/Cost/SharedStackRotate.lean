module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessCopy

@[expose] public section

/-! Two stack blocks are exchanged through temporary heap storage, which is fully reclaimed. -/
namespace Controller.Cost.SharedStackRotate
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

@[irreducible] def code (width base first second entry done : Nat) : Program width 8 :=
  (SharedWitnessPark.code width first).toArray ++
    ((SharedWitnessPark.code width second).toArray ++
      (SharedWitnessCopy.code width (entry + 2 * first + 2 * second)
        (entry + 2 * first + 2 * second + 10) base first ++
        (SharedWitnessCopy.code width (entry + 2 * first + 2 * second + 10)
          (entry + 2 * first + 2 * second + 20) (base + first) second ++
          SharedEvaluationReclaim.code width (entry + 2 * first + 2 * second + 20) done (first + second))))

@[simp] theorem code_size (width base first second entry done : Nat) :
    (code width base first second entry done).size = 2 * first + 2 * second + 27 := by
  unfold code; simp; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (retained : Array (Word width)) (first second suffix : List (Word width)) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * first.length + 2 * second.length + 27 < 2 ^ width)
    (positive : 0 < retained.size)
    (capacity : retained.size + first.length + second.length < 2 ^ width)
    (heapStored : state.heap = retained) (input : state.stack = first ++ second ++ suffix)
    (physical : CodeAt resident entry (code width retained.size first.length second.length entry done)) :
    ∃ final peak, Execution resident state final (12 * (first.length + second.length) + 14) peak ∧
      peak ≤ state.liveWords + first.length + second.length ∧
      final.heap = retained ∧ final.stack = second ++ first ++ suffix ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  have all := physical
  unfold code at all
  have firstCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail1 := RawSharedOrdered.takeSuffix resident entry _ _ all
  have rest1 : CodeAt resident (entry + 2 * first.length)
      ((SharedWitnessPark.code width second.length).toArray ++
        (SharedWitnessCopy.code width (entry + 2 * first.length + 2 * second.length)
          (entry + 2 * first.length + 2 * second.length + 10) retained.size first.length ++
          (SharedWitnessCopy.code width (entry + 2 * first.length + 2 * second.length + 10)
            (entry + 2 * first.length + 2 * second.length + 20) (retained.size + first.length) second.length ++
            SharedEvaluationReclaim.code width (entry + 2 * first.length + 2 * second.length + 20)
              done (first.length + second.length)))) := by simpa using tail1
  have secondCode := RawSharedOrdered.takePrefix resident (entry + 2 * first.length) _ _ rest1
  have tail2 := RawSharedOrdered.takeSuffix resident (entry + 2 * first.length) _ _ rest1
  have rest2 : CodeAt resident (entry + 2 * first.length + 2 * second.length)
      (SharedWitnessCopy.code width (entry + 2 * first.length + 2 * second.length)
        (entry + 2 * first.length + 2 * second.length + 10) retained.size first.length ++
        (SharedWitnessCopy.code width (entry + 2 * first.length + 2 * second.length + 10)
          (entry + 2 * first.length + 2 * second.length + 20) (retained.size + first.length) second.length ++
          SharedEvaluationReclaim.code width (entry + 2 * first.length + 2 * second.length + 20)
            done (first.length + second.length))) := by simpa using tail2
  have copyFirstCode := RawSharedOrdered.takePrefix resident (entry + 2 * first.length + 2 * second.length) _ _ rest2
  have tail3 := RawSharedOrdered.takeSuffix resident (entry + 2 * first.length + 2 * second.length) _ _ rest2
  have rest3 : CodeAt resident (entry + 2 * first.length + 2 * second.length + 10)
      (SharedWitnessCopy.code width (entry + 2 * first.length + 2 * second.length + 10)
        (entry + 2 * first.length + 2 * second.length + 20) (retained.size + first.length) second.length ++
        SharedEvaluationReclaim.code width (entry + 2 * first.length + 2 * second.length + 20)
          done (first.length + second.length)) := by simpa using tail3
  have copySecondCode := RawSharedOrdered.takePrefix resident (entry + 2 * first.length + 2 * second.length + 10) _ _ rest3
  have releaseCode := RawSharedOrdered.takeSuffix resident (entry + 2 * first.length + 2 * second.length + 10) _ _ rest3
  have firstBlock : SharedRootRead.BlockAt resident entry (SharedWitnessPark.code width first.length) := by
    intro offset bound; simpa using firstCode ⟨offset, by simpa using bound⟩
  obtain ⟨parkedFirst, trace1, heap1, stack1, output1, pc1, active1, frame1⟩ :=
    SharedWitnessPark.execution resident state first (second ++ suffix) entry position running (by omega)
      (by rw [heapStored]; omega) (by simpa only [List.append_assoc] using input) firstBlock
  have secondBlock : SharedRootRead.BlockAt resident (entry + 2 * first.length)
      (SharedWitnessPark.code width second.length) := by
    intro offset bound; simpa using secondCode ⟨offset, by simpa using bound⟩
  obtain ⟨parked, trace2, heap2, stack2, output2, pc2, active2, frame2⟩ :=
    SharedWitnessPark.execution resident parkedFirst second suffix (entry + 2 * first.length) pc1 active1
      (by omega) (by rw [heap1, heapStored]; simp only [Array.size_append, List.size_toArray]; omega) stack1 secondBlock
  have parkedHeap : parked.heap = retained ++ first.toArray ++ second.toArray := by
    rw [heap2, heap1, heapStored]
  have firstCells : ∀ index : Nat, ∀ valid : index < first.length,
      parked.heap[retained.size + index]? = some first[index] := by
    intro index valid
    rw [parkedHeap]
    simp [Array.getElem?_append, valid, List.getElem?_append_left valid]
  obtain ⟨copiedFirst, peak3, trace3, space3, heap3, stack3, output3, pc3, active3, frame3⟩ :=
    SharedWitnessCopy.execution resident parked retained.size first
      (entry + 2 * first.length + 2 * second.length) (entry + 2 * first.length + 2 * second.length + 10)
      pc2 active2 (by omega) positive (by omega) firstCells copyFirstCode
  have secondCells : ∀ index : Nat, ∀ valid : index < second.length,
      copiedFirst.heap[retained.size + first.length + index]? = some second[index] := by
    intro index valid
    rw [heap3, parkedHeap]
    simp [Array.getElem?_append, valid, show ¬ retained.size + first.length + index < retained.size from by omega,
      Nat.add_assoc, List.getElem?_append_right (by omega : first.length ≤ first.length + index)]
  obtain ⟨copied, peak4, trace4, space4, heap4, stack4, output4, pc4, active4, frame4⟩ :=
    SharedWitnessCopy.execution resident copiedFirst (retained.size + first.length) second
      (entry + 2 * first.length + 2 * second.length + 10) (entry + 2 * first.length + 2 * second.length + 20)
      pc3 active3 (by omega) (by omega) capacity secondCells copySecondCode
  obtain ⟨final, trace5, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalZero, finalSix, finalSeven, finalFrame⟩ :=
    SharedGraphReclaim.setup_execution resident copied (entry + 2 * first.length + 2 * second.length + 20) done
      retained (first ++ second) pc4 active4 (by omega)
      (by rw [heap4, heap3, parkedHeap]; simp only [List.append_toArray, Array.append_assoc])
      (by simp only [List.length_append]; omega) (by simpa using releaseCode)
  have live1 : parkedFirst.liveWords = state.liveWords := by
    simp only [State.liveWords, heap1, stack1, output1, input, Array.size_append, List.size_toArray, List.length_append]; omega
  have live2 : parked.liveWords = state.liveWords := by
    simp only [State.liveWords, heap2, stack2, output2, heap1, stack1, output1, input,
      Array.size_append, List.size_toArray, List.length_append]; omega
  have live3 : copiedFirst.liveWords = state.liveWords + first.length := by
    simp only [State.liveWords, heap3, stack3, output3, List.length_append]
    have storage := live2
    simp only [State.liveWords] at storage
    omega
  have live4 : copied.liveWords = state.liveWords + first.length + second.length := by
    simp only [State.liveWords, heap4, stack4, output4, List.length_append]
    have storage := live3
    simp only [State.liveWords] at storage
    omega
  have joined := trace1.append (trace2.append (trace3.append (trace4.append trace5)))
  refine ⟨final, max state.liveWords (max parkedFirst.liveWords (max peak3 (max peak4 copied.liveWords))),
    ?_, ?_, finalHeap, ?_, finalOutput.trans (output4.trans (output3.trans (output2.trans output1))),
    finalPC, finalRunning, ?_⟩
  · convert joined using 1 <;> simp only [List.length_append] <;> omega
  · rw [live1, live4]
    rw [live2] at space3
    rw [live3] at space4
    omega
  · simpa only [stack4, stack3, stack2, List.append_assoc] using finalStack
  · exact (finalFrame 4 (by decide) (by decide) (by decide)).trans
      (frame4.trans (frame3.trans ((frame2 4 (by decide)).trans (frame1 4 (by decide)))))

end Controller.Cost.SharedStackRotate
