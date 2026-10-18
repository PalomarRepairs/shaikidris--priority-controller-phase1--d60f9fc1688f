module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessCopy

@[expose] public section

/-! Fixed-coordinate masks are copied once to the retained stack suffix for reuse by zero queries. -/
namespace Controller.Cost.SharedConstraintCopy
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

@[irreducible] def code (width base count entry done : Nat) : Program width 8 :=
  (SharedWitnessPark.code width count).toArray ++
    (SharedWitnessCopy.code width (entry + 2 * count) (entry + 2 * count + 10) base count ++
      (SharedWitnessCopy.code width (entry + 2 * count + 10) (entry + 2 * count + 20) base count ++
        SharedEvaluationReclaim.code width (entry + 2 * count + 20) done count))

@[simp] theorem code_size (width base count entry done : Nat) :
    (code width base count entry done).size = 2 * count + 27 := by unfold code; simp

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (retained : Array (Word width)) (masks suffix : List (Word width)) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * masks.length + 27 < 2 ^ width) (positive : 0 < retained.size)
    (capacity : retained.size + masks.length < 2 ^ width)
    (heapStored : state.heap = retained) (input : state.stack = masks ++ suffix)
    (physical : CodeAt resident entry (code width retained.size masks.length entry done)) :
    ∃ final peak, Execution resident state final (18 * masks.length + 14) peak ∧
      peak ≤ state.liveWords + 2 * masks.length ∧
      final.heap = retained ∧ final.stack = masks ++ masks ++ suffix ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  have all := physical
  unfold code at all
  have parkCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail1 := RawSharedOrdered.takeSuffix resident entry _ _ all
  have rest1 : CodeAt resident (entry + 2 * masks.length)
      (SharedWitnessCopy.code width (entry + 2 * masks.length) (entry + 2 * masks.length + 10) retained.size masks.length ++
        (SharedWitnessCopy.code width (entry + 2 * masks.length + 10) (entry + 2 * masks.length + 20) retained.size masks.length ++
          SharedEvaluationReclaim.code width (entry + 2 * masks.length + 20) done masks.length)) := by simpa using tail1
  have firstCode := RawSharedOrdered.takePrefix resident (entry + 2 * masks.length) _ _ rest1
  have tail2 := RawSharedOrdered.takeSuffix resident (entry + 2 * masks.length) _ _ rest1
  have rest2 : CodeAt resident (entry + 2 * masks.length + 10)
      (SharedWitnessCopy.code width (entry + 2 * masks.length + 10) (entry + 2 * masks.length + 20) retained.size masks.length ++
        SharedEvaluationReclaim.code width (entry + 2 * masks.length + 20) done masks.length) := by simpa using tail2
  have secondCode := RawSharedOrdered.takePrefix resident (entry + 2 * masks.length + 10) _ _ rest2
  have releaseCode := RawSharedOrdered.takeSuffix resident (entry + 2 * masks.length + 10) _ _ rest2
  have parkBlock : SharedRootRead.BlockAt resident entry (SharedWitnessPark.code width masks.length) := by
    intro offset valid; simpa using parkCode ⟨offset, by simpa using valid⟩
  obtain ⟨parked, parkTrace, parkedHeap, parkedStack, parkedOutput, parkedPC, parkedRunning, parkedFrame⟩ :=
    SharedWitnessPark.execution resident state masks suffix entry position running (by omega)
      (by rw [heapStored]; exact capacity) input parkBlock
  have cells : ∀ index : Nat, ∀ valid : index < masks.length,
      parked.heap[retained.size + index]? = some masks[index] := by
    intro index valid
    rw [parkedHeap, heapStored]
    simp [Array.getElem?_append, valid]
  obtain ⟨first, firstPeak, firstTrace, firstSpace, firstHeap, firstStack, firstOutput, firstPC, firstRunning, firstFrame⟩ :=
    SharedWitnessCopy.execution resident parked retained.size masks (entry + 2 * masks.length)
      (entry + 2 * masks.length + 10) parkedPC parkedRunning (by omega) positive capacity cells firstCode
  obtain ⟨second, secondPeak, secondTrace, secondSpace, secondHeap, secondStack, secondOutput, secondPC, secondRunning, secondFrame⟩ :=
    SharedWitnessCopy.execution resident first retained.size masks (entry + 2 * masks.length + 10)
      (entry + 2 * masks.length + 20) firstPC firstRunning (by omega) positive capacity
      (by simpa only [firstHeap] using cells) secondCode
  obtain ⟨final, releaseTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
    finalZero, finalSix, finalSeven, finalFrame⟩ :=
    SharedGraphReclaim.setup_execution resident second (entry + 2 * masks.length + 20) done retained masks
      secondPC secondRunning (by omega) (by rw [secondHeap, firstHeap, parkedHeap, heapStored])
      (by omega) (by simpa using releaseCode)
  have parkedLive : parked.liveWords = state.liveWords := by
    simp only [State.liveWords, parkedHeap, parkedStack, parkedOutput, input,
      Array.size_append, List.size_toArray, List.length_append]; omega
  have firstLive : first.liveWords = state.liveWords + masks.length := by
    have storage := parkedLive
    simp only [State.liveWords] at storage
    simp only [State.liveWords, firstHeap, firstStack, firstOutput, List.length_append]
    omega
  have secondLive : second.liveWords = state.liveWords + 2 * masks.length := by
    have storage := firstLive
    simp only [State.liveWords] at storage
    simp only [State.liveWords, secondHeap, secondStack, secondOutput, List.length_append]
    omega
  have joined := parkTrace.append (firstTrace.append (secondTrace.append releaseTrace))
  refine ⟨final, max state.liveWords (max firstPeak (max secondPeak second.liveWords)), ?_, ?_,
    finalHeap, ?_, finalOutput.trans (secondOutput.trans (firstOutput.trans parkedOutput)), finalPC, finalRunning, ?_⟩
  · convert joined using 1 <;> omega
  · rw [parkedLive] at firstSpace
    rw [firstLive] at secondSpace
    rw [secondLive]
    omega
  · simpa only [secondStack, firstStack, parkedStack, List.append_assoc] using finalStack
  · exact (finalFrame 4 (by decide) (by decide) (by decide)).trans
      (secondFrame.trans (firstFrame.trans (parkedFrame 4 (by decide))))

end Controller.Cost.SharedConstraintCopy
