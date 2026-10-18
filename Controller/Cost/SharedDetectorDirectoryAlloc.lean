module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorData
public import Controller.Cost.SharedDetectorPrepare

@[expose] public section

namespace Controller.Cost.SharedDetectorDirectoryAlloc
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width heapSize rootBase count entry : Nat) : List (Instruction width 8) :=
  (SharedDetectorPrepare.code width heapSize count).toList ++
    ((SharedWitnessCopy.code width (entry + 2 * count + 1) (entry + 2 * count + 11) rootBase count).toList ++
      SharedWitnessPark.code width count)

@[simp] theorem code_length : (code width heapSize rootBase count entry).length = 4 * count + 11 := by
  simp [code]; omega

private theorem head_at (program : Program width 8) (entry : Nat) (left right : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (left ++ right)) : SharedRootRead.BlockAt program entry left := by
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left below] at found
  exact found

private theorem tail_at (program : Program width 8) (entry : Nat) (left right : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (left ++ right)) : SharedRootRead.BlockAt program (entry + left.length) right := by
  intro offset below
  have found := present (left.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at found
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using found

private theorem array_at (program : Program width 8) (entry : Nat) (instructions : Program width 8)
    (present : SharedRootRead.BlockAt program entry instructions.toList) : CodeAt program entry instructions := by
  intro phase
  simpa only [Array.getElem?_toList] using present phase.val (by simpa only [Array.length_toList] using phase.isLt)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem execution (program : Program width 8) (state : State width 8)
    (candidates roots references : List (Word width)) (rootBase entry : Nat)
    (sameCount : roots.length = candidates.length)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 4 * candidates.length + 11 < 2 ^ width)
    (heapRoom : state.heap.size + 2 * candidates.length < 2 ^ width)
    (positive : 0 < rootBase) (rootBound : rootBase + roots.length ≤ state.heap.size)
    (rootsStored : SharedDetectorData.Slots state.heap rootBase roots)
    (input : state.stack = candidates ++ references)
    (physical : SharedRootRead.BlockAt program entry (code width state.heap.size rootBase candidates.length entry)) :
    ∃ final peak, Execution program state final (10 * candidates.length + 6) peak ∧
      peak ≤ state.liveWords + candidates.length ∧
      final.heap = (state.heap ++ candidates.toArray) ++ roots.toArray ∧
      final.stack = references ∧ final.output = state.output ∧
      final.pc = word width (entry + 4 * candidates.length + 11) ∧ final.halted = false := by
  unfold code at physical
  have prepareAt := head_at program entry _ _ physical
  have tail := tail_at program entry _ _ physical
  simp only [Array.length_toList, SharedDetectorPrepare.code_size] at tail
  have copyAt := head_at program (entry + (2 * candidates.length + 1)) _ _ tail
  have parkAt := tail_at program (entry + (2 * candidates.length + 1)) _ _ tail
  simp only [Array.length_toList, SharedWitnessCopy.code_size] at parkAt
  obtain ⟨parked, prepareTrace, prepareHeap, prepareStack, prepareOutput, preparePC, prepareRunning, cursor, candidatesStored⟩ :=
    SharedDetectorPrepare.execution program state candidates references entry position running (by omega) (by omega) input
      (array_at _ _ _ prepareAt)
  have parkedLive : parked.liveWords = state.liveWords := by
    simp only [State.liveWords, prepareHeap, prepareStack, prepareOutput, Array.size_append, List.size_toArray,
      input, List.length_append]
    omega
  have copyCells : ∀ index : Nat, ∀ below : index < roots.length,
      parked.heap[rootBase + index]? = some roots[index] := by
    intro index below
    rw [prepareHeap, Array.getElem?_append_left (by omega)]
    exact rootsStored index below
  obtain ⟨copied, copyPeak, copyTrace, copyMemory, copyHeap, copyStack, copyOutput, copyPC, copyRunning, head⟩ :=
    SharedWitnessCopy.execution program parked rootBase roots (entry + 2 * candidates.length + 1)
      (entry + 2 * candidates.length + 11) preparePC prepareRunning (by omega) positive (by omega) copyCells
      (array_at _ _ _ (by simpa only [sameCount, Nat.add_assoc] using copyAt))
  have copiedLive : copied.liveWords = state.liveWords + candidates.length := by
    simp only [State.liveWords, copyHeap, prepareHeap, copyStack, prepareStack, copyOutput, prepareOutput,
      Array.size_append, List.size_toArray, List.length_append, input, sameCount]
    omega
  obtain ⟨final, parkTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, frame⟩ :=
    SharedWitnessPark.execution program copied roots references (entry + 2 * candidates.length + 11) copyPC copyRunning
      (by omega) (by rw [copyHeap, prepareHeap]; simp only [Array.size_append, List.size_toArray]; omega)
      (by simpa only [prepareStack] using copyStack)
      (by simpa only [sameCount, Nat.add_assoc, Nat.reduceAdd] using parkAt)
  have joined := prepareTrace.append (copyTrace.append parkTrace)
  refine ⟨final, max state.liveWords (max copyPeak copied.liveWords), ?_, ?_,
    finalHeap.trans (congrArg (fun heap => heap ++ roots.toArray) (copyHeap.trans prepareHeap)), finalStack,
    finalOutput.trans (copyOutput.trans prepareOutput), ?_, finalRunning⟩
  · convert joined using 1 <;> rw [sameCount] <;> omega
  · rw [parkedLive] at copyMemory
    rw [copiedLive]
    apply max_le
    · omega
    · apply max_le <;> omega
  · rw [sameCount] at finalPC
    convert finalPC using 1 <;> congr 1 <;> omega


theorem allocated_slots (heap : Array (Word width)) (candidates roots : List (Word width)) :
    SharedDetectorData.Slots ((heap ++ candidates.toArray) ++ roots.toArray) heap.size candidates ∧
    SharedDetectorData.Slots ((heap ++ candidates.toArray) ++ roots.toArray) (heap.size + candidates.length) roots ∧
    ForestZeroBackendFrame.PrefixFrame heap.size heap ((heap ++ candidates.toArray) ++ roots.toArray) := by
  refine ⟨?_, ?_, ?_⟩
  · intro index below
    rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega)]
    simp [Array.getElem?_append, below]
  · intro index below
    rw [Array.getElem?_append_right (by simp only [Array.size_append, List.size_toArray]; omega)]
    simp [Array.size_append, below]
  · refine ⟨by omega, by simp only [Array.size_append, List.size_toArray]; omega, ?_⟩
    intro index below
    rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
      Array.getElem?_append_left below]

end Controller.Cost.SharedDetectorDirectoryAlloc
