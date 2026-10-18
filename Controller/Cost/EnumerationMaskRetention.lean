module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationOracle
public import Controller.Cost.EnumerationSteps

@[expose] public section

/-! Retain prefix masks in heap cells while preserving the oracle's stack input.
Healthy reference tags are regenerated from the fixed healthy observation list. -/
namespace Controller.Cost.EnumerationMaskRetention
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def discardCode (width count : Nat) : List (Instruction width 8) := List.replicate count (.pop 0)

@[simp] theorem discard_length : (discardCode width count).length = count := by simp [discardCode]

theorem discard_execution (program : Program width 8) (state : State width 8)
    (values rest : List (Word width)) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (input : state.stack = values ++ rest) (room : entry + values.length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (discardCode width values.length)) :
    ∃ final, Execution program state final values.length state.liveWords ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (entry + values.length) ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  induction values generalizing state entry with
  | nil =>
    refine ⟨state, ?_, rfl, ?_, rfl, ?_, running, rfl⟩
    · simpa using Execution.refl (p := program) state
    · simpa using input
    · simpa using position
  | cons value tail ih =>
    obtain ⟨middle, first, middlePC, middleReg, middleHeap, middleStack, middleOutput, middleRunning, frame⟩ :=
      EnumerationSteps.pop_execution (program := program) state entry 0 value (tail ++ rest) position running
        (by simp only [List.length_cons] at room; omega) (by simpa using input)
        (by simpa [discardCode] using present 0 (by simp))
    have tailAt : SharedRootRead.BlockAt program (entry + 1) (discardCode width tail.length) := by
      intro offset below
      have found := present (1 + offset) (by simp at below ⊢; omega)
      rw [Nat.add_comm 1 offset] at found
      simpa [discardCode, List.replicate_succ, Nat.add_assoc, Nat.add_comm 1] using found
    obtain ⟨final, suffix, heap, stack, output, pc, active, head⟩ :=
      ih middle (entry + 1) middlePC middleRunning middleStack
        (by simp only [List.length_cons] at room; omega) tailAt
    have smaller : middle.liveWords ≤ state.liveWords := first.final_storage_le
    refine ⟨final, ?_, heap.trans middleHeap, stack, output.trans middleOutput, ?_, active,
      head.trans (frame 4 (by decide))⟩
    · simpa only [List.length_cons, Nat.add_comm 1, Nat.max_eq_left smaller] using first.append suffix
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using pc

private theorem left_at (program : Program width 8) (entry : Nat) (first rest : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (first ++ rest)) : SharedRootRead.BlockAt program entry first := by
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rwa [List.getElem?_append_left below] at found

private theorem right_at (program : Program width 8) (entry : Nat) (first rest : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program (entry + first.length) rest := by
  intro offset below
  have found := present (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at found
  simpa only [Nat.add_assoc] using found

def code (width entry maskBase count : Nat) (healthy : List (Word width)) : List (Instruction width 8) :=
  discardCode width healthy.length ++
    (SharedWitnessPark.code width count ++
    ((SharedWitnessCopy.code width (entry + healthy.length + 2 * count)
      (entry + healthy.length + 2 * count + 10) maskBase count).toList ++
      EnumerationOracle.pushCode width healthy))

@[simp] theorem code_length : (code width entry maskBase count healthy).length =
    3 * healthy.length + 2 * count + 10 := by
  simp [code]
  omega

theorem execution (program : Program width 8) (state : State width 8)
    (healthy masks rest : List (Word width)) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (input : state.stack = healthy ++ masks ++ rest)
    (positive : 0 < state.heap.size) (capacity : state.heap.size + masks.length < 2 ^ width)
    (room : entry + (code width entry state.heap.size masks.length healthy).length < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width entry state.heap.size masks.length healthy)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks = 3 * healthy.length + 8 * masks.length + 5 ∧ peak ≤ state.liveWords + masks.length ∧
      final.heap = state.heap ++ masks.toArray ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (code width entry state.heap.size masks.length healthy).length) ∧
      final.halted = false ∧ final.reg 4 = state.reg 4 := by
  have codeRoom := room
  rw [code_length] at codeRoom
  unfold code at present
  have discardAt := left_at program entry _ _ present
  have rest1 := right_at program entry _ _ present
  simp only [discard_length] at rest1
  have parkAt := left_at program _ _ _ rest1
  have rest2 := right_at program _ _ _ rest1
  simp only [SharedWitnessPark.code_length] at rest2
  have copyAt := left_at program _ _ _ rest2
  have pushAt := right_at program _ _ _ rest2
  simp only [Array.length_toList, SharedWitnessCopy.code_size, Nat.add_assoc] at pushAt
  obtain ⟨discarded, discardTrace, discardHeap, discardStack, discardOutput, discardPC, discardRunning, discardHead⟩ :=
    discard_execution program state healthy (masks ++ rest) entry position running (by simpa [List.append_assoc] using input)
      (by omega) discardAt
  obtain ⟨parked, parkTrace, parkHeap, parkStack, parkOutput, parkPC, parkRunning, parkFrame⟩ :=
    SharedWitnessPark.execution program discarded masks rest (entry + healthy.length) discardPC discardRunning
      (by omega) (by rw [discardHeap]; exact capacity) discardStack parkAt
  have maskCells : ∀ index : Nat, ∀ below : index < masks.length,
      parked.heap[state.heap.size + index]? = some masks[index] := by
    intro index below
    rw [parkHeap, discardHeap]
    simp [below]
  obtain ⟨copied, copyPeak, copyTrace, copySpace, copyHeap, copyStack, copyOutput, copyPC, copyRunning, copyHead⟩ :=
    SharedWitnessCopy.execution program parked state.heap.size masks (entry + healthy.length + 2 * masks.length)
      (entry + healthy.length + 2 * masks.length + 10) parkPC parkRunning (by omega) positive capacity maskCells
      (by intro phase; simpa only [Array.getElem?_toList] using copyAt phase.val (by simpa using phase.isLt))
  obtain ⟨final, pushTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    EnumerationOracle.push_execution program healthy copied (entry + healthy.length + 2 * masks.length + 10)
      copyPC copyRunning (by omega) (by simpa only [Nat.add_assoc] using pushAt)
  have discardedLive : discarded.liveWords + healthy.length = state.liveWords := by
    simp only [State.liveWords, discardHeap, discardStack, discardOutput, input, List.length_append]
    omega
  have parkedLive : parked.liveWords = discarded.liveWords := by
    simp only [State.liveWords, parkHeap, parkStack, parkOutput, discardStack,
      Array.size_append, List.size_toArray, List.length_append]
    omega
  have copiedLive : copied.liveWords = parked.liveWords + masks.length := by
    simp only [State.liveWords, copyHeap, copyStack, copyOutput, List.length_append]
    omega
  have joined := discardTrace.append (parkTrace.append (copyTrace.append pushTrace))
  refine ⟨final, healthy.length + (2 * masks.length + ((6 * masks.length + 5) + 2 * healthy.length)),
    max state.liveWords (max discarded.liveWords (max copyPeak (copied.liveWords + healthy.length))),
    joined, by omega, ?_, ?_, ?_, ?_, ?_, finalRunning, ?_⟩
  · rw [parkedLive] at copySpace
    omega
  · rw [finalHeap, copyHeap, parkHeap, discardHeap]
  · rw [finalStack, copyStack, parkStack]
    simpa only [List.append_assoc] using input.symm
  · exact finalOutput.trans (copyOutput.trans (parkOutput.trans discardOutput))
  · rw [code_length]
    convert finalPC using 1
    congr 1
    omega
  · exact (finalFrame 4 (by decide)).trans (copyHead.trans ((parkFrame 4 (by decide)).trans discardHead))

end Controller.Cost.EnumerationMaskRetention
