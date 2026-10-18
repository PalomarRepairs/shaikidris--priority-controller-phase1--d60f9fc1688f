module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedTrueInput
public import Controller.Cost.NativeRetainedCaller

@[expose] public section

namespace Controller.Cost.SharedTrueNative
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.NativeCircuitExecution

def nativeEntry (parameters : Parameters) (entry : Nat) : Nat := entry + 9 * parameters.channels

@[irreducible] def code (parameters : Parameters) (width heapSize base entry : Nat) : List (Instruction width 8) :=
  SharedTrueInput.code width base entry (List.finRange parameters.channels).reverse ++
    (NativeRetainedExecution.code parameters width heapSize (nativeEntry parameters entry)).map RegisterWiden.widenInstruction

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem execution (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (T : Finset (Fin parameters.channels)) (tag : Word width) (base entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (code parameters width state.heap.size base entry).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width) (addressRoom : base + parameters.channels < 2 ^ width)
    (tableBound : base + parameters.channels ≤ state.heap.size)
    (nativeRoom : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (held : state.reg 4 = tag)
    (stored : ∀ channel : Fin parameters.channels, state.heap[base + channel.val]? =
      some (word width (if assignmentOfSet T channel then 1 else 0)))
    (physical : SharedRootRead.BlockAt program entry (code parameters width state.heap.size base entry)) :
    ∃ final ticks, Execution program state final ticks
      (state.liveWords + parameters.channels + (compile parameters).toState.count) ∧
      ticks ≤ 10 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters + 13 * (selectedSize parameters).total ∧
      TableStored final.heap (state.heap.size + parameters.channels)
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (SharedWitnessDecode.decode T tag))) ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.reg 4 = tag ∧
      final.pc = word width (entry + (code parameters width state.heap.size base entry).length) ∧
      final.halted = false ∧ (∃ appended : Array (Word width), final.heap = state.heap ++ appended) := by
  have layoutBound := room
  unfold code at physical layoutBound
  simp only [List.length_append, List.length_map, SharedTrueInput.code_length, List.length_reverse,
    List.length_finRange] at layoutBound
  have inputAt : SharedRootRead.BlockAt program entry
      (SharedTrueInput.code width base entry (List.finRange parameters.channels).reverse) := by
    intro offset below
    have found := physical offset (by simp only [List.length_append]; omega)
    rw [List.getElem?_append_left below] at found
    exact found
  have nativeAt : ForestZeroCallerWiden.WidenedBlockAt program (nativeEntry parameters entry)
      (NativeRetainedExecution.code parameters width state.heap.size (nativeEntry parameters entry)) := by
    intro offset below
    have found := physical (9 * parameters.channels + offset) (by
      simp only [List.length_append, List.length_map, SharedTrueInput.code_length, List.length_reverse,
        List.length_finRange]
      omega)
    rw [List.getElem?_append_right (by
      simp only [SharedTrueInput.code_length, List.length_reverse, List.length_finRange]; omega)] at found
    simpa only [SharedTrueInput.code_length, List.length_reverse, List.length_finRange,
      Nat.add_sub_cancel_left, List.getElem?_map, nativeEntry, Nat.add_assoc] using found
  obtain ⟨prepared, inputTicks, inputTrace, inputTime, heap, output, stack, preparedTag, pc, active⟩ :=
    SharedTrueInput.all_channels program state T tag base entry position running (by omega) addressRoom tableBound held stored inputAt
  obtain ⟨final, nativeTicks, nativeTrace, nativeTime, table, finalStack, finalOutput, finalPC, finalRunning, appended, frame⟩ :=
    NativeRetainedCaller.execution parameters (SharedWitnessDecode.decode T tag) program prepared (nativeEntry parameters entry)
      state.stack pc active stack (by rw [heap]; dsimp only [nativeEntry] at layoutBound ⊢; omega) boolFits
      (by rw [heap]; exact nativeRoom) (by rw [heap]; exact nativeAt)
  have preparedLive : prepared.liveWords = state.liveWords + parameters.channels := by
    simp only [State.liveWords, heap, output, stack, List.length_append, NativeRootLoad.words_length]
    omega
  refine ⟨final, inputTicks + nativeTicks, ?_, by omega, ?_, finalStack, finalOutput.trans output,
    (frame 4 (by decide)).trans preparedTag, ?_, finalRunning, ?_⟩
  · have joined := inputTrace.append nativeTrace
    rw [preparedLive] at joined
    simpa only [Nat.max_eq_right (by omega : state.liveWords + parameters.channels ≤
      state.liveWords + parameters.channels + (compile parameters).toState.count)] using joined
  · simpa only [heap] using table
  · rw [heap] at finalPC
    simpa only [code, List.length_append, List.length_map, SharedTrueInput.code_length,
      List.length_reverse, List.length_finRange, nativeEntry, Nat.add_assoc] using finalPC
  · simpa only [heap] using appended

end Controller.Cost.SharedTrueNative
