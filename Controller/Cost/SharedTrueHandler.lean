module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedTrueAccept

@[expose] public section

namespace Controller.Cost.SharedTrueHandler
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution

def emitEntry (parameters : Parameters) (width heapSize base entry : Nat) : Nat :=
  entry + (SharedTrueNative.code parameters width heapSize base entry).length

def releaseEntry (parameters : Parameters) (width heapSize base entry : Nat) : Nat :=
  emitEntry parameters width heapSize base entry + 3 * (compile parameters).toState.count

def acceptEntry (parameters : Parameters) (width heapSize base entry : Nat) : Nat :=
  releaseEntry parameters width heapSize base entry + 7

@[irreducible] def code (parameters : Parameters) (width heapSize base entry : Nat) : List (Instruction width 8) :=
  SharedTrueNative.code parameters width heapSize base entry ++
    ((OutputProgram.emitCode width (NativeRealizedCore.addresses (heapSize + parameters.channels)
      (compile parameters).toState.count)).map RegisterWiden.widenInstruction ++
    ((SharedEvaluationReclaim.code width (releaseEntry parameters width heapSize base entry)
      (acceptEntry parameters width heapSize base entry) (parameters.channels + (compile parameters).toState.count)).toList ++
    (SharedTrueAccept.code width).toList))

theorem code_length (parameters : Parameters) (width heapSize base entry : Nat) :
    (code parameters width heapSize base entry).length =
      (SharedTrueNative.code parameters width heapSize base entry).length + 3 * (compile parameters).toState.count + 9 := by
  unfold code
  simp only [List.length_append, List.length_map, OutputProgram.emitCode_length, NativeRealizedCore.addresses_length,
    Array.length_toList, SharedEvaluationReclaim.code_size, SharedTrueAccept.code_size]
  omega

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
      (state.liveWords + parameters.channels + 2 * (compile parameters).toState.count) ∧
      ticks ≤ 14 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters + 13 * (selectedSize parameters).total +
        7 * (compile parameters).toState.count + 6 ∧
      final.halted = true ∧ final.reg 4 = word width 1 ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (SharedWitnessDecode.decode T tag)))).reverse ++ state.output ∧
      (parameters.layout = .raw → parameters.drive = true →
        Admissible parameters.buses parameters.bridge.target (SharedWitnessDecode.decode T tag) →
        (∃ observation, parameters.observations observation (assignmentOfSet {parameters.bridge.target}) ≠
          parameters.observations observation (assignmentOfSet (SharedWitnessDecode.decode T tag))) →
        Certificate.ModelCheck.check (formula parameters)
          (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  have totalRoom := room
  rw [code_length] at totalRoom
  unfold code at physical
  have nativeAt := head_at program entry _ _ physical
  have first := tail_at program entry _ _ physical
  change SharedRootRead.BlockAt program (emitEntry parameters width state.heap.size base entry) _ at first
  have emitBlock := head_at program (emitEntry parameters width state.heap.size base entry) _ _ first
  have second := tail_at program (emitEntry parameters width state.heap.size base entry) _ _ first
  simp only [List.length_map, OutputProgram.emitCode_length, NativeRealizedCore.addresses_length] at second
  change SharedRootRead.BlockAt program (releaseEntry parameters width state.heap.size base entry) _ at second
  have reclaimAt := head_at program (releaseEntry parameters width state.heap.size base entry) _ _ second
  have last := tail_at program (releaseEntry parameters width state.heap.size base entry) _ _ second
  simp only [Array.length_toList, SharedEvaluationReclaim.code_size] at last
  change SharedRootRead.BlockAt program (acceptEntry parameters width state.heap.size base entry) _ at last
  have emitAt : ForestZeroCallerWiden.WidenedBlockAt program (emitEntry parameters width state.heap.size base entry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)) := by
    intro offset below
    simpa only [List.getElem?_map] using emitBlock offset (by simpa only [List.length_map] using below)
  obtain ⟨finished, ticks, trace, time, heap, stack, output, pc, active, checked⟩ :=
    SharedTrueNativeFinish.execution parameters program state T tag base entry (acceptEntry parameters width state.heap.size base entry)
      position running (by omega) (by omega) boolFits addressRoom tableBound nativeRoom held stored nativeAt emitAt
      (array_at _ _ _ reclaimAt)
  obtain ⟨final, haltTrace, halted, decision, finalHeap, finalStack, finalOutput⟩ :=
    SharedTrueAccept.execution program finished (acceptEntry parameters width state.heap.size base entry) pc active
      (by dsimp only [acceptEntry, releaseEntry, emitEntry]; omega) (array_at _ _ _ last)
  have live : finished.liveWords = state.liveWords + (compile parameters).toState.count := by
    simp only [State.liveWords, heap, stack, output, List.length_append, List.length_reverse, NativeRootLoad.words_length]
    omega
  refine ⟨final, ticks + 2, ?_, by omega, halted, decision, finalHeap.trans heap, finalStack.trans stack,
    finalOutput.trans output, ?_⟩
  · have joined := trace.append haltTrace
    rw [live] at joined
    simpa only [Nat.max_eq_left (by omega : state.liveWords + (compile parameters).toState.count ≤
      state.liveWords + parameters.channels + 2 * (compile parameters).toState.count)] using joined
  · simpa only [finalOutput] using checked

end Controller.Cost.SharedTrueHandler
