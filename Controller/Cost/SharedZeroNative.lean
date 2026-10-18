module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeRetainedCaller
public import Controller.Cost.ForestZeroChannelPush

@[expose] public section

/-! One fetched execution projects the terminal FIFO's channels onto the stack and consumes them in the native evaluator. -/
namespace Controller.Cost.SharedZeroNative
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestZeroCompile Controller.Native Controller.Native.SourceController Controller.Decoder

def channels (parameters : Parameters) (dictionary : Dictionary ambient)
    (queue : List (Fin dictionary.coordinates.size)) (within : parameters.channels ≤ ambient) :
    Fin parameters.channels → Bool := fun channel =>
  ForestZeroModelLift.lift dictionary true (ForestZeroChannelPush.localValues queue)
    ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩

theorem execution (parameters : Parameters) (resident : Program width 8) (state : State width 8)
    (projectionEntry nativeEntry offBase : Nat) (dictionary : Dictionary ambient)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : ForestZeroDictionary.Represented state.heap layout dictionary)
    (within : parameters.channels ≤ ambient) (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue offBase state.heap)
    (countFits : dictionary.coordinates.size + 1 < 2 ^ width)
    (position : state.pc = word width projectionEntry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (remaining : state.reg 3 = word width parameters.channels)
    (tableWord : state.reg 4 = word width layout.tableBase) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (offWord : state.reg 7 = word width (offBase + 1))
    (channelsFit : parameters.channels + 1 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (projectionRoom : projectionEntry + 14 < 2 ^ width)
    (projectionAt : ForestZeroChannelPush.CodeAt resident projectionEntry nativeEntry)
    (nativeRoom : nativeEntry + (NativeRetainedExecution.code parameters width state.heap.size nativeEntry).length < 2 ^ width)
    (nativeHeap : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (nativeAt : ForestZeroCallerWiden.WidenedBlockAt resident nativeEntry
      (NativeRetainedExecution.code parameters width state.heap.size nativeEntry)) :
    let K := setOfAssignment (channels parameters dictionary queue within)
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 44 * (selectedSize parameters).total + 1 ∧
      peak ≤ state.liveWords + 2 * (selectedSize parameters).total ∧
      TableStored final.heap (state.heap.size + parameters.channels)
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (nativeEntry + (NativeRetainedExecution.code parameters width state.heap.size nativeEntry).length) ∧
      final.halted = false ∧ ∃ appended : Array (Word width), final.heap = state.heap ++ appended := by
  let K := setOfAssignment (channels parameters dictionary queue within)
  obtain ⟨projected, projectionTicks, projectionPeak, projectionTrace, projectionTime, projectionSpace,
    projectedHeap, projectedOutput, projectedStack, registers, exhausted, projectedPC, projectedRunning⟩ :=
    ForestZeroChannelPush.dictionary_execution resident state projectionEntry nativeEntry offBase dictionary layout represented
      within queue fifo countFits position running zero remaining tableWord one decrement offWord
      channelsFit heapFits projectionRoom projectionAt
  have input : projected.stack = NativeRootLoad.words width (assignmentOfSet K) ++ state.stack := by
    rw [projectedStack, ForestZeroChannelPush.native_words]
    simp only [K, assignmentOfSet_setOfAssignment]
    rfl
  have projectedLive : projected.liveWords = state.liveWords + parameters.channels := by
    simp only [State.liveWords, projectedHeap, projectedOutput, projectedStack, List.length_append,
      List.length_map, List.length_finRange]
    omega
  obtain ⟨final, nativeTicks, nativeTrace, nativeTime, table, stack, output, pc, finalRunning, ⟨appended, finalHeap⟩, high⟩ :=
    NativeRetainedCaller.execution parameters K resident projected nativeEntry state.stack projectedPC projectedRunning input
      (by simpa only [projectedHeap] using nativeRoom) (by omega)
      (by simpa only [projectedHeap] using nativeHeap) (by simpa only [projectedHeap] using nativeAt)
  have roots := (sourceCircuit parameters).roots_le
  have channelBound : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]
    omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have joined := projectionTrace.append nativeTrace
  refine ⟨final, projectionTicks + nativeTicks,
    max projectionPeak (projected.liveWords + (compile parameters).toState.count), joined, ?_, ?_, ?_, stack,
    output.trans projectedOutput, ?_, finalRunning, ⟨appended, ?_⟩⟩
  · omega
  · rw [projectedLive]
    exact max_le (by omega) (by omega)
  · simpa only [projectedHeap] using table
  · simpa only [projectedHeap] using pc
  · simpa only [projectedHeap] using finalHeap

end Controller.Cost.SharedZeroNative
