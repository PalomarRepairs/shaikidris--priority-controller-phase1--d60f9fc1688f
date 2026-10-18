module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroNative
public import Controller.Cost.NativeRetainedFinish
public import Controller.Cost.ForestZeroChannelPush

@[expose] public section

/-! The terminal FIFO projection, native evaluation, assignment emission and suffix reclamation form one fetched continuation. -/
namespace Controller.Cost.SharedZeroNativeComplete
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestZeroCompile Controller.Native Controller.Native.SourceController Controller.Decoder

def emitEntry (parameters : Parameters) (width base nativeEntry : Nat) : Nat :=
  nativeEntry + (NativeRetainedExecution.code parameters width base nativeEntry).length

theorem execution (parameters : Parameters) (resident : Program width 8) (state : State width 8)
    (projectionEntry nativeEntry offBase done : Nat) (dictionary : Dictionary ambient)
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
      (NativeRetainedExecution.code parameters width state.heap.size nativeEntry))
    (finishRoom : emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt resident (emitEntry parameters width state.heap.size nativeEntry)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : Controller.Cost.RawTransferLoops.CodeAt resident
      (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width (emitEntry parameters width state.heap.size nativeEntry + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count))) :
    let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 55 * (selectedSize parameters).total + 5 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      final.pc = word width done ∧ final.halted = false := by
  let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
  obtain ⟨native, nativeTicks, nativePeak, nativeTrace, nativeTime, nativeSpace, table, stack, output, pc, active,
    appended, heap⟩ := SharedZeroNative.execution parameters resident state projectionEntry nativeEntry offBase dictionary layout
      represented within queue fifo countFits position running zero remaining tableWord one decrement offWord channelsFit
      heapFits projectionRoom projectionAt nativeRoom nativeHeap nativeAt
  have suffixSize : appended.size = parameters.channels + (compile parameters).toState.count := by
    have endSize := table.1
    have total := congrArg Array.size heap
    simp only [Array.size_append] at total
    omega
  have nativeFits : native.heap.size < 2 ^ width := by have size := table.1; omega
  obtain ⟨final, finishTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    NativeRetainedFinish.execution resident native state.heap appended (state.heap.size + parameters.channels)
      (emitEntry parameters width state.heap.size nativeEntry) done
      (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K)) table heap pc active
      finishRoom nativeFits emitAt (by simpa only [suffixSize] using releaseAt)
  have nativeLive : native.liveWords = state.liveWords + parameters.channels + (compile parameters).toState.count := by
    have size := table.1
    simp only [State.liveWords, stack, output]
    omega
  have roots := (sourceCircuit parameters).roots_le
  have channelBound : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]
    omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have joined := nativeTrace.append finishTrace
  refine ⟨final, nativeTicks + (3 * (compile parameters).toState.count + 4 * appended.size + 4),
    max nativePeak (native.liveWords + (compile parameters).toState.count), joined, ?_, ?_, finalHeap,
    finalStack.trans stack, ?_, finalPC, finalRunning⟩
  · rw [suffixSize]
    omega
  · rw [nativeLive]
    exact max_le (by omega) (by omega)
  · simpa only [output] using finalOutput

end Controller.Cost.SharedZeroNativeComplete
