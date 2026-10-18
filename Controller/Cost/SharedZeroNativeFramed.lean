module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRegisterStack
public import Controller.Cost.SharedZeroNativeComplete
public import Controller.Cost.NativeRetainedFinish
public import Controller.Cost.ForestZeroChannelPush

@[expose] public section

/-! The terminal FIFO projection, native evaluation, assignment emission and suffix reclamation form one fetched continuation. -/
namespace Controller.Cost.SharedZeroNativeFramed
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestZeroCompile Controller.Native Controller.Native.SourceController Controller.Decoder

open Controller.Cost.SharedZeroNativeComplete

def prepared (state : State width 8) (projectionEntry : Nat) : State width 8 :=
  { state with stack := ((List.finRange 8).map state.reg).reverse ++ state.stack, pc := word width projectionEntry }

private theorem state_ext (left right : State width 8)
    (reg : left.reg = right.reg) (heap : left.heap = right.heap) (stack : left.stack = right.stack)
    (output : left.output = right.output) (pc : left.pc = right.pc) (halted : left.halted = right.halted) : left = right := by
  cases left
  cases right
  simp_all

theorem execution (parameters : Parameters) (resident : Program width 8) (state : State width 8)
    (saveEntry projectionEntry nativeEntry offBase done : Nat) (dictionary : Dictionary ambient)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : ForestZeroDictionary.Represented state.heap layout dictionary)
    (within : parameters.channels ≤ ambient) (queue : List (Fin dictionary.coordinates.size))
    (fifo : Controller.Horn.WorklistMark.Stored queue offBase state.heap)
    (countFits : dictionary.coordinates.size + 1 < 2 ^ width)
    (position : state.pc = word width saveEntry) (running : state.halted = false)
    (projectionEq : projectionEntry = saveEntry + 8)
    (saveAt : SharedRootRead.BlockAt resident saveEntry (SharedRegisterStack.saveCode (width := width) (List.finRange 8)))
    (restoreRoom : done + 8 < 2 ^ width)
    (restoreAt : SharedRootRead.BlockAt resident done (SharedRegisterStack.restoreCode (width := width) (List.finRange 8).reverse))
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
      ticks ≤ 55 * (selectedSize parameters).total + 21 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 8 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      final.reg = state.reg ∧ final.pc = word width (done + 8) ∧ final.halted = false := by
  let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
  obtain ⟨saved, saveTrace, saveHeap, saveOutput, saveReg, saveStack, savePC, saveRunning⟩ :=
    SharedRegisterStack.save_execution resident state saveEntry (List.finRange 8) position running
      (by have bound := projectionRoom; rw [projectionEq] at bound; simp; omega) saveAt
  have savedEq : saved = prepared state projectionEntry := by
    apply state_ext saved (prepared state projectionEntry) saveReg saveHeap saveStack saveOutput
    · simpa only [List.length_finRange, ← projectionEq, prepared] using savePC
    · exact saveRunning.trans running.symm
  rw [savedEq] at saveTrace
  obtain ⟨native, nativeTicks, nativePeak, nativeTrace, nativeTime, nativeSpace, heap, stack, output, pc, active⟩ :=
    SharedZeroNativeComplete.execution parameters resident (prepared state projectionEntry) projectionEntry nativeEntry offBase done
      dictionary layout represented within queue fifo countFits rfl running zero remaining tableWord one decrement offWord
      channelsFit heapFits projectionRoom projectionAt nativeRoom nativeHeap nativeAt finishRoom emitAt releaseAt
  have restoreInput : native.stack = (List.finRange 8).reverse.map state.reg ++ state.stack := by
    simpa only [prepared, List.map_reverse] using stack
  obtain ⟨final, restoreTrace, finalHeap, finalOutput, finalStack, registers, finalPC, finalRunning⟩ :=
    SharedRegisterStack.restore_execution resident native done (List.finRange 8).reverse state.reg state.stack pc active
      (by simpa using restoreRoom) restoreInput restoreAt
  have preparedLive : (prepared state projectionEntry).liveWords = state.liveWords + 8 := by
    simp [prepared, State.liveWords]
    omega
  have nativeLive : native.liveWords = state.liveWords + 8 + (compile parameters).toState.count := by
    simp only [State.liveWords, heap, stack, output, prepared, List.length_append, List.length_reverse,
      List.length_map, List.length_finRange, NativeRootLoad.words_length]
    omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have joined := (saveTrace.append nativeTrace).append restoreTrace
  refine ⟨final, (List.finRange 8).length + nativeTicks + (List.finRange 8).reverse.length,
    max (max (state.liveWords + (List.finRange 8).length) nativePeak) native.liveWords,
    joined, ?_, ?_, finalHeap.trans heap, finalStack, ?_, ?_, ?_, finalRunning⟩
  · simp only [List.length_finRange, List.length_reverse]
    omega
  · rw [nativeLive]
    rw [preparedLive] at nativeSpace
    simp only [List.length_finRange]
    omega
  · simpa only [prepared] using finalOutput.trans output
  · funext register
    simpa using registers register
  · simpa using finalPC

end Controller.Cost.SharedZeroNativeFramed
