module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroNativeFramed
public import Controller.Cost.ForestZeroReclaim

@[expose] public section

/-! The native success continuation restores the register/stack frame and then reclaims the solver scratch. -/
namespace Controller.Cost.SharedZeroNativeCleanup
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestZeroCompile Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.SharedZeroNativeComplete

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
    ∀ (keep count : Nat) (rest : List (Word width)) (returnPC : Nat),
    ∀ setupAt : ∀ phase : Fin 3, resident[done + 8 + phase.val]? = (ForestZeroReclaim.setupCode width)[phase.val]?,
    ∀ loopAt : ForestZeroReclaim.At resident (done + 11) returnPC,
    ∀ cleanupRoom : done + 15 < 2 ^ width,
    ∀ countFit : count < 2 ^ width,
    ∀ savedCount : state.stack = word width count :: rest,
    ∀ allocated : state.heap.size = keep + count,
    let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 55 * (selectedSize parameters).total + 4 * count + 25 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total + 8 ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      final.pc = word width returnPC ∧ final.halted = false ∧
      ForestZeroBackendFrame.PrefixFrame keep state.heap final.heap := by
  intro keep count rest returnPC setupAt loopAt cleanupRoom countFit savedCount allocated
  let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
  obtain ⟨native, nativeTicks, nativePeak, nativeTrace, timeBound, spaceBound, heap, stack, output, registers, pc, active⟩ :=
    SharedZeroNativeFramed.execution parameters resident state saveEntry projectionEntry nativeEntry offBase done dictionary layout
      represented within queue fifo countFits position running projectionEq saveAt restoreRoom restoreAt zero remaining tableWord
      one decrement offWord channelsFit heapFits projectionRoom projectionAt nativeRoom nativeHeap nativeAt finishRoom emitAt releaseAt
  obtain ⟨final, cleanupTrace, finalSize, finalStack, finalOutput, finalPC, finalRunning, prefixFrame⟩ :=
    ForestZeroReclaim.stacked_execution resident (done + 8) returnPC keep count native rest setupAt
      (by simpa [Nat.add_assoc] using loopAt) pc active (by omega) countFit (stack.trans savedCount)
      (by simpa only [heap] using allocated)
  have nativeLive : native.liveWords = state.liveWords + (compile parameters).toState.count := by
    simp only [State.liveWords, heap, stack, output, List.length_append, List.length_reverse, NativeRootLoad.words_length]
    omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have joined := nativeTrace.append cleanupTrace
  refine ⟨final, nativeTicks + (4 * count + 4), max nativePeak native.liveWords, joined, ?_, ?_, finalSize, finalStack,
    finalOutput.trans output, finalPC, finalRunning, ?_⟩
  · omega
  · rw [nativeLive]
    omega
  · simpa only [heap] using prefixFrame

end Controller.Cost.SharedZeroNativeCleanup
