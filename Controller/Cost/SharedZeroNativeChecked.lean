module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroNativeComplete
public import Controller.Cost.NativeRealizedChecked
public import Controller.Cost.NativeRetainedFinish
public import Controller.Cost.ForestZeroChannelPush

@[expose] public section

/-! The terminal FIFO projection, native evaluation, assignment emission and suffix reclamation form one fetched continuation. -/
namespace Controller.Cost.SharedZeroNativeChecked
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestZeroCompile Controller.Native Controller.Native.SourceController Controller.Decoder

open Controller.Cost.SharedZeroNativeComplete

theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true) (resident : Program width 8) (state : State width 8)
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
    ∀ eligible : Admissible parameters.buses parameters.bridge.target
      (setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)),
    ∀ differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet (setOfAssignment (SharedZeroNative.channels parameters dictionary queue within))),
    let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 55 * (selectedSize parameters).total + 5 ∧
      peak ≤ state.liveWords + 3 * (selectedSize parameters).total ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true ∧
      final.pc = word width done ∧ final.halted = false := by
  intro eligible differs
  let K := setOfAssignment (SharedZeroNative.channels parameters dictionary queue within)
  obtain ⟨final, ticks, peak, trace, timeBound, spaceBound, heap, stack, output, pc, active⟩ :=
    SharedZeroNativeComplete.execution parameters resident state projectionEntry nativeEntry offBase done dictionary layout
      represented within queue fifo countFits position running zero remaining tableWord one decrement offWord channelsFit
      heapFits projectionRoom projectionAt nativeRoom nativeHeap nativeAt finishRoom emitAt releaseAt
  refine ⟨final, ticks, peak, trace, timeBound, spaceBound, heap, stack, output, ?_, pc, active⟩
  rw [output, NativeRealizedChecked.output_decodes _ _ (by omega)]
  exact SourceLift.eligible_checked parameters raw K eligible drive differs

end Controller.Cost.SharedZeroNativeChecked
