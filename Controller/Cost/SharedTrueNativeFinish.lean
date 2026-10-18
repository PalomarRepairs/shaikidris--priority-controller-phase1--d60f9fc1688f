module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedTrueNative
public import Controller.Cost.NativeRetainedFinish
public import Controller.Cost.NativeRealizedChecked

@[expose] public section

namespace Controller.Cost.SharedTrueNativeFinish
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.NativeCircuitExecution

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem execution (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (T : Finset (Fin parameters.channels)) (tag : Word width) (base entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (SharedTrueNative.code parameters width state.heap.size base entry).length < 2 ^ width)
    (finishRoom : entry + (SharedTrueNative.code parameters width state.heap.size base entry).length +
      3 * (compile parameters).toState.count + 7 < 2 ^ width)
    (boolFits : 1 < 2 ^ width) (addressRoom : base + parameters.channels < 2 ^ width)
    (tableBound : base + parameters.channels ≤ state.heap.size)
    (nativeRoom : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (held : state.reg 4 = tag)
    (stored : ∀ channel : Fin parameters.channels, state.heap[base + channel.val]? =
      some (word width (if assignmentOfSet T channel then 1 else 0)))
    (physical : SharedRootRead.BlockAt program entry (SharedTrueNative.code parameters width state.heap.size base entry))
    (emitAt : ForestZeroCallerWiden.WidenedBlockAt program
      (entry + (SharedTrueNative.code parameters width state.heap.size base entry).length)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels) (compile parameters).toState.count)))
    (releaseAt : CodeAt program
      (entry + (SharedTrueNative.code parameters width state.heap.size base entry).length + 3 * (compile parameters).toState.count)
      (SharedEvaluationReclaim.code width
        (entry + (SharedTrueNative.code parameters width state.heap.size base entry).length + 3 * (compile parameters).toState.count)
        done (parameters.channels + (compile parameters).toState.count))) :
    ∃ final ticks, Execution program state final ticks
      (state.liveWords + parameters.channels + 2 * (compile parameters).toState.count) ∧
      ticks ≤ 14 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters + 13 * (selectedSize parameters).total +
        7 * (compile parameters).toState.count + 4 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses
          (SharedWitnessDecode.decode T tag)))).reverse ++ state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      (parameters.layout = .raw → parameters.drive = true →
        Admissible parameters.buses parameters.bridge.target (SharedWitnessDecode.decode T tag) →
        (∃ observation, parameters.observations observation (assignmentOfSet {parameters.bridge.target}) ≠
          parameters.observations observation (assignmentOfSet (SharedWitnessDecode.decode T tag))) →
        Certificate.ModelCheck.check (formula parameters)
          (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  obtain ⟨evaluated, nativeTicks, nativeTrace, nativeTime, table, stack, output, candidate, pc, active, appended⟩ :=
    SharedTrueNative.execution parameters program state T tag base entry position running room boolFits addressRoom
      tableBound nativeRoom held stored physical
  obtain ⟨suffix, heap⟩ := appended
  have suffixSize : suffix.size = parameters.channels + (compile parameters).toState.count := by
    have size := congrArg Array.size heap
    simp only [Array.size_append] at size
    have tableSize := table.1
    omega
  obtain ⟨final, finishTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    NativeRetainedFinish.execution program evaluated state.heap suffix (state.heap.size + parameters.channels)
      (entry + (SharedTrueNative.code parameters width state.heap.size base entry).length) done _ table heap pc active
      finishRoom (by have := table.1; omega) emitAt (by simpa only [suffixSize] using releaseAt)
  have evaluatedLive : evaluated.liveWords = state.liveWords + parameters.channels + (compile parameters).toState.count := by
    have tableSize := table.1
    simp only [State.liveWords, stack, output]
    omega
  refine ⟨final, nativeTicks + (3 * (compile parameters).toState.count + 4 * suffix.size + 4), ?_, ?_,
    finalHeap, finalStack.trans stack, ?_, finalPC, finalRunning, ?_⟩
  · have joined := nativeTrace.append finishTrace
    rw [evaluatedLive] at joined
    convert joined using 1 <;> omega
  · rw [suffixSize]
    omega
  · simpa only [output] using finalOutput
  · intro raw drive eligible differs
    rw [finalOutput, output, NativeRealizedChecked.output_decodes _ _ boolFits]
    exact SourceLift.eligible_checked parameters raw (SharedWitnessDecode.decode T tag) eligible drive differs

end Controller.Cost.SharedTrueNativeFinish
