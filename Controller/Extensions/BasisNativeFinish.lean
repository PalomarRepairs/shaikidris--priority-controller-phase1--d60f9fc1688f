module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BasisStackSearch
public import Controller.Cost.NativeRetainedEmit
public import Controller.Cost.NativeRealizedChecked

@[expose] public section

/-! The native continuation consumes a detector's stack vector, constructs
the physical bridge, evaluates and emits the selected source assignment,
and halts in the same resident program. -/
namespace Controller.Extensions.BasisNativeFinish
open Controller.Decoder Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.GateProgram

def code (parameters : Parameters) (width base entry : Nat) : List (Instruction width 8) :=
  (NativeRetainedExecution.code parameters width base entry).map RegisterWiden.widenInstruction ++
    ((OutputProgram.emitCode width (NativeRealizedCore.addresses (base + parameters.channels)
      (compile parameters).toState.count)).map RegisterWiden.widenInstruction ++ [.halt])

theorem code_length (parameters : Parameters) (width base entry : Nat) :
    (code parameters width base entry).length =
      (NativeRetainedExecution.code parameters width base entry).length + 3 * (compile parameters).toState.count + 1 := by
  simp [code, OutputProgram.emitCode_length, Nat.add_assoc]

theorem code_bound (parameters : Parameters) (width base entry : Nat) :
    (code parameters width base entry).length ≤ 34 * (selectedSize parameters).total + 1 := by
  have rootCode := NativeRetainedExecution.source_code_bound parameters width base entry
  have circuit := NativeSourceExecution.code_length_le parameters width (base + parameters.channels)
    (NativeRetainedExecution.circuitEntry parameters width base entry)
  change (NativeRetainedExecution.circuitCode parameters width base entry).length ≤ _ at circuit
  have roots := (sourceCircuit parameters).roots_le
  have channels : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]; omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]; omega
  rw [code_length, NativeRetainedExecution.code_length]
  omega

theorem words_eq (K : Finset (Channel n)) :
    LiteralWitnessReturn.words width K = NativeRootLoad.words width (assignmentOfSet K) := by
  simp only [LiteralWitnessReturn.words, NativeRootLoad.words, List.ofFn_eq_map, assignmentOfSet]

set_option maxHeartbeats 1600000 in
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (K : Finset (Channel parameters.channels)) (eligible : Admissible parameters.buses parameters.bridge.target K)
    (drive : parameters.drive = true)
    (differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet K))
    (resident : Program width 8) (state : State width 8) (entry : Nat) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (input : state.stack = LiteralWitnessReturn.words width K ++ suffix)
    (room : entry + (code parameters width state.heap.size entry).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width)
    (tableRoom : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (present : SharedRootRead.BlockAt resident entry (code parameters width state.heap.size entry)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 34 * (selectedSize parameters).total + 1 ∧
      peak ≤ state.liveWords + 2 * (selectedSize parameters).total ∧
      final.stack = suffix ∧ final.halted = true ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true := by
  have firstAt := SharedDetectorAssembly.block_left resident entry _ _ present
  have restAt := SharedDetectorAssembly.block_right resident entry _ _ present
  simp only [List.length_map] at restAt
  have emitAt := SharedDetectorAssembly.block_left resident _ _ _ restAt
  have haltAt := SharedDetectorAssembly.block_right resident _ _ _ restAt
  simp only [List.length_map, OutputProgram.emitCode_length, NativeRealizedCore.addresses_length] at haltAt
  have physical : ForestZeroCallerWiden.WidenedBlockAt resident entry
      (NativeRetainedExecution.code parameters width state.heap.size entry) := by
    intro i bound
    simpa only [List.getElem?_map] using firstAt i (by simpa only [List.length_map] using bound)
  have size := code_length parameters width state.heap.size entry
  obtain ⟨built, bt, buildTrace, buildTime, table, stack, output, pc, active, appended, high⟩ :=
    NativeRetainedCaller.execution parameters K resident state entry suffix position running
      (by simpa only [words_eq] using input) (by omega) boolFits tableRoom physical
  have nativeEmit : ForestZeroCallerWiden.WidenedBlockAt resident
      (entry + (NativeRetainedExecution.code parameters width state.heap.size entry).length)
      (OutputProgram.emitCode width (NativeRealizedCore.addresses (state.heap.size + parameters.channels)
        (compile parameters).toState.count)) := by
    intro i bound
    simpa only [List.getElem?_map] using emitAt i (by simpa only [List.length_map] using bound)
  obtain ⟨emitted, emitTrace, emitHeap, emitStack, emitOutput, emitPC, emitRun, _⟩ :=
    NativeRetainedEmit.execution resident built (state.heap.size + parameters.channels) _ _ table pc active
      (by omega) (by have exactSize := table.1; omega) nativeEmit
  obtain ⟨final, haltTrace, halted, finalHeap, finalStack, finalOutput⟩ :=
    EnumerationSteps.halt_execution resident emitted _ emitPC emitRun (by omega)
      (by simpa only [Nat.add_zero, List.getElem?_cons_zero] using haltAt 0 (by simp))
  have builtLive := buildTrace.final_storage_le
  have emittedLive := emitTrace.final_storage_le
  have roots := (sourceCircuit parameters).roots_le
  have channels : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]; omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]; omega
  have out : final.output = (NativeRootLoad.words width
      (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output := by
    rw [finalOutput, emitOutput, output]
  refine ⟨final, _, _, (buildTrace.append emitTrace).append haltTrace, by omega, ?_,
    finalStack.trans (emitStack.trans stack), halted, out, ?_⟩
  · omega
  · rw [out, NativeRealizedChecked.output_decodes _ _ boolFits]
    exact SourceLift.eligible_checked parameters raw K eligible drive differs

end Controller.Extensions.BasisNativeFinish
