module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeCircuitRetained
public import Controller.Cost.NativeRealizedCore

@[expose] public section

/-! Membership loading, physical root construction and native evaluation run at caller offsets while retaining its heap. -/
namespace Controller.Cost.NativeRetainedExecution
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution
open Controller.Cost.NativeSourceExecution Controller.Native Controller.Native.SourceController

def rootCode (parameters : Parameters) (width base entry : Nat) : List (Instruction width 4) :=
  NativeRootBuilder.code width base (entry + 2 * parameters.channels) (NativeRootBuilder.sourceGates parameters)

def circuitEntry (parameters : Parameters) (width base entry : Nat) : Nat :=
  entry + 2 * parameters.channels + (rootCode parameters width base entry).length

def circuitCode (parameters : Parameters) (width base entry : Nat) : List (Instruction width 4) :=
  NativeCircuitExecution.code width (base + parameters.channels) (circuitEntry parameters width base entry)
    (sourceCircuit parameters)

@[irreducible] def code (parameters : Parameters) (width base entry : Nat) : List (Instruction width 4) :=
  NativeRootLoad.code width parameters.channels ++
    (rootCode parameters width base entry ++ circuitCode parameters width base entry)

theorem source_code_bound (parameters : Parameters) (width base entry : Nat) :
    (rootCode parameters width base entry).length ≤ 16 * SourceInitialIDs.rootCount parameters := by
  apply (NativeRootBuilder.code_length_le width base (entry + 2 * parameters.channels)
    (NativeRootBuilder.sourceGates parameters) ?_).trans_eq (by rw [NativeRootBuilder.sourceGates_length])
  intro producer member position
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact NativePhysicalRootGate.code_length_le parameters.bridge.target
    ((SourceInitialIDs.rootIndex (n := parameters.channels) (b := parameters.buses)).symm index) width base position

theorem code_length (parameters : Parameters) (width base entry : Nat) :
    (code parameters width base entry).length = 2 * parameters.channels +
      (rootCode parameters width base entry).length + (circuitCode parameters width base entry).length := by
  rw [code]
  simp [Nat.add_assoc]

set_option maxHeartbeats 4000000 in
theorem execution (parameters : Parameters) (K : Finset (Channel parameters.channels))
    (resident : Program width 4) (state : State width 4) (entry : Nat) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (input : state.stack = NativeRootLoad.words width (assignmentOfSet K) ++ suffix)
    (room : entry + (code parameters width state.heap.size entry).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width)
    (tableRoom : state.heap.size + parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (physical : BlockAt resident entry (code parameters width state.heap.size entry)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + (compile parameters).toState.count) ∧
      ticks ≤ 2 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters +
        13 * (selectedSize parameters).total ∧
      TableStored final.heap (state.heap.size + parameters.channels)
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K)) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + (code parameters width state.heap.size entry).length) ∧
      final.halted = false ∧ ∃ appended : Array (Word width), final.heap = state.heap ++ appended := by
  have assembled := physical
  rw [code] at assembled
  have codeRoom := room
  rw [code_length] at codeRoom
  have rootsLe := (sourceCircuit parameters).roots_le
  have counts := (sourceCircuit parameters).variable_count
  have loadBlock := BlockAt.prefix _ _ _ _ assembled
  obtain ⟨loaded, loadTrace, loadedHeap, loadedStack, loadedOutput, loadedPC, loadedRunning⟩ :=
    NativeRootLoad.execution resident state (NativeRootLoad.words width (assignmentOfSet K)) suffix entry
      position running (by simp only [NativeRootLoad.words_length]; omega)
      (by simp only [NativeRootLoad.words_length]; omega) input
      (by simpa only [NativeRootLoad.words_length] using loadBlock)
  have loadedTable : TableStored loaded.heap state.heap.size (assignmentOfSet K) := by
    rw [loadedHeap]
    exact NativeRootBuilder.appended_table state.heap (assignmentOfSet K)
  have loadedSize : loaded.heap.size = state.heap.size + parameters.channels := by
    have := loadedTable.1
    omega
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp only [State.liveWords, loadedHeap, loadedStack, loadedOutput, input, Array.size_append,
      List.size_toArray, NativeRootLoad.words_length, List.length_append]
    omega
  have rootAndRest := BlockAt.suffix _ _ _ _ assembled
  have rootBlock : BlockAt resident (entry + 2 * parameters.channels)
      (rootCode parameters width state.heap.size entry) := by
    simpa only [NativeRootLoad.code_length] using BlockAt.prefix _ _ _ _ rootAndRest
  obtain ⟨produced, rootTicks, rootTrace, rootBound, producedHeap, retained,
    producedStack, producedOutput, producedPC, producedRunning⟩ :=
    NativeRootBuilder.execution resident loaded (assignmentOfSet K) (NativeRootBuilder.sourceGates parameters)
      state.heap.size (entry + 2 * parameters.channels)
      (by simpa only [NativeRootLoad.words_length] using loadedPC) loadedRunning
      (by change entry + 2 * parameters.channels + (rootCode parameters width state.heap.size entry).length < _; omega)
      boolFits (by rw [loadedSize, NativeRootBuilder.sourceGates_length]; omega) loadedTable.2 rootBlock
  let realized := Physical.realizeBridge parameters.bridge parameters.positiveBuses K
  have producedTable : TableStored produced.heap (state.heap.size + parameters.channels)
      (sourcePhysicalRoots parameters realized) := by
    rw [producedHeap, NativeRootBuilder.source_result_words]
    simpa only [loadedSize] using NativeRootBuilder.appended_table loaded.heap (sourcePhysicalRoots parameters realized)
  have producedLive : produced.liveWords = state.liveWords + SourceInitialIDs.rootCount parameters := by
    have := producedTable.1
    simp only [State.liveWords, producedStack, producedOutput]
    have before := loadedLive
    simp only [State.liveWords] at before
    omega
  have circuitBlock : BlockAt resident (circuitEntry parameters width state.heap.size entry)
      (circuitCode parameters width state.heap.size entry) := by
    simpa only [NativeRootLoad.code_length, circuitEntry] using BlockAt.suffix _ _ _ _ rootAndRest
  obtain ⟨final, ticks, trace, bound, table, stack, output, pc, finalRunning, appended, finalHeap⟩ :=
    NativeCircuitRetained.execution resident produced (sourceCircuit parameters) (sourcePhysicalRoots parameters realized)
      (state.heap.size + parameters.channels) (circuitEntry parameters width state.heap.size entry)
      (by simpa only [rootCode, circuitEntry] using producedPC) producedRunning
      (by change circuitEntry parameters width state.heap.size entry + (circuitCode parameters width state.heap.size entry).length < _;
          dsimp only [circuitEntry]; omega) boolFits tableRoom producedTable circuitBlock
  refine ⟨final, 2 * parameters.channels + rootTicks + ticks, ?_, ?_, table,
    stack.trans (producedStack.trans loadedStack), output.trans (producedOutput.trans loadedOutput), ?_, finalRunning,
    ⟨(NativeRootLoad.words width (assignmentOfSet K)).toArray ++
      (NativeRootBuilder.resultWords width (assignmentOfSet K) (NativeRootBuilder.sourceGates parameters)).toArray ++ appended, ?_⟩⟩
  · have joined := (loadTrace.append rootTrace).append trace
    rw [loadedLive, producedLive] at joined
    convert joined using 1 <;> simp only [NativeRootLoad.words_length, NativeRootBuilder.sourceGates_length] <;> omega
  · have rootLimit := source_code_bound parameters width state.heap.size entry
    have circuitLimit := NativeSourceExecution.code_length_le parameters width (state.heap.size + parameters.channels)
      (circuitEntry parameters width state.heap.size entry)
    change rootTicks ≤ (rootCode parameters width state.heap.size entry).length at rootBound
    omega
  · simpa only [code_length, circuitCode, circuitEntry, Nat.add_assoc] using pc
  · rw [finalHeap, producedHeap, loadedHeap]
    simp only [Array.append_assoc]

end Controller.Cost.NativeRetainedExecution
