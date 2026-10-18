module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeRootBuilder

@[expose] public section

/-! A single fetched run consumes membership words, constructs the physical
bridge inputs, evaluates the native source circuit, emits its assignment and
halts. The root construction and evaluator share the same heap and state. -/
namespace Controller.Cost.NativeRealizedCore
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution
open Controller.Cost.NativeSourceExecution Controller.Native Controller.Native.SourceController

def rootCode (parameters : Parameters) (width : Nat) : List (Instruction width 4) :=
  NativeRootBuilder.code width 0 (2 * parameters.channels) (NativeRootBuilder.sourceGates parameters)

def circuitEntry (parameters : Parameters) (width : Nat) : Nat :=
  2 * parameters.channels + (rootCode parameters width).length

def circuitCode (parameters : Parameters) (width : Nat) : List (Instruction width 4) :=
  NativeCircuitExecution.code width parameters.channels (circuitEntry parameters width) (sourceCircuit parameters)

def emitEntry (parameters : Parameters) (width : Nat) : Nat :=
  circuitEntry parameters width + (circuitCode parameters width).length

def addresses (base count : Nat) : List Nat := (List.finRange count).map (fun index => base + index.val)

@[simp] theorem addresses_length (base count : Nat) : (addresses base count).length = count := by simp [addresses]

@[irreducible] def code (parameters : Parameters) (width : Nat) : List (Instruction width 4) :=
  NativeRootLoad.code width parameters.channels ++
    (rootCode parameters width ++ (circuitCode parameters width ++
      (OutputProgram.emitCode width (addresses parameters.channels (compile parameters).toState.count) ++ [.halt])))

theorem code_length (parameters : Parameters) (width : Nat) :
    (code parameters width).length = 2 * parameters.channels + (rootCode parameters width).length +
      (circuitCode parameters width).length + 3 * (compile parameters).toState.count + 1 := by
  rw [code]
  simp only [List.length_append, NativeRootLoad.code_length, OutputProgram.emitCode_length,
    addresses_length, List.length_cons, List.length_nil]
  omega

theorem emitted_words (heap : Array (Word width)) (base : Nat) (values : Fin count → Bool)
    (stored : TableStored heap base values) :
    (addresses base count).map (OutputProgram.heapValue heap) = NativeRootLoad.words width values := by
  simp only [addresses, NativeRootLoad.words, List.ofFn_eq_map, List.map_map]
  apply List.map_congr_left
  intro index _
  obtain ⟨valid, cell⟩ := stored.2 index
  simpa only [Function.comp_apply, OutputProgram.heapValue_eq heap (base + index.val) valid] using cell

set_option maxHeartbeats 4000000 in
theorem execution (parameters : Parameters) (K : Finset (Channel parameters.channels))
    (resident : Program width 4) (state : State width 4) (suffix : List (Word width))
    (position : state.pc = word width 0) (running : state.halted = false)
    (empty : state.heap = #[])
    (input : state.stack = NativeRootLoad.words width (assignmentOfSet K) ++ suffix)
    (room : (code parameters width).length < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (tableRoom : parameters.channels + (compile parameters).toState.count < 2 ^ width)
    (physical : BlockAt resident 0 (code parameters width)) :
    ∃ final ticks, Execution resident state final ticks
        (state.liveWords + 2 * (compile parameters).toState.count) ∧
      ticks ≤ 2 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters +
        (circuitCode parameters width).length + 3 * (compile parameters).toState.count + 1 ∧
      TableStored final.heap parameters.channels
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K)) ∧
      final.stack = suffix ∧
      final.output = (NativeRootLoad.words width
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      final.halted = true := by
  have assembled := physical
  rw [code] at assembled
  have codeRoom := room
  rw [code_length] at codeRoom
  have rootsLe := (sourceCircuit parameters).roots_le
  have counts := (sourceCircuit parameters).variable_count
  have loadBlock : BlockAt resident 0 (NativeRootLoad.code width parameters.channels) :=
    BlockAt.prefix _ _ _ _ assembled
  obtain ⟨loaded, loadTrace, loadedHeap, loadedStack, loadedOutput, loadedPC, loadedRunning⟩ :=
    NativeRootLoad.execution resident state (NativeRootLoad.words width (assignmentOfSet K)) suffix 0
      position running (by simp only [NativeRootLoad.words_length]; omega)
      (by simp only [empty, Array.size_empty, Nat.zero_add, NativeRootLoad.words_length]; omega)
      input (by simpa only [NativeRootLoad.words_length] using loadBlock)
  have loadedTable : TableStored loaded.heap 0 (assignmentOfSet K) := by
    rw [loadedHeap, empty, Array.empty_append]
    exact NativeRootLoad.table width (assignmentOfSet K)
  have loadedSize : loaded.heap.size = parameters.channels := by
    have size := loadedTable.1
    omega
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp only [State.liveWords, loadedHeap, loadedStack, loadedOutput, empty, input,
      Array.empty_append, List.size_toArray, NativeRootLoad.words_length, List.length_append,
      Array.size_empty, List.length_nil]
    omega
  have rootAndRest := BlockAt.suffix _ _ _ _ assembled
  have rootBlock : BlockAt resident (2 * parameters.channels) (rootCode parameters width) := by
    simpa only [NativeRootLoad.code_length, Nat.zero_add] using BlockAt.prefix _ _ _ _ rootAndRest
  obtain ⟨produced, rootTicks, rootTrace, rootBound, producedHeap,
    _, producedStack, producedOutput, producedPC, producedRunning⟩ :=
    NativeRootBuilder.source_execution parameters K resident loaded (2 * parameters.channels)
      (by simpa only [NativeRootLoad.words_length, Nat.zero_add] using loadedPC) loadedRunning
      (by change 2 * parameters.channels + (rootCode parameters width).length < _; omega) boolFits
      (by rw [loadedSize]; omega) loadedTable.2 rootBlock
  let realized := Physical.realizeBridge parameters.bridge parameters.positiveBuses K
  have producedTable : TableStored produced.heap parameters.channels (sourcePhysicalRoots parameters realized) := by
    rw [producedHeap]
    simpa only [loadedSize] using NativeRootBuilder.appended_table loaded.heap
      (sourcePhysicalRoots parameters realized)
  have producedLive : produced.liveWords = state.liveWords + SourceInitialIDs.rootCount parameters := by
    have producedSize := producedTable.1
    simp only [State.liveWords, producedStack, producedOutput]
    have previous := loadedLive
    simp only [State.liveWords] at previous
    omega
  have circuitAndRest : BlockAt resident (circuitEntry parameters width)
      (circuitCode parameters width ++
        (OutputProgram.emitCode width (addresses parameters.channels (compile parameters).toState.count) ++ [.halt])) := by
    simpa only [NativeRootLoad.code_length, Nat.zero_add, circuitEntry] using BlockAt.suffix _ _ _ _ rootAndRest
  have circuitBlock := BlockAt.prefix _ _ _ _ circuitAndRest
  obtain ⟨evaluated, circuitTicks, circuitTrace, circuitBound, evaluatedTable,
    evaluatedStack, evaluatedOutput, evaluatedPC, evaluatedRunning⟩ :=
    NativeCircuitExecution.execution resident produced (sourceCircuit parameters) (sourcePhysicalRoots parameters realized)
      parameters.channels (circuitEntry parameters width) producedPC producedRunning
      (by change circuitEntry parameters width + (circuitCode parameters width).length < _; dsimp [circuitEntry]; omega)
      boolFits tableRoom producedTable circuitBlock
  have evaluatedLive : evaluated.liveWords = state.liveWords + (compile parameters).toState.count := by
    have size := evaluatedTable.1
    have previous := producedLive
    have beforeSize := producedTable.1
    simp only [State.liveWords, evaluatedStack, evaluatedOutput]
    simp only [State.liveWords] at previous
    omega
  have emitAndHalt : BlockAt resident (emitEntry parameters width)
      (OutputProgram.emitCode width (addresses parameters.channels (compile parameters).toState.count) ++ [.halt]) := by
    simpa only [emitEntry] using BlockAt.suffix _ _ _ _ circuitAndRest
  have emitBlock := BlockAt.prefix _ _ _ _ emitAndHalt
  have heapFits : evaluated.heap.size < 2 ^ width := by have size := evaluatedTable.1; omega
  have validAddresses : ∀ address ∈ addresses parameters.channels (compile parameters).toState.count,
      address < evaluated.heap.size := by
    intro address member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    have size := evaluatedTable.1
    have bound := index.isLt
    omega
  obtain ⟨emitted, emitTrace, emittedHeap, emittedStack, emittedOutput, emittedPC, emittedRunning⟩ :=
    OutputProgram.emitCode_execution resident evaluated (emitEntry parameters width)
      (addresses parameters.channels (compile parameters).toState.count) evaluatedPC evaluatedRunning
      (by simp only [addresses_length]; dsimp [emitEntry, circuitEntry]; omega) heapFits validAddresses emitBlock
  have haltBlock : BlockAt resident (emitEntry parameters width + 3 * (compile parameters).toState.count) [.halt] := by
    simpa only [OutputProgram.emitCode_length, addresses_length] using BlockAt.suffix _ _ _ _ emitAndHalt
  have haltFetch : resident[emitEntry parameters width + 3 * (compile parameters).toState.count]? = some .halt := by
    simpa using haltBlock 0 (by simp)
  have haltTrace := OutputProgram.halt_execution resident emitted
    (emitEntry parameters width + 3 * (compile parameters).toState.count)
    (by simpa only [addresses_length] using emittedPC) emittedRunning
    (by dsimp [emitEntry, circuitEntry]; omega) haltFetch
  let final := { emitted.advance with halted := true }
  have emittedLive : emitted.liveWords = state.liveWords + 2 * (compile parameters).toState.count := by
    simp only [State.liveWords, emittedHeap, emittedStack, emittedOutput, List.length_append,
      List.length_reverse, List.length_map, addresses_length]
    have previous := evaluatedLive
    simp only [State.liveWords] at previous
    omega
  have fullTrace := (((loadTrace.append rootTrace).append circuitTrace).append emitTrace).append haltTrace
  have peakEq : max (max (max (max state.liveWords (loaded.liveWords + SourceInitialIDs.rootCount parameters))
      (produced.liveWords + (sourceCircuit parameters).gateCount))
      (evaluated.liveWords + (addresses parameters.channels (compile parameters).toState.count).length)) emitted.liveWords =
      state.liveWords + 2 * (compile parameters).toState.count := by
    rw [loadedLive, producedLive, evaluatedLive, emittedLive, addresses_length]
    omega
  refine ⟨final, 2 * parameters.channels + rootTicks + circuitTicks + 3 * (compile parameters).toState.count + 1,
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [peakEq] at fullTrace
    simpa only [NativeRootLoad.words_length, addresses_length] using fullTrace
  · change _ ≤ 2 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters +
      (NativeCircuitExecution.code width parameters.channels (circuitEntry parameters width) (sourceCircuit parameters)).length +
      3 * (compile parameters).toState.count + 1
    omega
  · change TableStored emitted.heap parameters.channels _
    rw [emittedHeap]
    exact evaluatedTable
  · change emitted.stack = suffix
    rw [emittedStack, evaluatedStack, producedStack, loadedStack]
  · change emitted.output = _
    rw [emittedOutput, emitted_words evaluated.heap parameters.channels _ evaluatedTable,
      evaluatedOutput, producedOutput, loadedOutput]
    rfl

end Controller.Cost.NativeRealizedCore
