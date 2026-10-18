module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeRootLoad
public import Controller.Cost.NativeCircuitSize

@[expose] public section

/-! A complete native run consumes raw root words, evaluates all allocated
variables, emits their words in allocation order, and executes a fetched halt. -/
namespace Controller.Cost.NativeCircuitComplete
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution Controller.CNF

def addresses (variableCount : Nat) : List Nat := (List.finRange variableCount).map Fin.val

@[simp] theorem addresses_length (variableCount : Nat) : (addresses variableCount).length = variableCount := by
  simp [addresses]

def code (width : Nat) (circuit : AcyclicCircuit rootCount variableCount) : List (Instruction width 4) :=
  NativeRootLoad.code width rootCount ++
    (NativeCircuitExecution.code width 0 (2 * rootCount) circuit ++
      (OutputProgram.emitCode width (addresses variableCount) ++ [.halt]))

@[simp] theorem code_length (width : Nat) (circuit : AcyclicCircuit rootCount variableCount) :
    (code width circuit).length = 2 * rootCount +
      (NativeCircuitExecution.code width 0 (2 * rootCount) circuit).length + 3 * variableCount + 1 := by
  simp [code, OutputProgram.emitCode_length]
  omega

theorem emitted_words (heap : Array (Word width)) (values : Fin variableCount → Bool)
    (stored : TableStored heap 0 values) :
    (addresses variableCount).map (OutputProgram.heapValue heap) = NativeRootLoad.words width values := by
  simp only [addresses, NativeRootLoad.words, List.ofFn_eq_map, List.map_map]
  apply List.map_congr_left
  intro index _
  obtain ⟨valid, cell⟩ := stored.2 index
  simpa only [Function.comp_apply, Nat.zero_add, OutputProgram.heapValue_eq heap index.val (by simpa using valid)] using cell

set_option maxHeartbeats 3000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (circuit : AcyclicCircuit rootCount variableCount) (roots : Fin rootCount → Bool)
    (suffix : List (Word width)) (position : state.pc = word width 0) (running : state.halted = false)
    (empty : state.heap = #[]) (input : state.stack = NativeRootLoad.words width roots ++ suffix)
    (room : (code width circuit).length < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (tableRoom : variableCount < 2 ^ width)
    (physical : BlockAt resident 0 (code width circuit)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + circuit.gateCount + variableCount) ∧
      ticks ≤ (code width circuit).length ∧ TableStored final.heap 0 (circuit.evaluate roots) ∧
      final.stack = suffix ∧ final.output = (NativeRootLoad.words width (circuit.evaluate roots)).reverse ++ state.output ∧
      final.halted = true := by
  have rootsLe := circuit.roots_le
  have loadBlock : BlockAt resident 0 (NativeRootLoad.code width rootCount) :=
    BlockAt.prefix _ _ _ _ physical
  obtain ⟨loaded, loadTrace, loadedHeap, loadedStack, loadedOutput, loadedPC, loadedRunning⟩ :=
    NativeRootLoad.execution resident state (NativeRootLoad.words width roots) suffix 0 position running
      (by rw [code_length] at room; simp only [NativeRootLoad.words_length]; omega)
      (by simpa only [empty, Array.size_empty, Nat.zero_add, NativeRootLoad.words_length] using rootsLe.trans_lt tableRoom)
      input (by simpa only [NativeRootLoad.words_length] using loadBlock)
  have loadedTable : TableStored loaded.heap 0 roots := by
    rw [loadedHeap, empty, Array.empty_append]
    exact NativeRootLoad.table width roots
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp only [State.liveWords, loadedHeap, loadedStack, loadedOutput, empty,
      Array.empty_append, List.size_toArray, NativeRootLoad.words_length, input,
      List.length_append, Array.size_empty, List.length_nil]
    omega
  have bodyAndRest := BlockAt.suffix _ _ _ _ physical
  have bodyBlock : BlockAt resident (2 * rootCount)
      (NativeCircuitExecution.code width 0 (2 * rootCount) circuit) := by
    simpa only [NativeRootLoad.code_length, Nat.zero_add] using BlockAt.prefix _ _ _ _ bodyAndRest
  obtain ⟨evaluated, bodyTicks, bodyTrace, bodyBound, evaluatedTable,
    evaluatedStack, evaluatedOutput, evaluatedPC, evaluatedRunning⟩ :=
    NativeCircuitExecution.execution resident loaded circuit roots 0 (2 * rootCount)
      (by simpa only [NativeRootLoad.words_length, Nat.zero_add] using loadedPC) loadedRunning
      (by rw [code_length] at room; omega) boolFits (by simpa using tableRoom) loadedTable bodyBlock
  have evaluatedLive : evaluated.liveWords = state.liveWords + circuit.gateCount := by
    have allocated := circuit.variable_count
    have evaluatedSize := evaluatedTable.1
    have loadedSize := loadedTable.1
    simp only [State.liveWords, evaluatedStack, evaluatedOutput, loadedStack, loadedOutput,
      input, List.length_append, NativeRootLoad.words_length, empty, Array.size_empty]
    omega
  let emitEntry := 2 * rootCount + (NativeCircuitExecution.code width 0 (2 * rootCount) circuit).length
  have emitAndHalt : BlockAt resident emitEntry (OutputProgram.emitCode width (addresses variableCount) ++ [.halt]) := by
    simpa only [NativeRootLoad.code_length, Nat.zero_add] using BlockAt.suffix _ _ _ _ bodyAndRest
  have emitBlock := BlockAt.prefix _ _ _ _ emitAndHalt
  have heapFits : evaluated.heap.size < 2 ^ width := by
    have size := evaluatedTable.1
    omega
  have validAddresses : ∀ address ∈ addresses variableCount, address < evaluated.heap.size := by
    intro address member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    have size := evaluatedTable.1
    have bound := index.isLt
    omega
  obtain ⟨emitted, emitTrace, emittedHeap, emittedStack, emittedOutput, emittedPC, emittedRunning⟩ :=
    OutputProgram.emitCode_execution resident evaluated emitEntry (addresses variableCount)
      evaluatedPC evaluatedRunning (by rw [code_length] at room; simp only [addresses_length]; dsimp [emitEntry]; omega)
      heapFits validAddresses emitBlock
  have haltBlock : BlockAt resident (emitEntry + 3 * variableCount) [.halt] := by
    simpa only [OutputProgram.emitCode_length, addresses_length] using BlockAt.suffix _ _ _ _ emitAndHalt
  have haltFetch : resident[emitEntry + 3 * variableCount]? = some .halt := by
    simpa using haltBlock 0 (by simp)
  have haltTrace := OutputProgram.halt_execution resident emitted (emitEntry + 3 * variableCount)
    (by simpa only [addresses_length] using emittedPC) emittedRunning
    (by rw [code_length] at room; dsimp [emitEntry]; omega) haltFetch
  let final := { emitted.advance with halted := true }
  have emittedLive : emitted.liveWords = state.liveWords + circuit.gateCount + variableCount := by
    have wordsEqual := emitted_words evaluated.heap (circuit.evaluate roots) evaluatedTable
    simp only [State.liveWords, emittedHeap, emittedStack, emittedOutput,
      List.length_append, List.length_reverse, List.length_map, addresses_length]
    have previousLive := evaluatedLive
    simp only [State.liveWords] at previousLive
    omega
  have fullTrace := ((loadTrace.append bodyTrace).append emitTrace).append haltTrace
  have peakEq : max (max (max state.liveWords (loaded.liveWords + circuit.gateCount))
      (evaluated.liveWords + (addresses variableCount).length)) emitted.liveWords =
      state.liveWords + circuit.gateCount + variableCount := by
    rw [loadedLive, evaluatedLive, emittedLive, addresses_length]
    omega
  refine ⟨final, 2 * rootCount + bodyTicks + 3 * variableCount + 1, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [peakEq] at fullTrace
    simpa only [NativeRootLoad.words_length, addresses_length] using fullTrace
  · rw [code_length]
    omega
  · change TableStored emitted.heap 0 (circuit.evaluate roots)
    rw [emittedHeap]
    exact evaluatedTable
  · change emitted.stack = suffix
    rw [emittedStack, evaluatedStack, loadedStack]
  · change emitted.output = _
    rw [emittedOutput, emitted_words evaluated.heap (circuit.evaluate roots) evaluatedTable,
      evaluatedOutput, loadedOutput]

end Controller.Cost.NativeCircuitComplete
