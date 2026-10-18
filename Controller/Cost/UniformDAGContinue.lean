module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGRuntimeOutputs

@[expose] public section

/-! The shared evaluator returns to a resident caller after emitting all roots.
The endpoint remains running and exposes the exact evaluated heap for reuse
or reclamation before the next assignment. -/
namespace Controller.Cost.UniformDAGContinue
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.UniformDAGRuntimeOutputs

def code (width n : ℕ) (rows : List Row) (roots : List ℕ) (values : Assignment n) : Code width :=
  UniformDAGResources.code width n rows roots values ++
  SharedRootLoop.setupCode width (rootBase (packetHeaderHeap width n rows roots) rows) roots.length ++
  SharedRootLoop.code width (161 + 2 * n)
    ((cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n)

@[simp] theorem code_length (width n : ℕ) (rows : List Row) (roots : List ℕ)
    (values : Assignment n) : (code width n rows roots values).length = 173 + 2 * n := by
  simp [code]; omega

theorem execution_from_block (resident : Program width 4) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (suffix output : List (Word width)) (address loaded temporary : Word width)
    (physical : BlockAt resident 0 (code width n rows roots values)) :
    ∃ final ticks peak,
      Execution resident
        ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
          ((inputPacket n 0 rows roots).map (word width) ++
            List.ofFn (fun i => boolWord width (values i)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 97 * graph.countedSize + 36 ∧
      peak ≤ 8 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ output ∧
      final.heap = evaluationHeap (packetHeaderHeap width n rows roots) rows roots values (graph.evalTable values) ∧
      final.pc = word width (173 + 2 * n) ∧ final.halted = false := by
  let core := UniformDAGResources.code width n rows roots values
  let setup := SharedRootLoop.setupCode width
    (rootBase (packetHeaderHeap width n rows roots) rows) roots.length
  let loop := SharedRootLoop.code width (161 + 2 * n)
    ((cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n)
  have whole : BlockAt resident 0 (core ++ (setup ++ loop)) := by
    simpa only [code, core, setup, loop, List.append_assoc] using physical
  have coreBlock := BlockAt.prefix resident 0 core _ whole
  have restBlock := BlockAt.suffix resident 0 core _ whole
  have setupBlock := BlockAt.prefix resident (0 + core.length) setup _ restBlock
  have loopRest := BlockAt.suffix resident (0 + core.length) setup _ restBlock
  have rootBlock := loopRest
  have sourceBlock := BlockAt.prefix resident 0 (ForestInputMetadata.fullCode width 0) _ coreBlock
  have rest := BlockAt.suffix resident 0 (ForestInputMetadata.fullCode width 0) _ coreBlock
  simp only [ForestInputMetadata.fullCode_length, Nat.zero_add] at rest
  have loadBlock := BlockAt.prefix resident 33 (InputLoad.code n) _ rest
  have evalBlock := BlockAt.suffix resident 33 (InputLoad.code n) _ rest
  simp only [InputLoad.code_length] at evalBlock
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have heapSize :
      (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n + graph.nodeCount =
        5 + 7 * graph.nodeCount + graph.childIncidences + graph.guardIncidences +
          graph.roots.length + n := by
    simp only [cacheHeap_size, packetHeaderHeap_size]
    rw [matched.length_eq, children, guards, rootCount]
    omega
  obtain ⟨middle, ticks, peak, trace, time, space, heap, stack, out, pc, running⟩ :=
    UniformDAGRun.cold_execution resident graph rows roots matched heads rootMatches values
      suffix output address loaded temporary 0 (by omega) (by rw [heapSize]; omega)
      sourceBlock loadBlock (by simpa only [Nat.zero_add] using evalBlock)
  obtain ⟨ready, setupTrace, count, cursor, readyHeap, readyStack, readyOut, readyPC, readyRunning⟩ :=
    SharedRootLoop.setup_execution resident middle (159 + 2 * n)
      (rootBase (packetHeaderHeap width n rows roots) rows) roots.length
      (by simpa only [Nat.zero_add, show 33 + 2 * n + 126 = 159 + 2 * n from by omega] using pc)
      running (by omega)
      (by simpa only [core, UniformDAGResources.code_length, Nat.zero_add, setup] using setupBlock)
  have represented := roots_represented (packetHeaderHeap width n rows roots) graph rows roots rootMatches
    values (by rw [evaluationHeap_size, heapSize]; omega)
  have rootCursorFit : rootBase (packetHeaderHeap width n rows roots) rows + graph.roots.length < 2 ^ width := by
    have cacheSize := cacheHeap_size (width := width) (packetHeaderHeap width n rows roots) rows roots
    dsimp only [rootBase]
    omega
  obtain ⟨after, rootTrace, zero, endCursor, afterHeap, afterStack, afterOut, afterPC, afterRunning⟩ :=
    SharedRootLoop.execution resident ready (161 + 2 * n)
      ((cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n)
      (rootBase (packetHeaderHeap width n rows roots) rows)
      (graph.roots.map (fun root => (root.val, graph.eval values root)))
      (by simpa [readyHeap, heap] using represented) cursor
      (by simpa only [List.length_map, rootCount] using count)
      (by simpa only [List.length_map] using rootCursorFit)
      (by simp only [List.length_map]; omega)
      (by simpa only [show 159 + 2 * n + 2 = 161 + 2 * n from by omega] using readyPC)
      readyRunning (by omega)
      (by simpa only [core, setup, loop, UniformDAGResources.code_length,
        SharedRootLoop.setupCode_length, Nat.zero_add,
        show 159 + 2 * n + 2 = 161 + 2 * n from by omega] using rootBlock)
  have readyLive : ready.liveWords = middle.liveWords := by
    simp [State.liveWords, readyHeap, readyStack, readyOut]
  have middleLive : middle.liveWords = 5 +
      (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n + graph.nodeCount +
      suffix.length + output.length := by
    simp [State.liveWords, heap, stack, out, evaluationHeap_size]
    omega
  have afterLive : after.liveWords = ready.liveWords + graph.roots.length := by
    simp [State.liveWords, afterHeap, afterStack, afterOut]
    omega
  have joined := (trace.append setupTrace).append rootTrace
  refine ⟨after, _, _, joined, ?_, ?_, ?_, ?_, ?_, ?_, afterRunning⟩
  · simp only [List.length_map]
    omega
  · simp only [List.length_map]
    rw [readyLive, middleLive]
    omega
  · exact afterStack.trans (readyStack.trans stack)
  · simpa [DAG.outputValues, List.map_map, Function.comp_def, readyOut, out] using afterOut
  · exact afterHeap.trans (readyHeap.trans heap)
  · simpa only [show 161 + 2 * n + 12 = 173 + 2 * n by omega] using afterPC

end Controller.Cost.UniformDAGContinue
