module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGOutputs
public import Controller.Cost.SharedRootLoop

@[expose] public section

/-! Runtime root identifiers are read from the loaded packet. Every output
uses the one evaluated node table, with a fixed twelve-instruction loop. -/
namespace Controller.Cost.UniformDAGRuntimeOutputs
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun

def rootBase (heap : Array (Word width)) (rows : List Row) : ℕ :=
  heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length

theorem cache_root_cell (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (i : ℕ) (valid : i < roots.length) :
    (cacheHeap width heap rows roots)[rootBase heap rows + i]'(by
      simp [rootBase]; omega) = word width (roots[i]'valid) := by
  let before := rowHeaders rows ++ rowBases rows (heap.size + 6 * rows.length)
    (heap.size + 6 * rows.length + (rowChildren rows).length) ++ rowArities rows ++
    rowChildren rows ++ rowGuards rows
  have length : before.length = 6 * rows.length + (rowChildren rows).length +
      (rowGuards rows).length := by simp [before]; omega
  have packet : serializedRows heap.size rows roots = before ++ roots ++ [] := by
    simp [serializedRows, before, List.append_assoc]
  have cell := allocated_segment_word heap before roots [] i valid
  simpa [cacheHeap, packet, length, rootBase, Nat.add_assoc] using cell

/-- The evaluator's concrete heap supplies every root identifier and value to
the runtime output loop. No root-dependent instruction is required. -/
theorem roots_represented (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (rootMatches : RootsMatch graph roots)
    (values : Assignment n)
    (fits : (evaluationHeap heap rows roots values (graph.evalTable values)).size ≤ 2 ^ width) :
    SharedRootLoop.RepresentedRoots
      (evaluationHeap heap rows roots values (graph.evalTable values))
      (rootBase heap rows) ((cacheHeap width heap rows roots).size + n)
      (graph.roots.map (fun root => (root.val, graph.eval values root))) := by
  change roots = graph.roots.map Fin.val at rootMatches
  have lengths : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have bounds : ∀ i, (valid : i < graph.roots.length) →
      rootBase heap rows + i < (cacheHeap width heap rows roots).size := by
    intro i valid
    simp only [rootBase, cacheHeap_size]
    omega
  have channelBounds : ∀ i, (valid : i < graph.roots.length) →
      rootBase heap rows + i < (channelHeap heap rows roots values).size := by
    intro i valid
    have := bounds i valid
    simp only [channelHeap_size]
    omega
  have cells : ∀ i, (valid : i < graph.roots.length) →
      (channelHeap heap rows roots values)[rootBase heap rows + i]'(channelBounds i valid) =
        word width (graph.roots[i]'valid).val := by
    intro i valid
    have preserved := source_preserved (cacheHeap width heap rows roots) values
      (rootBase heap rows + i) (bounds i valid)
    have cell := cache_root_cell heap rows roots i (by omega)
    have identifier : roots[i]'(by omega) = (graph.roots[i]'valid).val := by
      simp only [rootMatches, List.getElem_map]
    exact preserved.trans (cell.trans (congrArg (word width) identifier))
  have represented := SharedRootLoop.represented_ids (channelHeap heap rows roots values)
    (graph.evalTable values) graph.roots (rootBase heap rows)
    (by simpa only [evaluationHeap, withValues_size] using fits) channelBounds cells
  simpa only [evaluationHeap, channelHeap_size, DAG.evalTable_eq_eval] using represented

def code (width n : ℕ) (rows : List Row) (roots : List ℕ) (values : Assignment n) : Code width :=
  UniformDAGResources.code width n rows roots values ++
  SharedRootLoop.setupCode width (rootBase (packetHeaderHeap width n rows roots) rows) roots.length ++
  SharedRootLoop.code width (161 + 2 * n)
    ((cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n) ++ [.halt]

def program (width n : ℕ) (rows : List Row) (roots : List ℕ) (values : Assignment n) :
    Program width 4 := (code width n rows roots values).toArray

@[simp] theorem code_length (width n : ℕ) (rows : List Row) (roots : List ℕ)
    (values : Assignment n) : (code width n rows roots values).length = 174 + 2 * n := by
  simp [code]; omega

theorem assignment_independent (width n : ℕ) (rows : List Row) (roots : List ℕ)
    (first second : Assignment n) :
    program width n rows roots first = program width n rows roots second := by
  simp only [program, code, UniformDAGResources.code, UniformDAGTypedNode.layout,
    channelHeap_size]

/-- Only source counts select instructions. Root identifiers, gate labels,
incidence identifiers, and assignment values stay in the input packet. -/
theorem shape_independent (width n : ℕ) (firstRows secondRows : List Row)
    (firstRoots secondRoots : List ℕ) (firstValues secondValues : Assignment n)
    (nodes : firstRows.length = secondRows.length)
    (children : (rowChildren firstRows).length = (rowChildren secondRows).length)
    (guards : (rowGuards firstRows).length = (rowGuards secondRows).length)
    (roots : firstRoots.length = secondRoots.length) :
    program width n firstRows firstRoots firstValues =
      program width n secondRows secondRoots secondValues := by
  simp only [program, code, UniformDAGResources.code, UniformDAGTypedNode.layout,
    channelHeap_size, cacheHeap_size, packetHeaderHeap_size, rootBase,
    nodes, children, guards, roots]

/-- Resident instructions and retained outputs have a linear word bound. -/
theorem resident_words_le (width : ℕ) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (values : Assignment n) (suffix output : List (Word width)) :
    programWords (program width n rows roots values) +
      (8 * graph.countedSize + 14 + suffix.length + output.length) ≤
      18 * graph.countedSize + 710 + suffix.length + output.length := by
  have size := graph.countedSize_eq
  simp only [programWords, program, List.size_toArray, code_length]
  omega

set_option maxHeartbeats 2000000 in
/-- The cold packet is evaluated once; root IDs are fetched at runtime from
that same heap, all outputs are emitted, and the resident machine halts. -/
theorem execution_at_width (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (width : ℕ) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (suffix output : List (Word width)) (address loaded temporary : Word width) :
    ∃ final ticks peak,
      Execution (program width n rows roots values)
        ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
          ((inputPacket n 0 rows roots).map (word width) ++
            List.ofFn (fun i => boolWord width (values i)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 97 * graph.countedSize + 37 ∧
      peak ≤ 8 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ output ∧
      final.halted = true := by
  let resident := program width n rows roots values
  let core := UniformDAGResources.code width n rows roots values
  let setup := SharedRootLoop.setupCode width
    (rootBase (packetHeaderHeap width n rows roots) rows) roots.length
  let loop := SharedRootLoop.code width (161 + 2 * n)
    ((cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n)
  have whole : BlockAt resident 0 (core ++ (setup ++ (loop ++ [.halt]))) := by
    intro offset bound
    simp [resident, program, code, core, setup, loop, List.getElem?_toArray, List.append_assoc]
  have coreBlock := BlockAt.prefix resident 0 core _ whole
  have restBlock := BlockAt.suffix resident 0 core _ whole
  have setupBlock := BlockAt.prefix resident (0 + core.length) setup _ restBlock
  have loopRest := BlockAt.suffix resident (0 + core.length) setup _ restBlock
  have rootBlock := BlockAt.prefix resident (0 + core.length + setup.length) loop [.halt] loopRest
  have haltBlock := BlockAt.suffix resident (0 + core.length + setup.length) loop [.halt] loopRest
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
  have haltFetched : resident[173 + 2 * n]? = some .halt := by
    have fetched := haltBlock 0 (by simp)
    simpa only [core, setup, loop, UniformDAGResources.code_length,
      SharedRootLoop.setupCode_length, SharedRootLoop.code_length, Nat.zero_add,
      Nat.add_zero, List.getElem?_cons_zero,
      show 159 + 2 * n + 2 + 12 = 173 + 2 * n from by omega] using fetched
  have haltTrace := OutputProgram.halt_execution resident after (173 + 2 * n)
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using afterPC)
    afterRunning (by omega) haltFetched
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
  have joined := ((trace.append setupTrace).append rootTrace).append haltTrace
  refine ⟨{ after.advance with halted := true }, _, _, joined, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [List.length_map]
    omega
  · simp only [List.length_map]
    rw [readyLive, middleLive] at afterLive
    rw [readyLive, middleLive]
    omega
  · exact afterStack.trans (readyStack.trans stack)
  · change after.output = _
    simpa [DAG.outputValues, List.map_map, Function.comp_def, readyOut, out] using afterOut

/-- Resident shared-kernel layout determined entirely by the original counts. -/
def shapeLayout (channels nodes children guards roots : ℕ) : UniformDAGNode.Layout where
  tagBase := 5
  headBase := 6
  channelBase := 5 + 6 * nodes + children + guards + roots
  nodeBase := 5 + 6 * nodes + children + guards + roots + channels
  childArityBase := 5 + 4 * nodes
  childSourceBase := 5 + 2 * nodes
  guardArityBase := 5 + 4 * nodes + 1
  guardSourceBase := 5 + 2 * nodes + 1

def shapeProgram (width channels nodes children guards roots : ℕ) : Program width 4 :=
  (ForestInputMetadata.fullCode width 0 ++
    (InputLoad.code channels ++ UniformDAGLoop.code width (33 + 2 * channels) 1
      (shapeLayout channels nodes children guards roots)) ++
    SharedRootLoop.setupCode width (5 + 6 * nodes + children + guards) roots ++
    SharedRootLoop.code width (161 + 2 * channels)
      (5 + 6 * nodes + children + guards + roots + channels) ++
      [Instruction.halt (width := width) (registers := 4)]).toArray

theorem program_shape (width n : ℕ) (rows : List Row) (roots : List ℕ) (values : Assignment n) :
    program width n rows roots values = shapeProgram width n rows.length
      (rowChildren rows).length (rowGuards rows).length roots.length := by
  simp only [program, code, shapeProgram, UniformDAGResources.code, UniformDAGTypedNode.layout,
    shapeLayout, channelHeap_size, cacheHeap_size, packetHeaderHeap_size, rootBase, Nat.reduceAdd]

@[simp] theorem shapeProgram_size (width channels nodes children guards roots : ℕ) :
    (shapeProgram width channels nodes children guards roots).size = 174 + 2 * channels := by
  simp [shapeProgram]; omega

end Controller.Cost.UniformDAGRuntimeOutputs
