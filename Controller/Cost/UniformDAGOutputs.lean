module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGResources
public import Controller.Cost.OutputProgram
public import Controller.Cost.RawNumberingCounts

@[expose] public section

/-! Shared topological evaluation followed by fetched root loads and halt.
Repeated root incidences reuse the same stored node table. -/
namespace Controller.Cost.UniformDAGOutputs
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGSource Controller.Cost.OutputProgram
open Controller.Cost.UniformDAGRun

/-- Canonical source rows erase finite bounds but retain every incidence. -/
def rowsOfGraph (graph : DAG n) : List Row :=
  List.ofFn (fun node => RawNumberingCounts.rowOfGate (RawGate.ofGate (graph.node node)))

theorem rowsOfGraph_match (graph : DAG n) : RowsMatch graph (rowsOfGraph graph) := by
  refine ⟨by simp [rowsOfGraph], ?_⟩
  intro node
  simp only [rowsOfGraph, List.getElem_ofFn]
  cases graph.node node <;>
    simp [RawNumberingCounts.rowOfGate, RawGate.ofGate, Row.Matches, Gate.children, Gate.guardLabels]

theorem rowsOfGraph_heads (graph : DAG n) :
    HeadsMatch graph (rowsOfGraph graph) (rowsOfGraph_match graph) := by
  constructor
  intro node
  simp only [rowsOfGraph, List.getElem_ofFn]
  cases graph.node node <;> rfl

def addresses (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat) : List Nat :=
  graph.roots.map (fun root =>
    (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n + root.val)

def code (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (values : Assignment n) : List (Instruction width 4) :=
  UniformDAGResources.code width n rows roots values ++ emitCode width (addresses width graph rows roots) ++ [.halt]

def program (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (values : Assignment n) : Program width 4 :=
  (code width graph rows roots values).toArray

/-- Assignment values are runtime input and do not select any instruction. -/
theorem program_assignment_independent (width : Nat) (graph : DAG n) (rows : List Row)
    (roots : List Nat) (first second : Assignment n) :
    program width graph rows roots first = program width graph rows roots second := by
  simp only [program, code, UniformDAGResources.code, UniformDAGTypedNode.layout,
    channelHeap_size]

@[simp] theorem addresses_length (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat) :
    (addresses width graph rows roots).length = graph.roots.length := by
  simp [addresses]

@[simp] theorem code_length (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (values : Assignment n) :
    (code width graph rows roots values).length = 160 + 2 * n + 3 * graph.roots.length := by
  simp [code]; omega

/-- Resident instructions and retained outputs obey a linear word bound. -/
theorem resident_words_le (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (values : Assignment n) (suffix output : List (Word width)) :
    programWords (program width graph rows roots values) +
      (8 * graph.countedSize + 14 + suffix.length + output.length) ≤
      28 * graph.countedSize + 654 + suffix.length + output.length := by
  have size := graph.countedSize_eq
  simp only [programWords, program, List.size_toArray, code_length]
  omega

theorem output_cells (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (values : Assignment n) :
    (addresses width graph rows roots).map
      (heapValue (evaluationHeap (packetHeaderHeap width n rows roots) rows roots values
        (graph.evalTable values))) = (graph.outputValues values).map (boolWord width) := by
  unfold addresses DAG.outputValues
  simp only [List.map_map]
  apply List.map_congr_left
  intro root _
  simp only [Function.comp_apply]
  have cell := ForestInputStored.value_cell
    (channelHeap (packetHeaderHeap width n rows roots) rows roots values) (graph.evalTable values) root
  have bound : (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n + root.val <
      (evaluationHeap (packetHeaderHeap width n rows roots) rows roots values (graph.evalTable values)).size := by
    simp only [evaluationHeap_size]
    omega
  rw [heapValue_eq _ _ bound]
  simpa only [evaluationHeap, channelHeap_size, DAG.evalTable_eq_eval] using cell

set_option maxHeartbeats 2000000 in
/-- Cold source input is evaluated once, every root is emitted, and the machine halts. -/
theorem execution_at_width (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (width : Nat) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (suffix output : List (Word width))
    (address loaded temporary : Word width) :
    ∃ final ticks peak,
      Execution (program width graph rows roots values)
        ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
          ((inputPacket n 0 rows roots).map (word width) ++
            List.ofFn (fun i => boolWord width (values i)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 88 * graph.countedSize + 34 ∧
      peak ≤ 8 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ output ∧
      final.halted = true := by
  let resident := program width graph rows roots values
  let core := UniformDAGResources.code width n rows roots values
  let outputs := emitCode width (addresses width graph rows roots)
  have whole : BlockAt resident 0 (core ++ (outputs ++ [.halt])) := by
    intro offset bound
    simp [resident, program, code, core, outputs, List.getElem?_toArray, List.append_assoc]
  have coreBlock := BlockAt.prefix resident 0 core (outputs ++ [.halt]) whole
  have restBlock := BlockAt.suffix resident 0 core (outputs ++ [.halt]) whole
  have outputBlock := BlockAt.prefix resident (0 + core.length) outputs [.halt] restBlock
  have haltBlock := BlockAt.suffix resident (0 + core.length) outputs [.halt] restBlock
  have sourceBlock := BlockAt.prefix resident 0 (ForestInputMetadata.fullCode width 0) _ coreBlock
  have rest := BlockAt.suffix resident 0 (ForestInputMetadata.fullCode width 0) _ coreBlock
  simp only [ForestInputMetadata.fullCode_length, Nat.zero_add] at rest
  have loadBlock := BlockAt.prefix resident 33 (InputLoad.code n) _ rest
  have loopBlock := BlockAt.suffix resident 33 (InputLoad.code n) _ rest
  simp only [InputLoad.code_length] at loopBlock
  have cap := capacity
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
      suffix output address loaded temporary 0 (by omega)
      (by rw [heapSize]; omega) sourceBlock loadBlock
      (by simpa only [Nat.zero_add] using loopBlock)
  have emitted := emitCode_execution resident middle (159 + 2 * n)
    (addresses width graph rows roots)
    (by simpa only [Nat.zero_add, show 33 + 2 * n + 126 = 159 + 2 * n from by omega] using pc) running
    (by rw [addresses_length]; omega)
    (by rw [heap, evaluationHeap_size, heapSize]; omega)
    (by
      intro a member
      obtain ⟨root, _, rfl⟩ := List.mem_map.mp member
      rw [heap, evaluationHeap_size]
      omega)
    (by simpa only [core, UniformDAGResources.code_length, Nat.zero_add] using outputBlock)
  obtain ⟨after, emitTrace, afterHeap, afterStack, afterOutput, afterPC, afterRunning⟩ := emitted
  have haltFetched : resident[159 + 2 * n + 3 * graph.roots.length]? = some .halt := by
    have fetched := haltBlock 0 (by simp)
    simpa only [core, outputs, UniformDAGResources.code_length, emitCode_length,
      addresses_length, Nat.zero_add, Nat.add_zero, List.getElem?_cons_zero] using fetched
  have haltTrace := halt_execution resident after (159 + 2 * n + 3 * graph.roots.length)
    (by simpa using afterPC) afterRunning (by omega) haltFetched
  have middleLive := trace.final_storage_le
  have afterLive : after.liveWords = middle.liveWords + graph.roots.length := by
    simp only [State.liveWords, afterHeap, afterStack, afterOutput, List.length_append,
      List.length_reverse, List.length_map, addresses_length]
    omega
  have joined := (trace.append emitTrace).append haltTrace
  refine ⟨{ after.advance with halted := true }, _, _, joined, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [addresses_length]
    omega
  · simp only [addresses_length]
    omega
  · exact afterStack.trans stack
  · change after.output = _
    rw [afterOutput, heap, output_cells, out]

set_option maxHeartbeats 2000000 in
/-- Cold source input is evaluated once, every root is emitted, and the machine halts. -/
theorem execution (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (suffix output : List (Word (UniformDAGResources.chosenWidth graph)))
    (address loaded temporary : Word (UniformDAGResources.chosenWidth graph)) :
    let width := UniformDAGResources.chosenWidth graph
    ∃ final ticks peak,
      Execution (program width graph rows roots values)
        ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
          ((inputPacket n 0 rows roots).map (word width) ++
            List.ofFn (fun i => boolWord width (values i)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 88 * graph.countedSize + 34 ∧
      peak ≤ 8 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ output ∧
      final.halted = true := by
  exact execution_at_width graph rows roots matched heads rootMatches values
    (UniformDAGResources.chosenWidth graph) (UniformDAGResources.capacity graph)
    suffix output address loaded temporary

set_option maxHeartbeats 2000000 in
/-- One fixed instruction array works for every assignment supplied on the input stack. -/
theorem fixed_program_execution (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (suffix output : List (Word (UniformDAGResources.chosenWidth graph)))
    (address loaded temporary : Word (UniformDAGResources.chosenWidth graph)) :
    let width := UniformDAGResources.chosenWidth graph
    ∃ final ticks peak,
      Execution (program width graph rows roots (fun _ => false))
        ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
          ((inputPacket n 0 rows roots).map (word width) ++
            List.ofFn (fun i => boolWord width (values i)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 88 * graph.countedSize + 34 ∧
      peak ≤ 8 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ output ∧
      final.halted = true := by
  have run := execution graph rows roots matched heads rootMatches values suffix output address loaded temporary
  dsimp only at run ⊢
  rw [program_assignment_independent (UniformDAGResources.chosenWidth graph) graph rows roots
    values (fun _ => false)] at run
  exact run

set_option maxHeartbeats 2000000 in
/-- Linear shared evaluation on the canonical counted representation, without matching premises. -/
theorem supplied_graph_execution (graph : DAG n) (values : Assignment n)
    (suffix output : List (Word (UniformDAGResources.chosenWidth graph)))
    (address loaded temporary : Word (UniformDAGResources.chosenWidth graph)) :
    let width := UniformDAGResources.chosenWidth graph
    ∃ final ticks peak,
      Execution (program width graph (rowsOfGraph graph) (graph.roots.map Fin.val) (fun _ => false))
        ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
          ((inputPacket n 0 (rowsOfGraph graph) (graph.roots.map Fin.val)).map (word width) ++
            List.ofFn (fun i => boolWord width (values i)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 88 * graph.countedSize + 34 ∧
      peak ≤ 8 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ output ∧
      final.halted = true := by
  exact fixed_program_execution graph (rowsOfGraph graph) (graph.roots.map Fin.val)
    (rowsOfGraph_match graph) (rowsOfGraph_heads graph) rfl values suffix output address loaded temporary

end Controller.Cost.UniformDAGOutputs
