module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootFinish

@[expose] public section

/-! One shared probe evaluates a retained graph, updates witnesses and reclaims temporary storage. -/
namespace Controller.Cost.SharedReusableProbe
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.RegisterWiden Controller.Cost.RawAdapterProgram
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRuntimeOutputs Controller.Cost.RawTransferLoops

def tableSize (width n : Nat) (rows : List Row) (roots : List Nat) : Nat :=
  (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat)
    (entry done : Nat) : Program width 8 :=
  (widenProgram (SharedGraphRound.kernel width n rows roots)).map (relocatedInstruction entry) ++
    SharedRootFinish.code width (entry + 126) done (tableSize width n rows roots) rows.length
      (rootBase (packetHeaderHeap width n rows roots) rows) (tableSize width n rows roots) roots.length

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 167 := by
  unfold code
  simp [widenProgram]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (witnesses suffix : List (Word width)) (candidate : Word width) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 167 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (input : state.stack = witnesses ++ suffix) (lengths : witnesses.length = graph.roots.length)
    (candidateHeld : state.reg 4 = candidate) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 72 * graph.countedSize + 22 ∧
      peak ≤ 8 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧
      final.stack = SharedRootAggregate.updated candidate
        (graph.roots.map (fun root => (root.val, graph.eval values root))) witnesses ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = candidate := by
  have all := physical
  unfold code at all
  have kernelCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have finishCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have kernelPhysical : ∀ index (valid : index < (widenProgram (SharedGraphRound.kernel width n rows roots)).size),
      resident[entry + index]? = some (relocatedInstruction entry
        ((widenProgram (SharedGraphRound.kernel width n rows roots))[index]'valid)) := by
    intro index valid
    simpa [Array.getElem?_eq_getElem valid] using kernelCode ⟨index, by simpa using valid⟩
  obtain ⟨evaluated, evalTicks, evalPeak, evalTrace, evalTime, evalSpace,
    evalHeap, evalStack, evalOutput, evalPC, evalRunning, evalFrame⟩ :=
    SharedGraphRound.execution resident state graph rows roots matched heads rootMatches values entry
      capacity kernelPhysical (by omega) position running heapStored
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have heapFits : tableSize width n rows roots + graph.nodeCount + graph.roots.length < 2 ^ width := by
    simp only [tableSize, cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount]
    omega
  have cursorFits : rootBase (packetHeaderHeap width n rows roots) rows + graph.roots.length < 2 ^ width := by
    simp only [rootBase, packetHeaderHeap_size, matched.length_eq, children, guards]
    simp only [tableSize, cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount] at heapFits
    omega
  let nodes := List.ofFn (fun id => boolWord width (graph.evalTable values id))
  have nodesLength : nodes.length = graph.nodeCount := by simp [nodes]
  have channelSize : (channelHeap (packetHeaderHeap width n rows roots) rows roots values).size =
      tableSize width n rows roots := by simp [tableSize]
  have represented := roots_represented (packetHeaderHeap width n rows roots) graph rows roots rootMatches values
    (by simp only [evaluationHeap_size]; change tableSize width n rows roots + graph.nodeCount ≤ 2 ^ width; omega)
  obtain ⟨final, finishTicks, finishTrace, finishTime, finalHeap, finalStack, finalOutput,
    finalPC, finalRunning, finalCandidate⟩ :=
    SharedRootFinish.execution resident evaluated
      (channelHeap (packetHeaderHeap width n rows roots) rows roots values) nodes witnesses suffix
      (graph.roots.map (fun root => (root.val, graph.eval values root))) (entry + 126) done
      (rootBase (packetHeaderHeap width n rows roots) rows) (tableSize width n rows roots) candidate
      evalPC evalRunning (by omega) (by simp [channelHeap_size, cacheHeap_size, packetHeaderHeap_size])
      (by omega) (by simpa only [channelSize, nodesLength, List.length_map] using heapFits)
      (by simpa only [List.length_map] using cursorFits) evalHeap (evalStack.trans input)
      (by simpa only [List.length_map] using lengths) ((evalFrame 4 (by decide)).trans candidateHeld)
      (by simpa only [evalHeap, tableSize] using represented)
      (by simpa only [widenProgram, Array.size_map, SharedGraphRound.kernel_size,
        channelSize, nodesLength, List.length_map, matched.length_eq, rootCount] using finishCode)
  have evaluatedLive : evaluated.liveWords = state.liveWords + graph.nodeCount := by
    simp only [State.liveWords, evalHeap, evalStack, evalOutput, heapStored,
      evaluationHeap_size, channelHeap_size]
    omega
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
  have joined := evalTrace.append finishTrace
  refine ⟨final, evalTicks + finishTicks, max evalPeak (evaluated.liveWords +
      (graph.roots.map (fun root => (root.val, graph.eval values root))).length), joined,
      ?_, ?_, finalHeap.trans heapStored.symm, finalStack, finalOutput.trans evalOutput,
      finalPC, finalRunning, finalCandidate⟩
  · simp only [nodesLength, List.length_map] at finishTime
    omega
  · simp only [List.length_map]
    rw [evaluatedLive]
    apply Nat.max_le.mpr
    constructor <;> omega

end Controller.Cost.SharedReusableProbe
