module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessCopy

@[expose] public section

/-! Shared evaluation with a retained copy of every node value. Successive
columns accumulate on the caller stack while the evaluation heap is reused. -/
namespace Controller.Cost.SharedTableProbe
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored Controller.Cost.RawTransferLoops
open Controller.Cost.RegisterWiden Controller.Cost.RawAdapterProgram

def words (graph : DAG n) (values : Assignment n) (width : Nat) : List (Word width) :=
  List.ofFn (fun id => boolWord width (graph.evalTable values id))

@[simp] theorem words_length (graph : DAG n) (values : Assignment n) :
    (words graph values width).length = graph.nodeCount := by simp [words]

def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  (widenProgram (SharedGraphRound.kernel width n rows roots)).map (relocatedInstruction entry) ++
    (SharedWitnessCopy.code width (entry + 126) (entry + 136)
      (SharedReusableProbe.tableSize width n rows roots) rows.length ++
      SharedEvaluationReclaim.code width (entry + 136) done rows.length)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 143 := by
  simp [code, widenProgram]

set_option maxHeartbeats 400000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 143 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 53 * graph.countedSize + 15 ∧ peak ≤ state.liveWords + 2 * graph.nodeCount + 4 ∧
      final.heap = state.heap ∧ final.stack = words graph values width ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = state.reg 4 := by
  have all := physical
  unfold code at all
  have evalAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  have tailAt' : CodeAt resident (entry + 126)
      (SharedWitnessCopy.code width (entry + 126) (entry + 136)
        (SharedReusableProbe.tableSize width n rows roots) rows.length ++
        SharedEvaluationReclaim.code width (entry + 136) done rows.length) := by
    simpa only [Array.size_map, widenProgram, SharedGraphRound.kernel_size] using tailAt
  have copyAt := RawSharedOrdered.takePrefix resident (entry + 126) _ _ tailAt'
  have reclaimAt := RawSharedOrdered.takeSuffix resident (entry + 126) _ _ tailAt'
  have kernelPhysical : ∀ index (valid : index < (widenProgram (SharedGraphRound.kernel width n rows roots)).size),
      resident[entry + index]? = some (relocatedInstruction entry
        ((widenProgram (SharedGraphRound.kernel width n rows roots))[index]'valid)) := by
    intro index valid
    simpa only [Array.getElem?_eq_getElem valid, Array.getElem?_map, Option.map_some] using evalAt ⟨index, by simpa using valid⟩
  obtain ⟨evaluated, evalTicks, evalPeak, evalTrace, evalTime, evalSpace, evalHeap, evalStack,
      evalOutput, evalPC, evalRunning, evalFrame⟩ :=
    SharedGraphRound.execution resident state graph rows roots matched heads rootMatches values entry
      capacity kernelPhysical (by omega) position running heapStored
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have tableBound : SharedReusableProbe.tableSize width n rows roots + graph.nodeCount < 2 ^ width := by
    simp only [SharedReusableProbe.tableSize, cacheHeap_size, packetHeaderHeap_size,
      matched.length_eq, children, guards, rootCount]
    omega
  have tablePositive : 0 < SharedReusableProbe.tableSize width n rows roots := by
    simp [SharedReusableProbe.tableSize]
  have cells : ∀ i (hi : i < (words graph values width).length),
      evaluated.heap[SharedReusableProbe.tableSize width n rows roots + i]? =
        some (words graph values width)[i] := by
    intro i hi
    have valid : i < graph.nodeCount := by simpa using hi
    rw [evalHeap]
    change (withValues (channelHeap (packetHeaderHeap width n rows roots) rows roots values)
      (graph.evalTable values))[SharedReusableProbe.tableSize width n rows roots + i]? = _
    have cell := value_cell (channelHeap (packetHeaderHeap width n rows roots) rows roots values)
      (graph.evalTable values) (⟨i, valid⟩ : Fin graph.nodeCount)
    have hv : SharedReusableProbe.tableSize width n rows roots + i <
        (withValues (channelHeap (packetHeaderHeap width n rows roots) rows roots values)
          (graph.evalTable values)).size := by
      simp only [SharedReusableProbe.tableSize, withValues_size, channelHeap_size]
      omega
    rw [Array.getElem?_eq_getElem hv]
    simpa only [SharedReusableProbe.tableSize, words, List.getElem_ofFn, channelHeap_size] using congrArg some cell
  obtain ⟨copied, copyPeak, copyTrace, copySpace, copyHeap, copyStack, copyOutput, copyPC, copyRunning, copyHead⟩ :=
    SharedWitnessCopy.execution resident evaluated (SharedReusableProbe.tableSize width n rows roots)
      (words graph values width) (entry + 126) (entry + 136) evalPC evalRunning (by omega)
      tablePositive (by simpa using tableBound) cells (by simpa only [words_length, matched.length_eq] using copyAt)
  obtain ⟨final, reclaimTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      _, _, _, finalFrame⟩ :=
    SharedGraphReclaim.node_table_execution resident copied graph rows roots values (entry + 136) done
      copyPC copyRunning (by omega) (copyHeap.trans evalHeap) (by omega)
      (by simpa only [SharedWitnessCopy.code_size, matched.length_eq, Nat.add_assoc, Nat.reduceAdd] using reclaimAt)
  have evalLive : evaluated.liveWords = state.liveWords + graph.nodeCount := by
    simp only [State.liveWords, evalHeap, evalStack, evalOutput, heapStored, evaluationHeap_size, channelHeap_size]
    omega
  have copyLive : copied.liveWords = state.liveWords + 2 * graph.nodeCount := by
    simp only [State.liveWords, copyHeap, copyStack, copyOutput, words_length, List.length_append,
      evalHeap, evalStack, evalOutput, heapStored, evaluationHeap_size, channelHeap_size]
    omega
  have joined := evalTrace.append (copyTrace.append reclaimTrace)
  refine ⟨final, evalTicks + ((6 * (words graph values width).length + 5) + (4 * graph.nodeCount + 4)),
    max evalPeak (max copyPeak copied.liveWords), joined, ?_, ?_, finalHeap.trans heapStored.symm,
    finalStack.trans (copyStack.trans (by rw [evalStack])), finalOutput.trans (copyOutput.trans evalOutput),
    finalPC, finalRunning, (finalFrame 4 (by decide) (by decide) (by decide)).trans (copyHead.trans (evalFrame 4 (by decide)))⟩
  · simp only [words_length]; omega
  · simp only [words_length] at copySpace
    rw [evalLive] at copySpace
    rw [copyLive]
    omega

end Controller.Cost.SharedTableProbe
