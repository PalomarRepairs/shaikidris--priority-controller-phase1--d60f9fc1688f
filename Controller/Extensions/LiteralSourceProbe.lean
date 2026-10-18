module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralSourceRun

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Original-source literal propagation with an executed copy and reclamation.
The result column is retained on the caller stack; the source heap is restored. -/
namespace Controller.Extensions.LiteralSourceProbe
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored Controller.Cost.RawTransferLoops
open Controller.Cost.RegisterWiden Controller.Cost.RawAdapterProgram

variable (config : LiteralSourceNode.Mode)

def kernel (width n : Nat) (rows : List Row) (roots : List Nat) : Program width 4 :=
  (LiteralSourceRun.code config width 0 1
    (UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false))).toArray

@[simp] theorem kernel_size (width n : Nat) (rows : List Row) (roots : List Nat) :
    (kernel config width n rows roots).size = 117 := by simp [kernel]

private theorem state_ext (left right : State width registers)
    (reg : left.reg = right.reg) (heap : left.heap = right.heap)
    (stack : left.stack = right.stack) (output : left.output = right.output)
    (pc : left.pc = right.pc) (halted : left.halted = right.halted) : left = right := by
  cases left
  cases right
  simp_all

set_option maxHeartbeats 2000000 in
theorem round_execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (entry : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : ∀ index (valid : index < (widenProgram (kernel config width n rows roots)).size),
      resident[entry + index]? = some (relocatedInstruction entry
        ((widenProgram (kernel config width n rows roots))[index]'valid)))
    (codeFits : entry + 117 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 45 * graph.countedSize + 6 ∧ peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = evaluationHeap (packetHeaderHeap width n rows roots) rows roots values (LiteralSourceRun.evalTable config graph values) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 117) ∧ final.halted = false ∧
      (∀ index : Fin 8, 4 ≤ index.val → final.reg index = state.reg index) := by
  let start : State width 4 := {
    reg := fun index => state.reg ⟨index.val, by omega⟩
    heap := state.heap, stack := state.stack, output := state.output
    pc := word width 0, halted := false }
  have block : BlockAt (kernel config width n rows roots) 0
      (LiteralSourceRun.code config width 0 1
    (UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false))) := by
    intro offset bound
    simp [kernel]
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, output, pc, active⟩ :=
    LiteralSourceRun.from_source config (kernel config width n rows roots) start graph rows roots
      matched heads rootMatches values 0 heapStored rfl rfl (by omega) capacity (by
        simpa only [SharedGraphEvaluation.layout_independent width n rows roots values (fun _ => false)] using block)
  have widened := widen_execution _ _ _ _ _ trace state.reg
  have relocated := relocated_execution resident _ entry physical
    (by simpa [widenProgram] using codeFits) widened
  have startEq : relocatedState entry (widenState start state.reg) = state := by
    apply state_ext
    · funext index
      fin_cases index <;> simp [relocatedState, widenState, start]
    · rfl
    · rfl
    · rfl
    · simpa [relocatedState, widenState, start, word] using position.symm
    · exact running.symm
  rw [startEq] at relocated
  refine ⟨relocatedState entry (widenState final state.reg), ticks, peak + 4,
    relocated, time, ?_, heap, stack, output, ?_, active, ?_⟩
  · have live : start.liveWords + 4 = state.liveWords := by simp [start, State.liveWords]; omega
    omega
  · simp only [relocatedState, widenState, pc, Nat.zero_add,
      show (word width 117).val = 117 from Nat.mod_eq_of_lt (by omega)]
    rw [Nat.add_comm]
  · intro index high
    exact widenState_high final state.reg index high

def words (graph : DAG n) (values : Assignment n) (width : Nat) : List (Word width) :=
  List.ofFn (fun id => boolWord width (LiteralSourceRun.evalTable config graph values id))

@[simp] theorem words_length (graph : DAG n) (values : Assignment n) :
    (words config graph values width).length = graph.nodeCount := by simp [words]

def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  (widenProgram (kernel config width n rows roots)).map (relocatedInstruction entry) ++
    (SharedWitnessCopy.code width (entry + 117) (entry + 127)
      (SharedReusableProbe.tableSize width n rows roots) rows.length ++
      SharedEvaluationReclaim.code width (entry + 127) done rows.length)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code config width n rows roots entry done).size = 134 := by
  simp [code, widenProgram]

set_option maxHeartbeats 400000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code config width n rows roots entry done))
    (room : entry + 134 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 55 * graph.countedSize + 15 ∧ peak ≤ state.liveWords + 2 * graph.nodeCount + 4 ∧
      final.heap = state.heap ∧ final.stack = words config graph values width ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = state.reg 4 := by
  have all := physical
  unfold code at all
  have evalAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  have tailAt' : CodeAt resident (entry + 117)
      (SharedWitnessCopy.code width (entry + 117) (entry + 127)
        (SharedReusableProbe.tableSize width n rows roots) rows.length ++
        SharedEvaluationReclaim.code width (entry + 127) done rows.length) := by
    simpa only [Array.size_map, widenProgram, kernel_size] using tailAt
  have copyAt := RawSharedOrdered.takePrefix resident (entry + 117) _ _ tailAt'
  have reclaimAt := RawSharedOrdered.takeSuffix resident (entry + 117) _ _ tailAt'
  have kernelPhysical : ∀ index (valid : index < (widenProgram (kernel config width n rows roots)).size),
      resident[entry + index]? = some (relocatedInstruction entry
        ((widenProgram (kernel config width n rows roots))[index]'valid)) := by
    intro index valid
    simpa only [Array.getElem?_eq_getElem valid, Array.getElem?_map, Option.map_some] using evalAt ⟨index, by simpa using valid⟩
  obtain ⟨evaluated, evalTicks, evalPeak, evalTrace, evalTime, evalSpace, evalHeap, evalStack,
      evalOutput, evalPC, evalRunning, evalFrame⟩ :=
    round_execution config resident state graph rows roots matched heads rootMatches values entry
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
  have cells : ∀ i (hi : i < (words config graph values width).length),
      evaluated.heap[SharedReusableProbe.tableSize width n rows roots + i]? =
        some (words config graph values width)[i] := by
    intro i hi
    have valid : i < graph.nodeCount := by simpa using hi
    rw [evalHeap]
    change (withValues (channelHeap (packetHeaderHeap width n rows roots) rows roots values)
      (LiteralSourceRun.evalTable config graph values))[SharedReusableProbe.tableSize width n rows roots + i]? = _
    have cell := value_cell (channelHeap (packetHeaderHeap width n rows roots) rows roots values)
      (LiteralSourceRun.evalTable config graph values) (⟨i, valid⟩ : Fin graph.nodeCount)
    have hv : SharedReusableProbe.tableSize width n rows roots + i <
        (withValues (channelHeap (packetHeaderHeap width n rows roots) rows roots values)
          (LiteralSourceRun.evalTable config graph values)).size := by
      simp only [SharedReusableProbe.tableSize, withValues_size, channelHeap_size]
      omega
    rw [Array.getElem?_eq_getElem hv]
    simpa only [SharedReusableProbe.tableSize, words, List.getElem_ofFn, channelHeap_size] using congrArg some cell
  obtain ⟨copied, copyPeak, copyTrace, copySpace, copyHeap, copyStack, copyOutput, copyPC, copyRunning, copyHead⟩ :=
    SharedWitnessCopy.execution resident evaluated (SharedReusableProbe.tableSize width n rows roots)
      (words config graph values width) (entry + 117) (entry + 127) evalPC evalRunning (by omega)
      tablePositive (by simpa using tableBound) cells (by simpa only [words_length, matched.length_eq] using copyAt)
  obtain ⟨final, reclaimTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      _, _, _, finalFrame⟩ :=
    SharedGraphReclaim.setup_execution resident copied (entry + 127) done
      (channelHeap (packetHeaderHeap width n rows roots) rows roots values)
      (words config graph values width) copyPC copyRunning (by omega)
      (by simpa only [words, evaluationHeap, withValues] using copyHeap.trans evalHeap)
      (by simpa only [words_length] using (show graph.nodeCount < 2 ^ width by omega))
      (by simpa only [SharedWitnessCopy.code_size, words_length, matched.length_eq, Nat.add_assoc, Nat.reduceAdd] using reclaimAt)
  have evalLive : evaluated.liveWords = state.liveWords + graph.nodeCount := by
    simp only [State.liveWords, evalHeap, evalStack, evalOutput, heapStored, evaluationHeap_size, channelHeap_size]
    omega
  have copyLive : copied.liveWords = state.liveWords + 2 * graph.nodeCount := by
    simp only [State.liveWords, copyHeap, copyStack, copyOutput, words_length, List.length_append,
      evalHeap, evalStack, evalOutput, heapStored, evaluationHeap_size, channelHeap_size]
    omega
  have joined := evalTrace.append (copyTrace.append reclaimTrace)
  refine ⟨final, evalTicks + ((6 * (words config graph values width).length + 5) + (4 * graph.nodeCount + 4)),
    max evalPeak (max copyPeak copied.liveWords), by simpa only [words_length] using joined,
    ?_, ?_, finalHeap.trans heapStored.symm,
    finalStack.trans (copyStack.trans (by rw [evalStack])), finalOutput.trans (copyOutput.trans evalOutput),
    finalPC, finalRunning, (finalFrame 4 (by decide) (by decide) (by decide)).trans (copyHead.trans (evalFrame 4 (by decide)))⟩
  · simp only [words_length]; omega
  · simp only [words_length] at copySpace
    rw [evalLive] at copySpace
    rw [copyLive]
    omega

end Controller.Extensions.LiteralSourceProbe
