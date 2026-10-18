module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedHeadControl

@[expose] public section

/-! One constraint word is consumed before a filtered shared candidate probe. -/
namespace Controller.Cost.SharedCandidateStep
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : Program width 8 :=
  SharedCandidateInput.code width entry (entry + 2 * roots.length + 18)
    (SharedReusableProbe.tableSize width n rows roots) roots.length ++
      SharedFilteredProbe.code width n rows roots (entry + 2 * roots.length + 18)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) :
    (code width n rows roots entry).size = 2 * roots.length + 202 := by unfold code; simp

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (channel : Fin n) (excluded : Bool)
    (witnesses suffix : List (Word width)) (entry : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry))
    (room : entry + 2 * roots.length + 202 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (input : state.stack = witnesses ++ boolWord width excluded :: suffix)
    (lengths : witnesses.length = graph.roots.length) (candidateHeld : state.reg 4 = word width channel.val) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧ ticks ≤ 84 * graph.countedSize + 47 ∧
      peak ≤ 8 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧
      final.stack = (if values channel || excluded then witnesses else
        SharedRootAggregate.updated (word width channel.val)
          (graph.roots.map (fun root => (root.val, graph.eval (SharedCandidateProbe.enabled values channel) root))) witnesses) ++ suffix ∧
      final.output = state.output ∧ final.pc = word width (entry + 2 * roots.length + 202) ∧
      final.halted = false ∧ final.reg 4 = word width channel.val := by
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have count : witnesses.length = roots.length := lengths.trans rootCount.symm
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have heapSize : state.heap.size = SharedReusableProbe.tableSize width n rows roots := by
    rw [heapStored, channelHeap_size]; rfl
  have heapFits : state.heap.size + witnesses.length < 2 ^ width := by
    rw [heapStored, channelHeap_size]
    simp only [cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount, lengths]
    omega
  have all := physical
  unfold code at all
  have inputCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have filterCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  obtain ⟨ready, inputPeak, inputTrace, inputSpace, readyHeap, readyStack, readyOutput,
    readyPC, readyRunning, excludedHeld, readyCandidate⟩ :=
    SharedCandidateInput.execution resident state witnesses suffix (boolWord width excluded) entry
      (entry + 2 * roots.length + 18) position running (by omega)
      (by rw [heapStored]; simp [channelHeap_size, cacheHeap_size, packetHeaderHeap_size])
      heapFits input (by simpa only [heapSize, count] using inputCode)
  obtain ⟨final, filterTicks, filterPeak, filterTrace, filterTime, filterSpace, finalHeap,
    finalStack, finalOutput, finalPC, finalRunning, finalCandidate⟩ :=
    SharedFilteredProbe.execution resident ready graph rows roots matched heads rootMatches values channel excluded
      witnesses suffix (entry + 2 * roots.length + 18) capacity
      (by simpa only [SharedCandidateInput.code_size, Nat.add_assoc] using filterCode) (by omega)
      readyPC readyRunning (readyHeap.trans heapStored) readyStack lengths
      (readyCandidate.trans candidateHeld) excludedHeld
  have shorter : ready.stack.length + 1 = state.stack.length := by
    simp only [readyStack, input, List.length_append, List.length_cons]; omega
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
  have joined := inputTrace.append filterTrace
  refine ⟨final, (12 * witnesses.length + 10) + filterTicks, max inputPeak filterPeak, joined,
    by omega, ?_, finalHeap.trans readyHeap, finalStack, finalOutput.trans readyOutput, ?_,
    finalRunning, finalCandidate⟩
  · simp only [readyOutput] at filterSpace
    apply Nat.max_le.mpr
    constructor <;> omega
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC

end Controller.Cost.SharedCandidateStep
