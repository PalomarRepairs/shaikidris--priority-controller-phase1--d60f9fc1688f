module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateFilter

@[expose] public section

/-! Disallowed heads skip the probe; allowed heads use the shared retained graph. -/
namespace Controller.Cost.SharedFilteredProbe
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored Controller.Cost.RawTransferLoops

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : Program width 8 :=
  SharedCandidateFilter.code width entry (entry + 184)
    (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size ++
      SharedCandidateProbe.code width n rows roots (entry + 9)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) :
    (code width n rows roots entry).size = 184 := by unfold code; simp

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (channel : Fin n) (excluded : Bool)
    (witnesses suffix : List (Word width)) (entry : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry)) (room : entry + 184 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (input : state.stack = witnesses ++ suffix) (lengths : witnesses.length = graph.roots.length)
    (candidateHeld : state.reg 4 = word width channel.val) (excludedHeld : state.reg 2 = boolWord width excluded) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧ ticks ≤ 72 * graph.countedSize + 37 ∧
      peak ≤ 8 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧
      final.stack = (if values channel || excluded then witnesses else
        SharedRootAggregate.updated (word width channel.val)
          (graph.roots.map (fun root => (root.val, graph.eval (SharedCandidateProbe.enabled values channel) root))) witnesses) ++ suffix ∧
      final.output = state.output ∧ final.pc = word width (entry + 184) ∧ final.halted = false ∧
      final.reg 4 = word width channel.val := by
  let baseHeap := cacheHeap width (packetHeaderHeap width n rows roots) rows roots
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have tableFits : baseHeap.size + n < 2 ^ width := by
    simp only [baseHeap, cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount]
    omega
  have all := physical
  unfold code at all
  have filterCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have probeCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  obtain ⟨filtered, filterTicks, filterTrace, filterTime, fh, fs, fo, fp, fr, ff⟩ :=
    SharedCandidateFilter.execution resident state baseHeap values channel excluded entry (entry + 184)
      position running (by omega) tableFits (by omega) heapStored candidateHeld excludedHeld filterCode
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
  cases guard : values channel || excluded with
  | true =>
    refine ⟨filtered, filterTicks, state.liveWords, filterTrace, by omega, by omega, fh, ?_, fo,
      ?_, fr, (ff 4 (by decide) (by decide)).trans candidateHeld⟩
    · simpa only [guard, ite_true] using fs.trans input
    · simpa only [guard, ite_true] using fp
  | false =>
    have absent : values channel = false := (Bool.or_eq_false_iff.mp guard).1
    obtain ⟨final, probeTicks, probePeak, probeTrace, probeTime, probeSpace, finalHeap, finalStack,
      finalOutput, finalPC, finalRunning, finalCandidate⟩ :=
      SharedCandidateProbe.execution resident filtered graph rows roots matched heads rootMatches values channel
        absent witnesses suffix (entry + 9) capacity
        (by simpa only [SharedCandidateFilter.code_size] using probeCode) (by omega)
        (by simpa only [guard, Bool.false_eq_true, ite_false] using fp) fr (fh.trans heapStored)
        (fs.trans input) lengths ((ff 4 (by decide) (by decide)).trans candidateHeld)
    have joined := filterTrace.append probeTrace
    refine ⟨final, filterTicks + probeTicks, max state.liveWords probePeak, joined, by omega,
      ?_, finalHeap.trans fh, ?_, finalOutput.trans fo, ?_, finalRunning, finalCandidate⟩
    · simp only [fs, fo] at probeSpace
      apply Nat.max_le.mpr
      constructor <;> omega
    · simpa only [guard, Bool.false_eq_true, ite_false] using finalStack
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC

end Controller.Cost.SharedFilteredProbe
