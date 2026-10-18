module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateSet

@[expose] public section

/-! A runtime candidate is enabled, evaluated and reset while graph storage is reused. -/
namespace Controller.Cost.SharedCandidateProbe
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored Controller.Cost.RawTransferLoops

def enabled (values : Assignment n) (channel : Fin n) : Assignment n :=
  fun index => if index = channel then true else values index

theorem reset_enabled (values : Assignment n) (channel : Fin n) (absent : values channel = false) :
    (fun index => if index = channel then false else enabled values channel index) = values := by
  funext index
  by_cases same : index = channel <;> simp [enabled, same, absent]

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : Program width 8 :=
  let base := (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size
  SharedCandidateSet.code width base true ++
    (SharedReusableProbe.code width n rows roots (entry + 4) (entry + 171) ++
      SharedCandidateSet.code width base false)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) :
    (code width n rows roots entry).size = 175 := by unfold code; simp

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (channel : Fin n)
    (absent : values channel = false) (witnesses suffix : List (Word width)) (entry : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry))
    (room : entry + 175 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (input : state.stack = witnesses ++ suffix) (lengths : witnesses.length = graph.roots.length)
    (candidateHeld : state.reg 4 = word width channel.val) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 72 * graph.countedSize + 30 ∧
      peak ≤ 8 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧
      final.stack = SharedRootAggregate.updated (word width channel.val)
        (graph.roots.map (fun root => (root.val, graph.eval (enabled values channel) root))) witnesses ++ suffix ∧
      final.output = state.output ∧ final.pc = word width (entry + 175) ∧ final.halted = false ∧
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
  have enableCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  have probeCode := RawSharedOrdered.takePrefix resident (entry + 4) _ _ (by simpa using tail)
  have resetCode := RawSharedOrdered.takeSuffix resident (entry + 4) _ _ (by simpa using tail)
  obtain ⟨ready, enableTrace, readyHeap, readyStack, readyOutput, readyPC, readyRunning, readyFrame⟩ :=
    SharedCandidateSet.execution resident state baseHeap values channel true entry position running
      (by omega) tableFits heapStored candidateHeld enableCode
  have readyStored : ready.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (enabled values channel) := readyHeap
  obtain ⟨probed, probeTicks, probePeak, probeTrace, probeTime, probeSpace, probedHeap,
    probedStack, probedOutput, probedPC, probedRunning, probedCandidate⟩ :=
    SharedReusableProbe.execution resident ready graph rows roots matched heads rootMatches (enabled values channel)
      witnesses suffix (word width channel.val) (entry + 4) (entry + 171) capacity probeCode
      (by omega) readyPC readyRunning readyStored (readyStack.trans input) lengths
      ((readyFrame 4 (by decide) (by decide)).trans candidateHeld)
  have probedStored : probed.heap = withValues baseHeap (enabled values channel) := probedHeap.trans readyStored
  obtain ⟨final, resetTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    SharedCandidateSet.execution resident probed baseHeap (enabled values channel) channel false (entry + 171)
      probedPC probedRunning (by omega) tableFits probedStored probedCandidate
      (by simpa [baseHeap, Nat.add_assoc] using resetCode)
  have originalHeap : final.heap = state.heap := by
    rw [reset_enabled values channel absent] at finalHeap
    exact finalHeap.trans heapStored.symm
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, readyHeap, heapStored, channelHeap, withValues_size, readyStack, readyOutput, baseHeap]
  have probedLive : probed.liveWords = state.liveWords := by
    have updatedLength : (SharedRootAggregate.updated (word width channel.val)
      (graph.roots.map (fun root => (root.val, graph.eval (enabled values channel) root))) witnesses).length =
        witnesses.length := by simp [SharedRootAggregate.updated, lengths]
    simp only [State.liveWords, probedHeap, probedStack, probedOutput, readyStack, readyOutput,
      updatedLength, input, List.length_append, readyHeap, heapStored, channelHeap, withValues_size, baseHeap]
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
  have joined := enableTrace.append (probeTrace.append resetTrace)
  refine ⟨final, 4 + (probeTicks + 4), max state.liveWords (max probePeak probed.liveWords), joined,
    by omega, ?_, originalHeap, finalStack.trans probedStack,
    finalOutput.trans (probedOutput.trans readyOutput), ?_, finalRunning, ?_⟩
  · simp only [readyStack, readyOutput] at probeSpace
    rw [probedLive]
    apply Nat.max_le.mpr
    constructor
    · omega
    · apply Nat.max_le.mpr
      constructor <;> omega
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · exact (finalFrame 4 (by decide) (by decide)).trans probedCandidate


theorem enabled_set (T : Finset (Channel n)) (channel : Channel n) :
    enabled (assignmentOfSet T) channel = assignmentOfSet (insert channel T) := by
  funext index
  by_cases same : index = channel <;> simp [enabled, assignmentOfSet, same]

theorem absent_set (T : Finset (Channel n)) (channel : Channel n) (absent : channel ∉ T) :
    assignmentOfSet T channel = false := by simp [assignmentOfSet, absent]

end Controller.Cost.SharedCandidateProbe
