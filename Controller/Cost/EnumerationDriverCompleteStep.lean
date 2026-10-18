module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverQuery

@[expose] public section

/-! One descent transition in the resident enumeration program. A free channel
uses the actual returning oracle; a forced target advances without a query. -/
namespace Controller.Cost.EnumerationDriverCompleteStep
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.EnumerationDriverPrefix
open Controller.Cost.EnumerationDriverQuery

section
variable (parameters : Parameters) (graph : DAG parameters.channels)
  (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
  (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
  (context : Context parameters graph retained entry rows roots program)
local notation "w" => EnumerationPrefixOracle.Width parameters graph retained
local notation "l" => EnumerationDriverCode.labels parameters graph w entry
local notation "packet" => EnumerationPrefixOracle.packet parameters w rows roots

def child (depth : Nat) (lower : depth < parameters.channels) (partialSet : Finset (Fin parameters.channels)) :=
  if query graph parameters.buses parameters.bridge.target true (depth + 1) partialSet then
    partialSet else insert ⟨depth, lower⟩ partialSet

include context

set_option maxHeartbeats 2000000 in
theorem execution (depth : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State w 8)
    (ready : Ready parameters packet depth depth partialSet state)
    (bounded : Bounded depth partialSet) (lower : depth < parameters.channels)
    (feasible : query graph parameters.buses parameters.bridge.target true depth partialSet = true)
    (position : state.pc = word w (l).descend) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ budget parameters graph + 36 ∧ peak ≤ state.liveWords + scratch parameters graph ∧
      Ready parameters packet (depth + 1) (depth + 1) (child parameters graph depth lower partialSet) final ∧
      final.pc = word w (l).descend ∧ final.output = state.output := by
  have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches (assignmentOfSet {parameters.bridge.target})
  have fits := channels_fit parameters graph retained entry rows roots program context
  have heapFits := heap_fits parameters graph retained entry rows roots program context state depth depth partialSet ready
  have descendAt := EnumerationDriverControlAt.descent parameters graph w entry rows roots program context.present
  rw [← packetSize] at descendAt
  have descentRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 9 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_append, List.length_cons, List.length_nil, Array.length_toList, SharedTagCompare.code_size,
    EnumerationMaskWrite.code_length, EnumerationDriverCode.jump] at descentRoom
  have descentBound : (l).descend + (10 + (if parameters.buses = 1 then 3 else 0)) < 2 ^ w := by
    split at descentRoom <;> simp only [List.length_nil, Array.length_toList, SharedTagCompare.code_size] at descentRoom <;> split <;> omega
  by_cases forced : parameters.buses = 1 ∧ parameters.bridge.target.val = depth
  · have forcedRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 10 (by decide)
    simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
      List.length_append, List.length_cons, List.length_nil, EnumerationCounter.code_length, EnumerationDriverCode.jump] at forcedRoom
    obtain ⟨final, trace, finalReady, pc, output⟩ :=
      EnumerationDriverDescent.forced_entry parameters program state (l).descend (l).emit (l).forcedDescend (l).call (l).descend
        depth packet partialSet ready bounded lower forced.1 forced.2 position fits
        (by simp only [ite_eq_left forced.1] at descentBound; omega) forcedRoom descendAt
        (EnumerationDriverControlAt.forced_descent parameters graph w entry rows roots program context.present)
    have absent : parameters.bridge.target ∉ partialSet := by
      intro member
      have bound := bounded parameters.bridge.target member
      rw [forced.2] at bound
      omega
    have rejected := EnumerationMasks.forced_query_false graph parameters.buses parameters.bridge.target partialSet forced.1 absent
    rw [forced.2] at rejected
    refine ⟨final, 10, state.liveWords, trace, by omega, by omega, ?_, pc, output⟩
    simpa only [child, rejected, Bool.false_eq_true, ite_false] using finalReady
  · obtain ⟨called, front, callReady, callPC, callMode, callOutput⟩ :=
      EnumerationDriverDescent.free_entry parameters program state (l).descend (l).emit (l).forcedDescend (l).call depth
        packet partialSet ready bounded lower forced position fits heapFits
        (by simp only [EnumerationDriverDescent.freeCode, List.length_append, EnumerationDriverDescent.checks_length,
          EnumerationDriverControl.selectCode_length]; omega) descendAt
    have consistent := EnumerationMasks.false_child_consistent graph context.guarded parameters.buses parameters.bridge.target
      depth partialSet lower bounded feasible forced
    obtain ⟨decided, queryTicks, queryPeak, oracle, queryTime, querySpace, queryReady, queryPC, queryMode, flag, queryOutput⟩ :=
      query_execution parameters graph retained entry rows roots program context (depth + 1) depth 1 partialSet called
        callReady consistent callPC callMode
    have dispatchRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 3 (by decide)
    simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
      List.length_append, Array.length_toList, SharedTagCompare.code_size] at dispatchRoom
    have positive : 0 < parameters.channels := by have := parameters.bridge.target.isLt; omega
    obtain ⟨dispatched, dispatchTicks, dispatchTrace, dispatchTime, dispatchHeap, dispatchStack, dispatchOutput,
      dispatchPC, dispatchRunning, dispatchFrame⟩ :=
      EnumerationDriverDispatch.execution program decided (l).dispatch (l).initialPost (l).completePost 1 queryPC queryReady.running queryMode
        (by omega) dispatchRoom (EnumerationDriverDispatch.physical parameters graph w entry rows roots program context.present)
    have dispatchReady : Ready parameters packet (depth + 1) depth partialSet dispatched :=
      ⟨dispatchHeap.trans queryReady.heap, (dispatchFrame 3 (by decide)).trans queryReady.counter,
        dispatchStack.trans queryReady.stack, dispatchRunning⟩
    have answerRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 7 (by decide)
    simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
      List.length_append, List.length_cons, List.length_nil, EnumerationCounter.code_length, EnumerationDriverCode.jump] at answerRoom
    obtain ⟨answered, answerTicks, answerTrace, answerTime, answerReady, answerPC, answerOutput⟩ :=
      EnumerationDriverAnswer.execution parameters program dispatched (l).completePost (l).completeRepair (l).descend depth packet partialSet
        (query graph parameters.buses parameters.bridge.target true (depth + 1) partialSet) dispatchReady
        (by simpa using dispatchPC) ((dispatchFrame 4 (by decide)).trans flag) (by omega) answerRoom
        (EnumerationDriverAnswer.completion_at parameters graph w entry rows roots program context.present)
    have callLive := ready_live_eq parameters packet state called depth depth (depth + 1) depth partialSet partialSet ready callReady callOutput
    have queryLive := ready_live_eq parameters packet called decided (depth + 1) depth (depth + 1) depth partialSet partialSet callReady queryReady queryOutput
    have dispatchLive : dispatched.liveWords = decided.liveWords := by
      simp only [State.liveWords, dispatchHeap, dispatchStack, dispatchOutput]
    have answeredLive := ready_live_eq parameters packet dispatched answered (depth + 1) depth (depth + 1)
      (if query graph parameters.buses parameters.bridge.target true (depth + 1) partialSet then depth + 1 else depth)
      partialSet partialSet dispatchReady answerReady answerOutput
    have joined := front.append (oracle.append (dispatchTrace.append answerTrace))
    have prefixTime : 10 + (if parameters.buses = 1 then 3 else 0) + (queryTicks + (dispatchTicks + answerTicks)) ≤ budget parameters graph + 24 := by
      split <;> omega
    have prefixSpace : max state.liveWords (max queryPeak (max decided.liveWords dispatched.liveWords)) ≤ state.liveWords + scratch parameters graph := by
      rw [callLive] at querySpace
      rw [dispatchLive, queryLive, callLive]
      simp only [max_le_iff]; omega
    have output : answered.output = state.output := answerOutput.trans (dispatchOutput.trans (queryOutput.trans callOutput))
    cases value : query graph parameters.buses parameters.bridge.target true (depth + 1) partialSet with
    | true =>
      refine ⟨answered, _, _, joined, ?_, prefixSpace, ?_, ?_, output⟩
      · omega
      · simpa only [value, child, ite_true] using answerReady
      · simpa only [value, ite_true] using answerPC
    | false =>
      have repairRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 8 (by decide)
      simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
        List.length_append, List.length_cons, List.length_nil, EnumerationCounter.code_length, EnumerationDriverCode.jump,
        EnumerationMaskWrite.code_length] at repairRoom
      have repairAt := EnumerationDriverRepair.physical parameters graph w entry rows roots program context.present
      rw [← packetSize] at repairAt
      have repairReady : Ready parameters packet (depth + 1) depth partialSet answered := by
        simpa only [value, Bool.false_eq_true, ite_false] using answerReady
      obtain ⟨final, repairTrace, finalReady, finalPC, finalOutput⟩ :=
        EnumerationDriverRepair.execution parameters program answered (l).completeRepair (l).descend depth packet partialSet repairReady bounded lower
          (by simpa only [value, Bool.false_eq_true, ite_false] using answerPC) (by omega)
          (heap_fits parameters graph retained entry rows roots program context answered (depth + 1) depth partialSet repairReady)
          repairRoom repairAt
      refine ⟨final, _, _, joined.append repairTrace, ?_, ?_, ?_, finalPC, finalOutput.trans output⟩
      · omega
      · rw [answeredLive, dispatchLive, queryLive, callLive]
        rw [dispatchLive, queryLive, callLive] at prefixSpace
        exact max_le prefixSpace (by omega)
      · simpa only [child, value, Bool.false_eq_true, ite_false] using finalReady

end
end Controller.Cost.EnumerationDriverCompleteStep
