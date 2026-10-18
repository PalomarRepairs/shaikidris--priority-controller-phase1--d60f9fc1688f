module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverStart

@[expose] public section

/-! Initial allocation, actual initial oracle call, dispatch and completion
execute in the same resident program. The trace includes first-result and
zero-result search. -/
namespace Controller.Cost.EnumerationDriverStartup
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery

section
variable (parameters : Parameters) (graph : DAG parameters.channels)
  (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
  (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
  (context : Context parameters graph retained entry rows roots program)
local notation "w" => EnumerationPrefixOracle.Width parameters graph retained
local notation "l" => EnumerationDriverCode.labels parameters graph w entry
local notation "packet" => EnumerationPrefixOracle.packet parameters w rows roots
include context

set_option maxHeartbeats 2000000 in
theorem execution (drive : parameters.drive = true) (state : State w 8)
    (heapStored : state.heap = packet) (stackEmpty : state.stack = []) (running : state.halted = false)
    (position : state.pc = word w entry) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ parameters.channels * (budget parameters graph + 36) + budget parameters graph + 4 * parameters.channels + 18 ∧
      peak ≤ state.liveWords + 2 * parameters.channels + scratch parameters graph ∧ final.output = state.output ∧
      EnumerationDriverStart.Endpoint parameters packet (l).emit
        (next graph parameters.buses parameters.bridge.target true .initial).output final := by
  have initialAt := EnumerationDriverControlAt.initial parameters graph w entry rows roots program context.present
  rw [drive] at initialAt
  have masksLength : (EnumerationDriverCode.initWords parameters w).length = 2 * parameters.channels :=
    EnumerationPrefixOracle.masks_length parameters w ∅ ∅
  have initialRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 0 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_zero,
    List.length_append, List.length_cons, List.length_nil, EnumerationDriverCode.allocateWords_length,
    EnumerationDriverCode.jump] at initialRoom
  have startEq : (l).start = entry := rfl
  rw [startEq, masksLength] at initialRoom
  have widthPositive : 0 < w := by
    have positive : 0 < parameters.channels := by have := parameters.bridge.target.isLt; omega
    have fits := channels_fit parameters graph retained entry rows roots program context
    by_contra bad
    have zero : w = 0 := by omega
    rw [zero] at fits
    norm_num at fits
    omega
  obtain ⟨allocated, front, allocHeap, allocStack, allocOutput, allocPC, allocRunning, allocCounter, allocMode⟩ :=
    EnumerationDriverInitial.drive_true program state entry (l).call (l).halt (EnumerationDriverCode.initWords parameters w)
      position running widthPositive (by omega) (by rw [heapStored, masksLength]; exact Nat.le_of_lt context.heapFits) initialAt
  have allocatedReady : Ready parameters packet 0 0 ∅ allocated :=
    ⟨by rw [allocHeap, heapStored, EnumerationDriverPrefix.initial_masks], allocCounter, allocStack.trans stackEmpty, allocRunning⟩
  obtain ⟨decided, queryTicks, queryPeak, oracle, queryTime, querySpace, queryReady, queryPC, queryMode, flag, queryOutput⟩ :=
    query_execution parameters graph retained entry rows roots program context 0 0 0 ∅ allocated allocatedReady
      (EnumerationMasks.initial_consistent parameters.buses parameters.bridge.target) allocPC allocMode
  have dispatchRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 3 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_append, Array.length_toList, SharedTagCompare.code_size] at dispatchRoom
  obtain ⟨dispatched, dispatchTicks, dispatchTrace, dispatchTime, dispatchHeap, dispatchStack, dispatchOutput, dispatchPC, dispatchRunning, dispatchFrame⟩ :=
    EnumerationDriverDispatch.execution program decided (l).dispatch (l).initialPost (l).completePost 0 queryPC queryReady.running queryMode
      (by omega) (by omega) (EnumerationDriverDispatch.physical parameters graph w entry rows roots program context.present)
  have dispatchReady : Ready parameters packet 0 0 ∅ dispatched :=
    ⟨dispatchHeap.trans queryReady.heap, (dispatchFrame 3 (by decide)).trans queryReady.counter,
      dispatchStack.trans queryReady.stack, dispatchRunning⟩
  obtain ⟨answered, answerTicks, answerTrace, answerTime, answerHeap, answerStack, answerOutput, continuation⟩ :=
    EnumerationDriverStart.answer_entry parameters graph retained entry rows roots program context
      (query graph parameters.buses parameters.bridge.target true 0 ∅) dispatched dispatchReady
      (by simpa using dispatchPC) ((dispatchFrame 4 (by decide)).trans flag)
  have allocatedLive : allocated.liveWords = state.liveWords + 2 * parameters.channels := by
    simp only [State.liveWords, allocHeap, allocStack, allocOutput, Array.size_append, List.size_toArray, masksLength]; omega
  have decidedLive := ready_live_eq parameters packet allocated decided 0 0 0 0 ∅ ∅ allocatedReady queryReady queryOutput
  have dispatchedLive : dispatched.liveWords = decided.liveWords := by simp only [State.liveWords, dispatchHeap, dispatchStack, dispatchOutput]
  have answeredLive : answered.liveWords = dispatched.liveWords := by simp only [State.liveWords, answerHeap, answerStack, answerOutput]
  have joined := front.append (oracle.append (dispatchTrace.append answerTrace))
  have frontSpace : max (state.liveWords + (EnumerationDriverCode.initWords parameters w).length)
      (max queryPeak (max decided.liveWords dispatched.liveWords)) ≤ state.liveWords + 2 * parameters.channels + scratch parameters graph := by
    rw [allocatedLive] at querySpace
    rw [masksLength, dispatchedLive, decidedLive, allocatedLive]
    simp only [max_le_iff]; omega
  have output := answerOutput.trans (dispatchOutput.trans (queryOutput.trans allocOutput))
  cases feasible : query graph parameters.buses parameters.bridge.target true 0 ∅ with
  | false =>
    refine ⟨answered, _, _, joined, ?_, frontSpace, output, ?_⟩
    · rw [masksLength]; omega
    · simpa only [next, feasible, Bool.false_eq_true, ite_false, EnumerationDriverStart.Endpoint] using continuation
  | true =>
    have entered : Ready parameters packet 0 0 ∅ answered ∧ answered.pc = word w (l).descend := by
      simpa only [feasible, ite_true] using continuation
    obtain ⟨final, completeTicks, completePeak, completeTrace, completeTime, completeSpace, completeReady, completePC, completeOutput⟩ :=
      EnumerationDriverComplete.execution parameters graph retained entry rows roots program context parameters.channels 0 ∅ answered
        (by omega) entered.1 (by intro channel member; simp at member) feasible entered.2
    refine ⟨final, _, _, joined.append completeTrace, ?_, ?_, completeOutput.trans output, ?_⟩
    · rw [masksLength]; omega
    · rw [answeredLive, dispatchedLive, decidedLive, allocatedLive] at completeSpace
      exact max_le frontSpace completeSpace
    · simpa only [next, feasible, ite_true, EnumerationDriverStart.Endpoint] using And.intro completeReady completePC

end
end Controller.Cost.EnumerationDriverStartup
