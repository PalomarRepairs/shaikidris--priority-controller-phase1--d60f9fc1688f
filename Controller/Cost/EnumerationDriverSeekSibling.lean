module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverSeekReject

@[expose] public section

/-! A fetched sibling query and its answer-dependent continuation. Success
enters completion with a feasible prefix; rejection resumes smaller seek. -/
namespace Controller.Cost.EnumerationDriverSeekSibling
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
theorem execution (previous : Finset (Fin parameters.channels)) (cursor : Nat) (lower : cursor < parameters.channels)
    (absent : (⟨cursor, lower⟩ : Fin parameters.channels) ∉ previous)
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ previous)
    (state : State w 8) (ready : Ready parameters packet (cursor + 1) cursor (fixedTrue (cursor + 1) previous) state)
    (position : state.pc = word w (l).seekTry) :
    let selected := insert ⟨cursor, lower⟩ (fixedTrue cursor previous)
    let answer := query graph parameters.buses parameters.bridge.target true (cursor + 1) selected
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ budget parameters graph + 28 ∧
      peak ≤ state.liveWords + scratch parameters graph ∧ final.output = state.output ∧
      (if answer then Ready parameters packet (cursor + 1) (cursor + 1) selected final ∧ final.pc = word w (l).descend
       else Ready parameters packet cursor cursor (fixedTrue cursor previous) final ∧ final.pc = word w (l).seek) := by
  dsimp only
  let selected := insert ⟨cursor, lower⟩ (fixedTrue cursor previous)
  let answer := query graph parameters.buses parameters.bridge.target true (cursor + 1) selected
  have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches (assignmentOfSet {parameters.bridge.target})
  have siblingAt := EnumerationDriverControlAt.sibling parameters graph w entry rows roots program context.present
  rw [← packetSize] at siblingAt
  have siblingRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 13 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_append, EnumerationMaskWrite.code_length, EnumerationDriverCode.jump, List.length_cons, List.length_nil] at siblingRoom
  obtain ⟨called, front, callReady, callPC, callMode, callOutput⟩ :=
    EnumerationDriverPrefix.sibling_entry parameters program state (l).seekTry (l).call cursor packet previous lower absent ready position
      (heap_fits parameters graph retained entry rows roots program context state (cursor + 1) cursor _ ready) (by omega) siblingAt
  obtain ⟨decided, queryTicks, queryPeak, oracle, queryTime, querySpace, queryReady, queryPC, queryMode, flag, queryOutput⟩ :=
    query_execution parameters graph retained entry rows roots program context (cursor + 1) cursor 2 selected called callReady
      (EnumerationMasks.sibling_consistent parameters.buses parameters.bridge.target cursor lower previous forced) callPC callMode
  have dispatchRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 3 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_append, Array.length_toList, SharedTagCompare.code_size] at dispatchRoom
  obtain ⟨dispatched, dispatchTicks, dispatchTrace, dispatchTime, dispatchHeap, dispatchStack, dispatchOutput, dispatchPC, dispatchRunning, dispatchFrame⟩ :=
    EnumerationDriverDispatch.execution program decided (l).dispatch (l).initialPost (l).completePost 2 queryPC queryReady.running queryMode
      (by omega) (by omega) (EnumerationDriverDispatch.physical parameters graph w entry rows roots program context.present)
  have dispatchReady : Ready parameters packet (cursor + 1) cursor selected dispatched :=
    ⟨dispatchHeap.trans queryReady.heap, (dispatchFrame 3 (by decide)).trans queryReady.counter,
      dispatchStack.trans queryReady.stack, dispatchRunning⟩
  have answerRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 4 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_append, EnumerationCounter.code_length, EnumerationDriverCode.jump, List.length_cons, List.length_nil] at answerRoom
  obtain ⟨answered, answerTicks, answerTrace, answerTime, answerReady, answerPC, answerOutput⟩ :=
    EnumerationDriverAnswer.execution parameters program dispatched (l).seekPost (l).seekFail (l).descend cursor packet selected answer dispatchReady
      (by simpa [EnumerationDriverCode.labels] using dispatchPC) ((dispatchFrame 4 (by decide)).trans flag)
      (by have := channels_fit parameters graph retained entry rows roots program context; omega) (by omega)
      (EnumerationDriverAnswer.sibling_at parameters graph w entry rows roots program context.present)
  have callLive := ready_live_eq parameters packet state called (cursor + 1) cursor (cursor + 1) cursor _ selected ready callReady callOutput
  have queryLive := ready_live_eq parameters packet called decided (cursor + 1) cursor (cursor + 1) cursor selected selected callReady queryReady queryOutput
  have dispatchLive : dispatched.liveWords = decided.liveWords := by simp only [State.liveWords, dispatchHeap, dispatchStack, dispatchOutput]
  have answeredLive := ready_live_eq parameters packet dispatched answered (cursor + 1) cursor (cursor + 1)
    (if answer then cursor + 1 else cursor) selected selected dispatchReady answerReady answerOutput
  have joined := front.append (oracle.append (dispatchTrace.append answerTrace))
  have joinedSpace : max state.liveWords (max queryPeak (max decided.liveWords dispatched.liveWords)) ≤ state.liveWords + scratch parameters graph := by
    rw [callLive] at querySpace
    rw [dispatchLive, queryLive, callLive]
    simp only [max_le_iff]; omega
  have output := answerOutput.trans (dispatchOutput.trans (queryOutput.trans callOutput))
  cases value : answer with
  | true =>
    dsimp [answer, selected] at value
    exact ⟨answered, _, _, joined, by omega, joinedSpace, output,
      by simpa only [answer, selected, value, ite_true] using And.intro answerReady answerPC⟩
  | false =>
    dsimp [answer, selected] at value
    have rejectedReady : Ready parameters packet (cursor + 1) cursor selected answered := by
      simpa only [answer, selected, value, Bool.false_eq_true, ite_false] using answerReady
    obtain ⟨final, cleanup, finalReady, pc, finalOutput⟩ :=
      EnumerationDriverSeekReject.execution parameters graph retained entry rows roots program context previous cursor lower absent forced answered
        rejectedReady (by simpa only [answer, selected, value, Bool.false_eq_true, ite_false] using answerPC)
    refine ⟨final, _, _, joined.append cleanup, by omega, ?_, finalOutput.trans output, ?_⟩
    · rw [answeredLive, dispatchLive, queryLive, callLive]
      rw [dispatchLive, queryLive, callLive] at joinedSpace
      exact max_le joinedSpace (by omega)
    · simpa only [value, Bool.false_eq_true, ite_false] using And.intro finalReady pc

end
end Controller.Cost.EnumerationDriverSeekSibling
