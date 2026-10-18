module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverSeekStep

@[expose] public section

/-! Fetched clearing of a true seek coordinate. The forced one-bus target keeps
its baseline bit; every other true coordinate clears both prefix cells. -/
namespace Controller.Cost.EnumerationDriverSeekSkip
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly
open Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery

section
variable (parameters : Parameters) (graph : DAG parameters.channels)
  (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
  (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
  (context : Context parameters graph retained entry rows roots program)
local notation "w" => EnumerationPrefixOracle.Width parameters graph retained
local notation "l" => EnumerationDriverCode.labels parameters graph w entry
local notation "packet" => EnumerationPrefixOracle.packet parameters w rows roots
include context

private theorem tail_at : SharedRootRead.BlockAt program ((l).seek + 9)
    (EnumerationDriverSeekStep.tailCode parameters w (packet).size (l).seek (l).seekForced) := by
  have whole := EnumerationDriverSeekStep.physical parameters graph retained entry rows roots program context.present
  have tail := block_right program (l).seek
    (EnumerationDriverSeekStep.headCode w (SharedDetectorPrepared.packetSize graph) (l).halt (l).seekTry)
    (EnumerationDriverSeekStep.tailCode parameters w (SharedDetectorPrepared.packetSize graph) (l).seek (l).seekForced) whole
  have size : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches (assignmentOfSet {parameters.bridge.target})
  simpa only [EnumerationDriverSeekStep.headCode_length, ← size] using tail

private theorem tail_room : (l).seek + 9 + (if parameters.buses = 1 then 3 else 0) + 10 < 2 ^ w := by
  have room := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 11 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_append, Array.length_toList, SharedTagCompare.code_size, EnumerationCounter.code_length,
    EnumerationDriverCode.readBit, EnumerationMaskWrite.code_length, EnumerationDriverCode.jump, List.length_cons, List.length_nil] at room
  split at room <;> simp only [List.length_nil, Array.length_toList, SharedTagCompare.code_size] at room <;> split <;> omega

set_option maxHeartbeats 2000000 in
theorem free_entry (previous : Finset (Fin parameters.channels)) (cursor : Nat) (lower : cursor < parameters.channels)
    (member : (⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous)
    (free : ¬(parameters.buses = 1 ∧ parameters.bridge.target.val = cursor))
    (state : State w 8) (ready : Ready parameters packet (cursor + 1) cursor (fixedTrue (cursor + 1) previous) state)
    (position : state.pc = word w ((l).seek + 9)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 13 ∧
      Ready parameters packet cursor cursor (fixedTrue cursor previous) final ∧
      final.pc = word w (l).seek ∧ final.output = state.output := by
  let compare := if parameters.buses = 1 then (SharedTagCompare.code w (l).seekForced parameters.bridge.target.val 3).toList else []
  let clear := EnumerationDriverControl.pairCode w (packet).size ((packet).size + parameters.channels) false false ++ EnumerationDriverCode.jump w (l).seek
  have whole : SharedRootRead.BlockAt program ((l).seek + 9) (compare ++ clear) := by
    simpa only [compare, clear, EnumerationDriverSeekStep.tailCode, EnumerationDriverControl.pairCode, List.append_assoc] using
      tail_at parameters graph retained entry rows roots program context
  have compareAt := block_left program ((l).seek + 9) compare clear whole
  have clearAt := block_right program ((l).seek + 9) compare clear whole
  have compareLength : compare.length = if parameters.buses = 1 then 3 else 0 := by
    dsimp [compare]; split <;> simp [SharedTagCompare.code_size]
  have room := tail_room parameters graph retained entry rows roots program context
  have compared : ∃ tested, Execution program state tested compare.length state.liveWords ∧
      Ready parameters packet (cursor + 1) cursor (fixedTrue (cursor + 1) previous) tested ∧
      tested.pc = word w ((l).seek + 9 + compare.length) ∧ tested.output = state.output := by
    by_cases one : parameters.buses = 1
    · have different : cursor ≠ parameters.bridge.target.val := fun same => free ⟨one, same.symm⟩
      obtain ⟨tested, trace, heap, stack, output, pc, running, frame⟩ :=
        SharedTagCompare.execution program state ((l).seek + 9) (l).seekForced parameters.bridge.target.val cursor 3 (by decide)
          position ready.running (by rw [ite_eq_left one] at room; omega)
          ((parameters.bridge.target.isLt).trans (channels_fit parameters graph retained entry rows roots program context))
          (lower.trans (channels_fit parameters graph retained entry rows roots program context)) ready.counter
          (by intro phase; simpa [compare, one, Array.getElem?_toList] using compareAt phase.val (by simp [compare, one]; exact phase.isLt))
      refine ⟨tested, ?_, ⟨heap.trans ready.heap, (frame 3 (by decide)).trans ready.counter, stack.trans ready.stack, running⟩, ?_, output⟩
      · simpa only [compareLength, ite_eq_left one] using trace
      · simpa only [ite_eq_right different, compareLength, ite_eq_left one] using pc
    · exact ⟨state, by simpa only [compareLength, ite_eq_right one] using Execution.refl (p := program) state,
        ready, by simpa only [compareLength, ite_eq_right one, Nat.add_zero] using position, rfl⟩
  obtain ⟨tested, first, testedReady, testedPC, testedOutput⟩ := compared
  let masks := EnumerationMasks.maskList w parameters.buses parameters.bridge.target (cursor + 1) (fixedTrue (cursor + 1) previous)
  have pairAt := block_left program ((l).seek + 9 + compare.length)
    (EnumerationDriverControl.pairCode w (packet).size ((packet).size + parameters.channels) false false) (EnumerationDriverCode.jump w (l).seek) clearAt
  have jumpAt := block_right program ((l).seek + 9 + compare.length)
    (EnumerationDriverControl.pairCode w (packet).size ((packet).size + parameters.channels) false false) (EnumerationDriverCode.jump w (l).seek) clearAt
  obtain ⟨updated, second, heap, stack, output, pc, running, frame⟩ :=
    EnumerationDriverControl.pair_execution program tested ((l).seek + 9 + compare.length) 0 parameters.channels cursor packet masks false false
      testedPC testedReady.running testedReady.counter
      (by simp only [masks, EnumerationMasks.maskList_length]; omega) (by simp only [masks, EnumerationMasks.maskList_length]; omega)
      testedReady.heap (heap_fits parameters graph retained entry rows roots program context tested (cursor + 1) cursor _ testedReady)
      (by rw [compareLength]; omega) (by simpa only [Nat.add_zero] using pairAt)
  obtain ⟨final, third, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    EnumerationSteps.jump_execution (program := program) updated ((l).seek + 9 + compare.length + 8) (l).seek pc running
      (by rw [compareLength]; omega)
      (by simpa [EnumerationDriverControl.pairCode_length, EnumerationDriverCode.jump] using jumpAt 0 (by simp [EnumerationDriverCode.jump]))
      (by simpa [EnumerationDriverControl.pairCode_length, EnumerationDriverCode.jump] using jumpAt 1 (by simp [EnumerationDriverCode.jump]))
  have flagCell : masks[parameters.channels + cursor]? = some (boolWord w false) := by
    have absent : (⟨cursor, lower⟩ : Fin parameters.channels) ∉ fixedFalse (cursor + 1) (fixedTrue (cursor + 1) previous) := by
      simp [fixedFalse, fixedTrue, member]
    simpa [masks, EnumerationMasks.maskList, absent] using EnumerationMasks.masksOf_getElem?_flag w
      (extensionBase parameters.buses parameters.bridge.target (fixedTrue (cursor + 1) (fixedTrue (cursor + 1) previous)))
      (fixedFalse (cursor + 1) (fixedTrue (cursor + 1) previous)) ⟨cursor, lower⟩
  have unchanged : masks.set (parameters.channels + cursor) (boolWord w false) = masks :=
    EnumerationDriverSeekStep.set_self_of_getElem? masks (parameters.channels + cursor) (boolWord w false) flagCell
  have maskEq : (masks.set cursor (boolWord w false)).set (parameters.channels + cursor) (boolWord w false) =
      EnumerationMasks.maskList w parameters.buses parameters.bridge.target cursor (fixedTrue cursor previous) := by
    rw [set_cells_comm parameters, unchanged]
    exact (EnumerationMasks.seek_skip w parameters.buses parameters.bridge.target cursor previous lower member free).symm
  have testedLive := ready_live_eq parameters packet state tested (cursor + 1) cursor (cursor + 1) cursor _ _ ready testedReady testedOutput
  have updatedLive : updated.liveWords = tested.liveWords := by
    simp only [State.liveWords, heap, testedReady.heap, stack, output, Array.size_append, List.size_toArray, List.length_set, masks]
  refine ⟨final, compare.length + 10, ?_, by rw [compareLength]; split <;> omega,
    ⟨?_, (finalFrame 3 (by decide)).trans ((frame 3 (by decide) (by decide)).trans testedReady.counter),
      finalStack.trans (stack.trans testedReady.stack), finalRunning⟩, finalPC, finalOutput.trans (output.trans testedOutput)⟩
  · simpa only [testedLive, updatedLive, Nat.max_self, Nat.reduceAdd] using first.append (second.append third)
  · rw [finalHeap, heap, Nat.zero_add, maskEq]

set_option maxHeartbeats 2000000 in
theorem forced_entry (previous : Finset (Fin parameters.channels)) (cursor : Nat) (lower : cursor < parameters.channels)
    (one : parameters.buses = 1) (targetEq : parameters.bridge.target.val = cursor)
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ previous)
    (state : State w 8) (ready : Ready parameters packet (cursor + 1) cursor (fixedTrue (cursor + 1) previous) state)
    (position : state.pc = word w ((l).seek + 9)) :
    ∃ final, Execution program state final 9 state.liveWords ∧
      Ready parameters packet cursor cursor (fixedTrue cursor previous) final ∧
      final.pc = word w (l).seek ∧ final.output = state.output := by
  have whole := tail_at parameters graph retained entry rows roots program context
  have compareAt : SharedRootRead.BlockAt program ((l).seek + 9)
      (SharedTagCompare.code w (l).seekForced parameters.bridge.target.val 3).toList := by
    have found := block_left program ((l).seek + 9)
      (SharedTagCompare.code w (l).seekForced parameters.bridge.target.val 3).toList
      (EnumerationMaskWrite.code w (packet).size false ++ EnumerationMaskWrite.code w ((packet).size + parameters.channels) false ++
        EnumerationDriverCode.jump w (l).seek) (by simpa [EnumerationDriverSeekStep.tailCode, one, List.append_assoc] using whole)
    exact found
  have room := tail_room parameters graph retained entry rows roots program context
  rw [ite_eq_left one] at room
  obtain ⟨tested, first, heap, stack, output, pc, running, frame⟩ :=
    SharedTagCompare.execution program state ((l).seek + 9) (l).seekForced parameters.bridge.target.val cursor 3 (by decide)
      position ready.running (by omega)
      ((parameters.bridge.target.isLt).trans (channels_fit parameters graph retained entry rows roots program context))
      (lower.trans (channels_fit parameters graph retained entry rows roots program context)) ready.counter
      (by intro phase; simpa only [Array.getElem?_toList] using compareAt phase.val (by simpa using phase.isLt))
  have testedReady : Ready parameters packet (cursor + 1) cursor (fixedTrue (cursor + 1) previous) tested :=
    ⟨heap.trans ready.heap, (frame 3 (by decide)).trans ready.counter, stack.trans ready.stack, running⟩
  obtain ⟨final, second, finalReady, finalPC, finalOutput⟩ :=
    EnumerationDriverSeekStep.forced_skip_entry parameters graph retained entry rows roots program context previous cursor lower one targetEq forced
      tested testedReady (by simpa only [ite_eq_left targetEq.symm] using pc)
  have testedLive := ready_live_eq parameters packet state tested (cursor + 1) cursor (cursor + 1) cursor _ _ ready testedReady output
  exact ⟨final, by simpa only [testedLive, Nat.max_self, Nat.reduceAdd] using first.append second,
    finalReady, finalPC, finalOutput.trans output⟩

theorem execution (previous : Finset (Fin parameters.channels)) (cursor : Nat) (lower : cursor < parameters.channels)
    (member : (⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous)
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ previous)
    (state : State w 8) (ready : Ready parameters packet (cursor + 1) cursor (fixedTrue (cursor + 1) previous) state)
    (position : state.pc = word w ((l).seek + 9)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 13 ∧
      Ready parameters packet cursor cursor (fixedTrue cursor previous) final ∧
      final.pc = word w (l).seek ∧ final.output = state.output := by
  by_cases fixed : parameters.buses = 1 ∧ parameters.bridge.target.val = cursor
  · obtain ⟨final, trace, finalReady, pc, output⟩ :=
      forced_entry parameters graph retained entry rows roots program context previous cursor lower fixed.1 fixed.2 forced state ready position
    exact ⟨final, 9, trace, by omega, finalReady, pc, output⟩
  · exact free_entry parameters graph retained entry rows roots program context previous cursor lower member fixed state ready position

end
end Controller.Cost.EnumerationDriverSeekSkip
