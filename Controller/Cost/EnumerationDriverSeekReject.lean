module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverSeekSkip

@[expose] public section

/-! A rejected true sibling clears its baseline cell and resumes the smaller
prefix. The already-cleared false cell needs no further allocation or write. -/
namespace Controller.Cost.EnumerationDriverSeekReject
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

set_option maxHeartbeats 2000000 in
theorem execution (previous : Finset (Fin parameters.channels)) (cursor : Nat) (lower : cursor < parameters.channels)
    (absent : (⟨cursor, lower⟩ : Fin parameters.channels) ∉ previous)
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ previous)
    (state : State w 8)
    (ready : Ready parameters packet (cursor + 1) cursor (insert ⟨cursor, lower⟩ (fixedTrue cursor previous)) state)
    (position : state.pc = word w (l).seekFail) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      Ready parameters packet cursor cursor (fixedTrue cursor previous) final ∧
      final.pc = word w (l).seek ∧ final.output = state.output := by
  have free : ¬(parameters.buses = 1 ∧ parameters.bridge.target.val = cursor) := by
    rintro ⟨one, same⟩
    have channelEq : parameters.bridge.target = ⟨cursor, lower⟩ := Fin.ext same
    exact absent (channelEq ▸ forced one)
  have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches (assignmentOfSet {parameters.bridge.target})
  have wholeAt := EnumerationDriverLayout.physical parameters graph w entry rows roots program context.present 5 (by decide)
  change SharedRootRead.BlockAt program (l).seekFail
    (EnumerationMaskWrite.code w (SharedDetectorPrepared.packetSize graph) false ++ EnumerationDriverCode.jump w (l).seek) at wholeAt
  rw [← packetSize] at wholeAt
  have writeAt := block_left program (l).seekFail (EnumerationMaskWrite.code w (packet).size false) (EnumerationDriverCode.jump w (l).seek) wholeAt
  have jumpAt := block_right program (l).seekFail (EnumerationMaskWrite.code w (packet).size false) (EnumerationDriverCode.jump w (l).seek) wholeAt
  have room := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 5 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_append, EnumerationMaskWrite.code_length, EnumerationDriverCode.jump, List.length_cons, List.length_nil] at room
  let masks := EnumerationMasks.maskList w parameters.buses parameters.bridge.target (cursor + 1) (insert ⟨cursor, lower⟩ (fixedTrue cursor previous))
  obtain ⟨updated, first, heap, stack, output, pc, running, frame⟩ :=
    EnumerationDriverMask.write_execution program state (l).seekFail 0 cursor packet masks false position ready.running ready.counter
      (by simp only [masks, EnumerationMasks.maskList_length]; omega) ready.heap
      (heap_fits parameters graph retained entry rows roots program context state (cursor + 1) cursor _ ready) (by omega)
      (by simpa only [Nat.add_zero] using writeAt)
  obtain ⟨final, second, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    EnumerationSteps.jump_execution (program := program) updated ((l).seekFail + 4) (l).seek pc running (by omega)
      (by simpa [EnumerationDriverCode.jump] using jumpAt 0 (by simp [EnumerationDriverCode.jump]))
      (by simpa [EnumerationDriverCode.jump] using jumpAt 1 (by simp [EnumerationDriverCode.jump]))
  have updatedLive : updated.liveWords = state.liveWords := by
    simp only [State.liveWords, heap, ready.heap, stack, output, Array.size_append, List.size_toArray, List.length_set, masks]
  refine ⟨final, ?_, ⟨?_, (finalFrame 3 (by decide)).trans ((frame 3 (by decide) (by decide)).trans ready.counter),
    finalStack.trans (stack.trans ready.stack), finalRunning⟩, finalPC, finalOutput.trans output⟩
  · simpa only [updatedLive, Nat.max_self, Nat.reduceAdd] using first.append second
  · rw [finalHeap, heap, Nat.zero_add]
    rw [← EnumerationMasks.seek_fail w parameters.buses parameters.bridge.target cursor previous lower absent free]

end
end Controller.Cost.EnumerationDriverSeekReject
