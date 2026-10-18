module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverSeekSibling

@[expose] public section

/-! At cursor zero the resident seek comparison reaches the actual halt
instruction without a prefix query or an output word. -/
namespace Controller.Cost.EnumerationDriverSeekHalt
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.SharedDetectorAssembly
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

theorem execution (previous : Finset (Fin parameters.channels)) (state : State w 8)
    (ready : Ready parameters packet 0 0 (fixedTrue 0 previous) state)
    (position : state.pc = word w (l).seek) :
    ∃ final, Execution program state final 4 state.liveWords ∧ final.halted = true ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output := by
  have whole := EnumerationDriverSeekStep.physical parameters graph retained entry rows roots program context.present
  have headAt := block_left program (l).seek
    (EnumerationDriverSeekStep.headCode w (SharedDetectorPrepared.packetSize graph) (l).halt (l).seekTry)
    (EnumerationDriverSeekStep.tailCode parameters w (SharedDetectorPrepared.packetSize graph) (l).seek (l).seekForced) whole
  have compareAt := block_left program (l).seek (SharedTagCompare.code w (l).halt 0 3).toList
    (EnumerationCounter.code w (2 ^ w - 1) ++ EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph) ++ [.branchZero 1 (word w (l).seekTry)])
    (by simpa only [EnumerationDriverSeekStep.headCode, List.append_assoc] using headAt)
  have room := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 11 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_append, Array.length_toList, SharedTagCompare.code_size, EnumerationCounter.code_length,
    EnumerationDriverCode.readBit, EnumerationMaskWrite.code_length, EnumerationDriverCode.jump, List.length_cons, List.length_nil] at room
  have testRoom : (l).seek + 3 < 2 ^ w := by
    split at room <;> simp only [List.length_nil, Array.length_toList, SharedTagCompare.code_size] at room <;> omega
  obtain ⟨tested, first, heap, stack, output, pc, running, frame⟩ :=
    SharedTagCompare.execution program state (l).seek (l).halt 0 0 3 (by decide) position ready.running testRoom
      (by omega) (by omega) ready.counter
      (by intro phase; simpa only [Array.getElem?_toList] using compareAt phase.val (by simpa using phase.isLt))
  have haltAt := EnumerationDriverLayout.physical parameters graph w entry rows roots program context.present 15 (by decide)
  change SharedRootRead.BlockAt program (l).halt [.halt] at haltAt
  have haltRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 15 (by decide)
  change (l).halt + 1 < 2 ^ w at haltRoom
  obtain ⟨final, second, halted, finalHeap, finalStack, finalOutput⟩ :=
    EnumerationSteps.halt_execution (program := program) tested (l).halt (by simpa using pc) running haltRoom
      (by simpa using haltAt 0 (by simp))
  have testedLive : tested.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  exact ⟨final, by simpa only [testedLive, Nat.max_self, Nat.reduceAdd] using first.append second,
    halted, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output⟩

end
end Controller.Cost.EnumerationDriverSeekHalt
