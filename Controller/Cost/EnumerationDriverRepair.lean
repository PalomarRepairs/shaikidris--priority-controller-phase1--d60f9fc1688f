module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverAnswer

@[expose] public section

/-! Completion's rejected false child is repaired to its feasible true sibling
by the two actual mask stores, then the saved depth advances. -/
namespace Controller.Cost.EnumerationDriverRepair
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly
open Controller.Cost.EnumerationDriverPrefix

def code (width base falseBase descend : Nat) : List (Instruction width 8) :=
  EnumerationDriverControl.pairCode width falseBase base false true ++ EnumerationDriverControl.incrementCode width descend

@[simp] theorem code_length : (code width base falseBase descend).length = 12 := rfl

theorem execution (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry descend depth : Nat) (packet : Array (Word width)) (partialSet : Finset (Fin parameters.channels))
    (ready : Ready parameters packet (depth + 1) depth partialSet state) (bounded : Bounded depth partialSet)
    (lower : depth < parameters.channels) (position : state.pc = word width entry)
    (fits : depth + 1 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) (room : entry + 12 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (code width packet.size (packet.size + parameters.channels) descend)) :
    ∃ final, Execution program state final 12 state.liveWords ∧
      Ready parameters packet (depth + 1) (depth + 1) (insert ⟨depth, lower⟩ partialSet) final ∧
      final.pc = word width descend ∧ final.output = state.output := by
  have pairAt := block_left program entry (EnumerationDriverControl.pairCode width (packet.size + parameters.channels) packet.size false true)
    (EnumerationDriverControl.incrementCode width descend) present
  obtain ⟨updated, first, heap, stack, output, pc, running, frame⟩ :=
    EnumerationDriverControl.pair_execution program state entry parameters.channels 0 depth packet
      (EnumerationMasks.maskList width parameters.buses parameters.bridge.target (depth + 1) partialSet) false true position ready.running ready.counter
      (by simp only [EnumerationMasks.maskList_length]; omega) (by simp only [EnumerationMasks.maskList_length]; omega)
      ready.heap heapFits (by omega) (by simpa using pairAt)
  have incAt : SharedRootRead.BlockAt program (entry + 8) (EnumerationDriverControl.incrementCode width descend) := by
    simpa using block_right program entry (EnumerationDriverControl.pairCode width (packet.size + parameters.channels) packet.size false true)
      (EnumerationDriverControl.incrementCode width descend) present
  obtain ⟨final, second, cursor, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    EnumerationDriverControl.increment_execution program updated (entry + 8) depth descend pc running
      ((frame 3 (by decide) (by decide)).trans ready.counter) fits (by omega) incAt
  have updatedSize : updated.heap.size = state.heap.size := by
    simp only [heap, ready.heap, Array.size_append, List.size_toArray, List.length_set]
  have updatedLive : updated.liveWords = state.liveWords := by simp only [State.liveWords, updatedSize, stack, output]
  refine ⟨final, ?_, ⟨?_, cursor, finalStack.trans (stack.trans ready.stack), finalRunning⟩,
    finalPC, finalOutput.trans output⟩
  · simpa only [updatedLive, Nat.max_self, Nat.reduceAdd] using first.append second
  · rw [finalHeap, heap, Nat.zero_add]
    rw [EnumerationMasks.complete_true_child width parameters.buses parameters.bridge.target depth partialSet lower bounded]

/-- The selected true sibling has the exact semantic feasibility used by the
D08 completion recurrence; no second oracle query is assumed or executed. -/
theorem true_child_feasible (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (depth : Nat) (partialSet : Finset (Fin parameters.channels)) (lower : depth < parameters.channels)
    (bounded : Bounded depth partialSet)
    (feasible : query graph parameters.buses parameters.bridge.target true depth partialSet = true)
    (rejected : query graph parameters.buses parameters.bridge.target true (depth + 1) partialSet = false) :
    query graph parameters.buses parameters.bridge.target true (depth + 1) (insert ⟨depth, lower⟩ partialSet) = true :=
  Enumeration.true_child_feasible graph guarded parameters.buses parameters.bridge.target true depth partialSet lower bounded feasible rejected

theorem physical (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (EnumerationDriverCode.code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt program (EnumerationDriverCode.labels parameters graph width entry).completeRepair
      (code width (SharedDetectorPrepared.packetSize graph) (SharedDetectorPrepared.packetSize graph + parameters.channels)
        (EnumerationDriverCode.labels parameters graph width entry).descend) := by
  have found := EnumerationDriverLayout.physical parameters graph width entry rows roots program present 8 (by decide)
  simpa [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, code, EnumerationDriverControl.pairCode,
    EnumerationDriverControl.incrementCode, List.append_assoc] using found

end Controller.Cost.EnumerationDriverRepair
