module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverComplete

@[expose] public section

/-! A full detecting prefix emits its canonical native input from the actual
resident emission block, then returns to the resident sibling search. -/
namespace Controller.Cost.EnumerationDriverEmit
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.SharedDetectorAssembly
open Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery

theorem stored (parameters : Parameters) (packet : Array (Word width)) (K : Finset (Fin parameters.channels))
    (state : State width 8) (ready : Ready parameters packet parameters.channels parameters.channels K state)
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ K) :
    EnumerationCanonicalCoordinates.Stored parameters state.heap packet.size K := by
  intro channel
  rw [ready.heap]
  have cell := EnumerationMasks.result_baseline width parameters.buses parameters.bridge.target K forced channel
  simpa only [Array.getElem?_append_right (by omega : packet.size ≤ packet.size + channel.val), Nat.add_sub_cancel_left,
    List.getElem?_toArray] using cell

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
theorem execution (K : Finset (Fin parameters.channels)) (state : State w 8)
    (ready : Ready parameters packet parameters.channels parameters.channels K state)
    (detects : Detecting graph parameters.buses parameters.bridge.target true K)
    (position : state.pc = word w (l).emit) :
    ∃ final ticks, Execution program state final ticks (state.liveWords + EnumerationCanonicalEmit.Coordinates parameters) ∧
      ticks ≤ 5 + 4 * EnumerationCanonicalEmit.Coordinates parameters ∧
      Ready parameters packet parameters.channels parameters.channels K final ∧
      final.pc = word w (l).seek ∧
      final.output = (EnumerationCanonicalEmit.words parameters w K).reverse ++ state.output := by
  have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches (assignmentOfSet {parameters.bridge.target})
  have wholeAt := EnumerationDriverLayout.physical parameters graph w entry rows roots program context.present 14 (by decide)
  change SharedRootRead.BlockAt program (l).emit
    (EnumerationCanonicalEmit.code parameters w (l).emit (SharedDetectorPrepared.packetSize graph) ++ EnumerationDriverCode.jump w (l).seek) at wholeAt
  rw [← packetSize] at wholeAt
  have emitterAt := block_left program (l).emit (EnumerationCanonicalEmit.code parameters w (l).emit (packet).size)
    (EnumerationDriverCode.jump w (l).seek) wholeAt
  have jumpAt := block_right program (l).emit (EnumerationCanonicalEmit.code parameters w (l).emit (packet).size)
    (EnumerationDriverCode.jump w (l).seek) wholeAt
  have room := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 14 (by decide)
  change (l).emit + (EnumerationCanonicalEmit.code parameters w (l).emit (SharedDetectorPrepared.packetSize graph) ++
    EnumerationDriverCode.jump w (l).seek).length < 2 ^ w at room
  rw [← packetSize] at room
  simp only [List.length_append, EnumerationDriverCode.jump, List.length_cons, List.length_nil] at room
  have positive : 0 < w := by
    have fits := channels_fit parameters graph retained entry rows roots program context
    have channelPositive : 0 < parameters.channels := by have := parameters.bridge.target.isLt; omega
    by_contra zero; have widthZero : w = 0 := by omega
    rw [widthZero] at fits; norm_num at fits; omega
  obtain ⟨emitted, emitTicks, emitTrace, emitTime, heap, stack, output, pc, running, working, frame⟩ :=
    EnumerationCanonicalEmit.execution parameters program state (l).emit (packet).size K
      (stored parameters packet K state ready detects.2.1.2) position ready.running positive (by omega)
      (heap_fits parameters graph retained entry rows roots program context state parameters.channels parameters.channels K ready)
      (by simp only [ready.heap, Array.size_append, List.size_toArray, EnumerationMasks.maskList_length]; omega) emitterAt
  obtain ⟨final, jumpTrace, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    EnumerationSteps.jump_execution (program := program) emitted ((l).emit + (EnumerationCanonicalEmit.code parameters w (l).emit (packet).size).length)
      (l).seek pc running (by omega)
      (by simpa [EnumerationDriverCode.jump] using jumpAt 0 (by simp [EnumerationDriverCode.jump]))
      (by simpa [EnumerationDriverCode.jump] using jumpAt 1 (by simp [EnumerationDriverCode.jump]))
  have emitLive : emitted.liveWords = state.liveWords + EnumerationCanonicalEmit.Coordinates parameters := by
    simp only [State.liveWords, heap, stack, output, List.length_append, List.length_reverse, EnumerationCanonicalEmit.words_length]
    omega
  refine ⟨final, emitTicks + 2, ?_, by omega,
    ⟨finalHeap.trans (heap.trans ready.heap), (finalFrame 3 (by decide)).trans ((frame 3 (by decide) (by decide) (by decide) (by decide)).trans ready.counter),
      finalStack.trans (stack.trans ready.stack), finalRunning⟩, finalPC, finalOutput.trans output⟩
  simpa only [emitLive, Nat.max_self] using emitTrace.append jumpTrace

set_option maxHeartbeats 2000000 in
theorem completion_emission (depth : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State w 8)
    (lower : depth ≤ parameters.channels) (ready : Ready parameters packet depth depth partialSet state)
    (bounded : Bounded depth partialSet)
    (feasible : query graph parameters.buses parameters.bridge.target true depth partialSet = true)
    (position : state.pc = word w (l).descend) :
    let K := (complete graph parameters.buses parameters.bridge.target true depth partialSet (parameters.channels - depth)).eligible
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ (parameters.channels - depth) * (budget parameters graph + 36) + 8 + 4 * EnumerationCanonicalEmit.Coordinates parameters ∧
      peak ≤ state.liveWords + scratch parameters graph + EnumerationCanonicalEmit.Coordinates parameters ∧
      Ready parameters packet parameters.channels parameters.channels K final ∧ final.pc = word w (l).seek ∧
      final.output = (EnumerationCanonicalEmit.words parameters w K).reverse ++ state.output := by
  dsimp only
  obtain ⟨completed, completeTicks, completePeak, completeTrace, completeTime, completeSpace, completeReady, completePC, completeOutput⟩ :=
    EnumerationDriverComplete.execution parameters graph retained entry rows roots program context (parameters.channels - depth)
      depth partialSet state (by omega) ready bounded feasible position
  have spec := EnumerationDriverComplete.result_spec parameters graph retained entry rows roots program context depth partialSet lower bounded feasible
  obtain ⟨final, emitTicks, emitTrace, emitTime, finalReady, finalPC, finalOutput⟩ :=
    execution parameters graph retained entry rows roots program context _ completed completeReady spec.1 completePC
  have completedLive := ready_live_eq parameters packet state completed depth depth parameters.channels parameters.channels
    partialSet _ ready completeReady completeOutput
  refine ⟨final, completeTicks + emitTicks, _, completeTrace.append emitTrace, by omega, ?_, finalReady, finalPC, ?_⟩
  · rw [completedLive]
    exact max_le (by omega) (by omega)
  · rw [finalOutput, completeOutput]

end
end Controller.Cost.EnumerationDriverEmit
