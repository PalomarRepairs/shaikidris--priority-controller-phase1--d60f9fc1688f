module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverEmit
public import Controller.Cost.EnumerationSafeEmit

@[expose] public section

/-! Pointwise working-space refinement of the fetched completion and resident
canonical emission. Accumulated output has no effect on either bound. -/
namespace Controller.Cost.EnumerationDriverWorking
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.SharedDetectorAssembly
open Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery
open Controller.Cost.EnumerationStreamEmit Controller.Cost.EnumerationWorkingTrace

section
variable (parameters : Parameters) (graph : DAG parameters.channels)
  (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
  (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
  (context : Context parameters graph retained entry rows roots program)
local notation "w" => EnumerationPrefixOracle.Width parameters graph retained
local notation "l" => EnumerationDriverCode.labels parameters graph w entry
local notation "packet" => EnumerationPrefixOracle.packet parameters w rows roots
include context

theorem ready_working_bound (depth cursor : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State w 8)
    (ready : Ready parameters packet depth cursor partialSet state) :
    workingWords state ≤ 6 * graph.countedSize + 14 := by
  have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches (assignmentOfSet {parameters.bridge.target})
  have size := graph.countedSize_eq
  simp only [workingWords, ready.heap, ready.stack, Array.size_append, List.size_toArray,
    EnumerationMasks.maskList_length, List.length_nil, Nat.add_zero, packetSize,
    SharedDetectorPrepared.packetSize, SharedDetectorPrepared.maskBase, SharedDetectorPrepared.rootBase]
  omega

theorem completion (depth : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State w 8)
    (lower : depth ≤ parameters.channels) (ready : Ready parameters packet depth depth partialSet state)
    (bounded : Bounded depth partialSet)
    (feasible : query graph parameters.buses parameters.bridge.target true depth partialSet = true)
    (position : state.pc = word w (l).descend) :
    let K := (complete graph parameters.buses parameters.bridge.target true depth partialSet (parameters.channels - depth)).eligible
    ∃ final ticks peak, WorkingExecution program state final ticks peak ∧
      ticks ≤ (parameters.channels - depth) * (budget parameters graph + 36) + 3 ∧
      peak ≤ workingWords state + scratch parameters graph ∧
      Ready parameters packet parameters.channels parameters.channels K final ∧
      final.pc = word w (l).emit ∧ final.output = state.output := by
  obtain ⟨final, ticks, peak, trace, time, space, finalReady, pc, output⟩ :=
    EnumerationDriverComplete.execution parameters graph retained entry rows roots program context (parameters.channels - depth)
      depth partialSet state (by omega) ready bounded feasible position
  obtain ⟨workingPeak, workingTrace, bound⟩ := quiet_bound trace output space
  exact ⟨final, ticks, workingPeak, workingTrace, time, bound, finalReady, pc, output⟩

set_option maxHeartbeats 2000000 in
theorem emission (K : Finset (Fin parameters.channels)) (state : State w 8)
    (ready : Ready parameters packet parameters.channels parameters.channels K state)
    (detects : Detecting graph parameters.buses parameters.bridge.target true K)
    (position : state.pc = word w (l).emit) :
    ∃ final ticks peak, WorkingExecution program state final ticks peak ∧
      ticks ≤ 5 + 4 * EnumerationCanonicalEmit.Coordinates parameters ∧ peak ≤ workingWords state ∧
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
  obtain ⟨emitted, emitTicks, emitPeak, emitTrace, emitSpace, emitTime, heap, stack, output, pc, running, frame⟩ :=
    EnumerationSafeEmit.execution parameters program state (l).emit (packet).size K
      (EnumerationDriverEmit.stored parameters packet K state ready detects.2.1.2) position ready.running positive (by omega)
      (heap_fits parameters graph retained entry rows roots program context state parameters.channels parameters.channels K ready)
      (by simp only [ready.heap, Array.size_append, List.size_toArray, EnumerationMasks.maskList_length]; omega) emitterAt
  obtain ⟨final, jumpTrace, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    EnumerationSteps.jump_execution (program := program) emitted ((l).emit + (EnumerationCanonicalEmit.code parameters w (l).emit (packet).size).length)
      (l).seek pc running (by omega)
      (by simpa [EnumerationDriverCode.jump] using jumpAt 0 (by simp [EnumerationDriverCode.jump]))
      (by simpa [EnumerationDriverCode.jump] using jumpAt 1 (by simp [EnumerationDriverCode.jump]))
  obtain ⟨jumpPeak, jumpWorking, jumpSpace⟩ := quiet_bound (extra := 0) jumpTrace finalOutput (by omega)
  have emittedWorking : workingWords emitted = workingWords state := by simp only [workingWords, heap, stack]
  refine ⟨final, emitTicks + 2, max emitPeak jumpPeak, emitTrace.append jumpWorking, by omega, ?_,
    ⟨finalHeap.trans (heap.trans ready.heap), (finalFrame 3 (by decide)).trans ((frame 3 (by decide) (by decide) (by decide) (by decide)).trans ready.counter),
      finalStack.trans (stack.trans ready.stack), finalRunning⟩, finalPC, finalOutput.trans output⟩
  rw [emittedWorking, Nat.add_zero] at jumpSpace
  exact max_le emitSpace jumpSpace

theorem completion_emission (depth : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State w 8)
    (lower : depth ≤ parameters.channels) (ready : Ready parameters packet depth depth partialSet state)
    (bounded : Bounded depth partialSet)
    (feasible : query graph parameters.buses parameters.bridge.target true depth partialSet = true)
    (position : state.pc = word w (l).descend) :
    let K := (complete graph parameters.buses parameters.bridge.target true depth partialSet (parameters.channels - depth)).eligible
    ∃ final ticks peak, WorkingExecution program state final ticks peak ∧
      ticks ≤ (parameters.channels - depth) * (budget parameters graph + 36) + 8 + 4 * EnumerationCanonicalEmit.Coordinates parameters ∧
      peak ≤ workingWords state + scratch parameters graph ∧
      Ready parameters packet parameters.channels parameters.channels K final ∧ final.pc = word w (l).seek ∧
      final.output = (EnumerationCanonicalEmit.words parameters w K).reverse ++ state.output := by
  dsimp only
  obtain ⟨completed, completeTicks, completePeak, completeTrace, completeTime, completeSpace, completeReady, completePC, completeOutput⟩ :=
    completion parameters graph retained entry rows roots program context depth partialSet state lower ready bounded feasible position
  have spec := EnumerationDriverComplete.result_spec parameters graph retained entry rows roots program context depth partialSet lower bounded feasible
  obtain ⟨final, emitTicks, emitPeak, emitTrace, emitTime, emitSpace, finalReady, finalPC, finalOutput⟩ :=
    emission parameters graph retained entry rows roots program context _ completed completeReady spec.1 completePC
  have completedWorking : workingWords completed = workingWords state := by
    simp only [workingWords, completeReady.heap, ready.heap, completeReady.stack, ready.stack,
      Array.size_append, List.size_toArray, EnumerationMasks.maskList_length]
  refine ⟨final, completeTicks + emitTicks, _, completeTrace.append emitTrace, by omega, ?_, finalReady, finalPC, ?_⟩
  · rw [completedWorking] at emitSpace
    exact max_le completeSpace (by omega)
  · rw [finalOutput, completeOutput]

theorem completion_emission_graph_bound (depth : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State w 8)
    (lower : depth ≤ parameters.channels) (ready : Ready parameters packet depth depth partialSet state)
    (bounded : Bounded depth partialSet)
    (feasible : query graph parameters.buses parameters.bridge.target true depth partialSet = true)
    (position : state.pc = word w (l).descend) :
    let K := (complete graph parameters.buses parameters.bridge.target true depth partialSet (parameters.channels - depth)).eligible
    ∃ final ticks peak, WorkingExecution program state final ticks peak ∧
      ticks ≤ (parameters.channels - depth) * (budget parameters graph + 36) + 8 + 4 * EnumerationCanonicalEmit.Coordinates parameters ∧
      peak ≤ 258 * (graph.countedSize + 1) ∧
      Ready parameters packet parameters.channels parameters.channels K final ∧ final.pc = word w (l).seek ∧
      final.output = (EnumerationCanonicalEmit.words parameters w K).reverse ++ state.output := by
  obtain ⟨final, ticks, peak, trace, time, space, finalReady, pc, output⟩ :=
    completion_emission parameters graph retained entry rows roots program context depth partialSet state lower ready bounded feasible position
  have initial := ready_working_bound parameters graph retained entry rows roots program context depth depth partialSet state ready
  exact ⟨final, ticks, peak, trace, time, by dsimp [scratch] at space; omega, finalReady, pc, output⟩

end
end Controller.Cost.EnumerationDriverWorking
