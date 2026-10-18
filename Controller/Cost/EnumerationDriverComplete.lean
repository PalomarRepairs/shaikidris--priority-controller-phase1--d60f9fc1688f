module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverCompleteStep

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The concrete resident descent reaches the exact D08 greedy completion.
Its entire fetched trace, including every oracle call, has a linear prefix
charge and one uniform scratch bound. -/
namespace Controller.Cost.EnumerationDriverComplete
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
include context

set_option maxHeartbeats 2000000 in
theorem execution (fuel : Nat) : ∀ (depth : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State w 8),
    depth + fuel = parameters.channels → Ready parameters packet depth depth partialSet state →
    Bounded depth partialSet → query graph parameters.buses parameters.bridge.target true depth partialSet = true →
    state.pc = word w (l).descend →
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ fuel * (budget parameters graph + 36) + 3 ∧ peak ≤ state.liveWords + scratch parameters graph ∧
      Ready parameters packet parameters.channels parameters.channels
        (complete graph parameters.buses parameters.bridge.target true depth partialSet fuel).eligible final ∧
      final.pc = word w (l).emit ∧ final.output = state.output := by
  induction fuel with
  | zero =>
    intro depth partialSet state total ready bounded feasible position
    have full : depth = parameters.channels := by omega
    subst depth
    have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
      SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches (assignmentOfSet {parameters.bridge.target})
    have descentAt := EnumerationDriverControlAt.descent parameters graph w entry rows roots program context.present
    rw [← packetSize] at descentAt
    have room := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 9 (by decide)
    simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
      List.length_append, List.length_cons, List.length_nil, Array.length_toList, SharedTagCompare.code_size,
      EnumerationMaskWrite.code_length, EnumerationDriverCode.jump] at room
    have headRoom : (l).descend + 3 < 2 ^ w := by
      split at room <;> simp only [List.length_nil, Array.length_toList, SharedTagCompare.code_size] at room <;> omega
    obtain ⟨final, trace, finalReady, pc, output⟩ := EnumerationDriverDescent.leaf_entry parameters program state
      (l).descend (l).emit (l).forcedDescend (l).call packet partialSet ready position
      (channels_fit parameters graph retained entry rows roots program context) headRoom descentAt
    exact ⟨final, 3, state.liveWords, trace, by simp, by omega, finalReady, pc, output⟩
  | succ fuel ih =>
    intro depth partialSet state total ready bounded feasible position
    have lower : depth < parameters.channels := by omega
    obtain ⟨next, firstTicks, firstPeak, first, firstTime, firstSpace, nextReady, nextPC, firstOutput⟩ :=
      EnumerationDriverCompleteStep.execution parameters graph retained entry rows roots program context
        depth partialSet state ready bounded lower feasible position
    let child := EnumerationDriverCompleteStep.child parameters graph depth lower partialSet
    have nextBounded : Bounded (depth + 1) child := by
      dsimp [child, EnumerationDriverCompleteStep.child]
      split
      · exact fun channel member => (bounded channel member).trans (by omega)
      · exact bounded_insert depth partialSet lower bounded
    have nextFeasible : query graph parameters.buses parameters.bridge.target true (depth + 1) child = true := by
      dsimp [child, EnumerationDriverCompleteStep.child]
      cases answer : query graph parameters.buses parameters.bridge.target true (depth + 1) partialSet with
      | true => simp only [answer, ite_true]
      | false =>
        simpa only [answer, Bool.false_eq_true, ite_false] using
          true_child_feasible graph context.guarded parameters.buses parameters.bridge.target true depth partialSet lower bounded feasible answer
    obtain ⟨final, restTicks, restPeak, rest, restTime, restSpace, finalReady, finalPC, finalOutput⟩ :=
      ih (depth + 1) child next (by omega) nextReady nextBounded nextFeasible nextPC
    have nextLive := ready_live_eq parameters packet state next depth depth (depth + 1) (depth + 1) partialSet child ready nextReady firstOutput
    refine ⟨final, firstTicks + restTicks, max firstPeak restPeak, first.append rest, ?_, ?_, ?_, finalPC, finalOutput.trans firstOutput⟩
    · calc
        firstTicks + restTicks ≤ (budget parameters graph + 36) + (fuel * (budget parameters graph + 36) + 3) := Nat.add_le_add firstTime restTime
        _ = (fuel + 1) * (budget parameters graph + 36) + 3 := by ring
    · rw [nextLive] at restSpace
      exact max_le firstSpace restSpace
    · simpa only [complete, dite_eq_left lower, child, EnumerationDriverCompleteStep.child] using finalReady

/-- The concrete endpoint is detecting and is the least detecting completion
of the supplied feasible prefix. -/
theorem result_spec (depth : Nat) (partialSet : Finset (Fin parameters.channels))
    (lower : depth ≤ parameters.channels) (bounded : Bounded depth partialSet)
    (feasible : query graph parameters.buses parameters.bridge.target true depth partialSet = true) :
    let K := (complete graph parameters.buses parameters.bridge.target true depth partialSet (parameters.channels - depth)).eligible
    Detecting graph parameters.buses parameters.bridge.target true K ∧ Agrees depth partialSet K ∧
      ∀ other, Detecting graph parameters.buses parameters.bridge.target true other → Agrees depth partialSet other →
        K = other ∨ Before K other := by
  have total : depth + (parameters.channels - depth) = parameters.channels := by omega
  exact ⟨(complete_spec graph context.guarded parameters.buses parameters.bridge.target true _ depth partialSet total bounded feasible).1,
    (complete_spec graph context.guarded parameters.buses parameters.bridge.target true _ depth partialSet total bounded feasible).2,
    complete_min graph context.guarded parameters.buses parameters.bridge.target true _ depth partialSet total bounded feasible⟩

end
end Controller.Cost.EnumerationDriverComplete
