module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverSeekHalt

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact resident sibling search. Induction on the cursor composes fetched
reads, skips, actual oracle calls, rejected-sibling cleanup and completion. -/
namespace Controller.Cost.EnumerationDriverSeek
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery

/-- Seek returns a completed prefix, or halts with the baseline masks restored. -/
def Endpoint (parameters : Parameters) (packet : Array (Word width)) (emit : Nat)
    (result : Option (Finset (Fin parameters.channels))) (state : State width 8) : Prop :=
  match result with
  | none => state.halted = true ∧ state.heap = packet ++
      (EnumerationMasks.maskList width parameters.buses parameters.bridge.target 0 ∅).toArray ∧ state.stack = []
  | some K => Ready parameters packet parameters.channels parameters.channels K state ∧ state.pc = word width emit

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
theorem execution (previous : Finset (Fin parameters.channels))
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ previous) (cursor : Nat) :
    ∀ state : State w 8, cursor ≤ parameters.channels →
    Ready parameters packet cursor cursor (fixedTrue cursor previous) state → state.pc = word w (l).seek →
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ (cursor + parameters.channels) * (budget parameters graph + 60) + 4 ∧
      peak ≤ state.liveWords + scratch parameters graph ∧ final.output = state.output ∧
      Endpoint parameters packet (l).emit (seek graph parameters.buses parameters.bridge.target true previous cursor).output final := by
  induction cursor with
  | zero =>
    intro state lower ready position
    obtain ⟨final, trace, halted, heap, stack, output⟩ :=
      EnumerationDriverSeekHalt.execution parameters graph retained entry rows roots program context previous state ready position
    have empty : fixedTrue 0 previous = ∅ := by simp [fixedTrue]
    refine ⟨final, 4, state.liveWords, trace, by omega, by omega, output, ?_⟩
    change final.halted = true ∧ final.heap = packet ++ (EnumerationMasks.maskList w parameters.buses parameters.bridge.target 0 ∅).toArray ∧ final.stack = []
    exact ⟨halted, heap.trans (by simpa only [empty] using ready.heap), stack.trans ready.stack⟩
  | succ cursor ih =>
    intro state bound ready position
    have lower : cursor < parameters.channels := by omega
    obtain ⟨observed, readTrace, observedReady, observedBit, observedPC, readOutput⟩ :=
      EnumerationDriverSeekStep.read_entry parameters graph retained entry rows roots program context previous cursor lower forced state ready position
    have observedLive := ready_live_eq parameters packet state observed (cursor + 1) (cursor + 1) (cursor + 1) cursor _ _ ready observedReady readOutput
    let B := budget parameters graph + 60
    have totalEq : (cursor + 1 + parameters.channels) * B + 4 = (cursor + parameters.channels) * B + B + 4 := by ring
    by_cases member : (⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous
    · obtain ⟨next, skipTicks, skipTrace, skipTime, nextReady, nextPC, skipOutput⟩ :=
        EnumerationDriverSeekSkip.execution parameters graph retained entry rows roots program context previous cursor lower member forced observed
          observedReady (by simpa only [ite_eq_left member] using observedPC)
      obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, restOutput, endpoint⟩ := ih next (by omega) nextReady nextPC
      have nextLive := ready_live_eq parameters packet observed next (cursor + 1) cursor cursor cursor _ _ observedReady nextReady skipOutput
      refine ⟨final, 9 + (skipTicks + restTicks), _, readTrace.append (skipTrace.append restTrace), ?_, ?_,
        restOutput.trans (skipOutput.trans readOutput), ?_⟩
      · change _ ≤ (cursor + 1 + parameters.channels) * B + 4
        rw [totalEq]; dsimp [B] at *; omega
      · rw [nextLive, observedLive] at restSpace
        rw [observedLive]
        exact max_le (by omega) (max_le (by omega) restSpace)
      · simpa only [seek, dite_eq_left lower, ite_eq_left member] using endpoint
    · obtain ⟨answered, siblingTicks, siblingPeak, siblingTrace, siblingTime, siblingSpace, siblingOutput, continuation⟩ :=
        EnumerationDriverSeekSibling.execution parameters graph retained entry rows roots program context previous cursor lower member forced observed
          observedReady (by simpa only [ite_eq_right member] using observedPC)
      let selected := insert ⟨cursor, lower⟩ (fixedTrue cursor previous)
      cases answer : query graph parameters.buses parameters.bridge.target true (cursor + 1) selected with
      | false =>
        dsimp [selected] at answer
        have rejected : Ready parameters packet cursor cursor (fixedTrue cursor previous) answered ∧ answered.pc = word w (l).seek := by
          simpa only [answer, Bool.false_eq_true, ite_false] using continuation
        obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, restOutput, endpoint⟩ := ih answered (by omega) rejected.1 rejected.2
        have answeredLive := ready_live_eq parameters packet observed answered (cursor + 1) cursor cursor cursor _ _ observedReady rejected.1 siblingOutput
        refine ⟨final, 9 + (siblingTicks + restTicks), _, readTrace.append (siblingTrace.append restTrace), ?_, ?_,
          restOutput.trans (siblingOutput.trans readOutput), ?_⟩
        · change _ ≤ (cursor + 1 + parameters.channels) * B + 4
          rw [totalEq]; dsimp [B] at *; omega
        · rw [observedLive] at siblingSpace
          rw [answeredLive, observedLive] at restSpace
          exact max_le (by omega) (max_le siblingSpace restSpace)
        · simpa only [seek, dite_eq_left lower, ite_eq_right member, selected, answer, Bool.false_eq_true, ite_false] using endpoint
      | true =>
        dsimp [selected] at answer
        have accepted : Ready parameters packet (cursor + 1) (cursor + 1) selected answered ∧ answered.pc = word w (l).descend := by
          simpa only [selected, answer, ite_true] using continuation
        have prefixBounded : Bounded cursor (fixedTrue cursor previous) := by
          intro channel inPrefix; exact (Finset.mem_filter.mp inPrefix).2
        obtain ⟨final, completeTicks, completePeak, completeTrace, completeTime, completeSpace, completeReady, completePC, completeOutput⟩ :=
          EnumerationDriverComplete.execution parameters graph retained entry rows roots program context (parameters.channels - (cursor + 1))
            (cursor + 1) selected answered (by omega) accepted.1 (bounded_insert cursor _ lower prefixBounded) answer accepted.2
        have answeredLive := ready_live_eq parameters packet observed answered (cursor + 1) cursor (cursor + 1) (cursor + 1) _ selected observedReady accepted.1 siblingOutput
        refine ⟨final, 9 + (siblingTicks + completeTicks), _, readTrace.append (siblingTrace.append completeTrace), ?_, ?_,
          completeOutput.trans (siblingOutput.trans readOutput), ?_⟩
        · have charge : (parameters.channels - (cursor + 1)) * (budget parameters graph + 36) ≤ parameters.channels * B :=
            Nat.mul_le_mul (by omega) (by dsimp [B]; omega)
          have generous : parameters.channels * B + B ≤ (cursor + 1 + parameters.channels) * B := by
            have inequality := Nat.mul_le_mul_right B (show parameters.channels + 1 ≤ cursor + 1 + parameters.channels by omega)
            simpa only [Nat.add_mul, Nat.one_mul] using inequality
          change _ ≤ (cursor + 1 + parameters.channels) * B + 4
          dsimp [B] at charge generous ⊢; omega
        · rw [observedLive] at siblingSpace
          rw [answeredLive, observedLive] at completeSpace
          exact max_le (by omega) (max_le siblingSpace completeSpace)
        · have endpoint : Endpoint parameters packet (l).emit
              (some (complete graph parameters.buses parameters.bridge.target true (cursor + 1) selected (parameters.channels - (cursor + 1))).eligible) final :=
            ⟨completeReady, completePC⟩
          simpa only [seek, dite_eq_left lower, ite_eq_right member, selected,
            answer, ite_true] using endpoint

end
end Controller.Cost.EnumerationDriverSeek
