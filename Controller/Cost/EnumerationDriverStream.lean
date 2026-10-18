module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverNext

@[expose] public section

/-! The immutable program streams the exact D08 trace and reaches its finite
exhaustion state. Ghost result lists specify emitted words and are never stored
in the runtime heap or stack. -/
namespace Controller.Cost.EnumerationDriverStream
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery
open Controller.Cost.EnumerationStreamEmit Controller.Cost.EnumerationWorkingTrace
open Controller.Cost.EnumerationDriverNext

/-- Ghost concatenation of canonical chunks in chronological emission order. -/
def words (parameters : Parameters) (width : Nat) (results : List (Finset (Fin parameters.channels))) : List (Word width) :=
  results.flatMap (EnumerationCanonicalEmit.words parameters width)

/-- Separate fetched emission charge for one completed native model. -/
def emitBudget (parameters : Parameters) : Nat := 5 + 4 * EnumerationCanonicalEmit.Coordinates parameters

theorem result_detecting (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (logical : Enumeration.State parameters.channels) (K : Finset (Fin parameters.channels))
    (returned : (next graph parameters.buses parameters.bridge.target parameters.drive logical).output = some K) :
    Detecting graph parameters.buses parameters.bridge.target parameters.drive K := by
  have spec := next_spec graph guarded parameters.buses parameters.bridge.target parameters.drive logical
  rw [returned] at spec
  cases logical with
  | initial => exact spec.1
  | after previous => exact spec.1.1
  | exhausted => simp [next] at returned

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
theorem execution (fuel : Nat) : ∀ (logical : Enumeration.State parameters.channels) (state : State w 8),
    Runtime parameters graph packet entry (l).seek logical state →
    ∃ final ticks peak, WorkingExecution program state final ticks peak ∧
      ticks ≤ fuel * delay parameters graph +
        (trace graph parameters.buses parameters.bridge.target parameters.drive fuel logical).length * emitBudget parameters ∧ peak ≤ space graph ∧
      final.output = (words parameters w (trace graph parameters.buses parameters.bridge.target parameters.drive fuel logical)).reverse ++ state.output ∧
      Runtime parameters graph packet entry (l).seek (finish graph parameters.buses parameters.bridge.target parameters.drive fuel logical) final := by
  induction fuel with
  | zero =>
    intro logical state runtime
    exact ⟨state, 0, workingWords state, WorkingExecution.refl state, by simp,
      runtime_words parameters graph retained entry rows roots program context logical state runtime, by simp [words, trace], runtime⟩
  | succ fuel ih =>
    intro logical state runtime
    obtain ⟨found, searchTicks, searchPeak, searchTrace, searchTime, searchSpace, searchOutput, endpoint⟩ :=
      EnumerationDriverNext.execution parameters graph retained entry rows roots program context logical state runtime
    cases returned : (next graph parameters.buses parameters.bridge.target parameters.drive logical).output with
    | none =>
      have halted : found.halted = true := by simpa only [returned, EnumerationDriverStart.Endpoint] using endpoint
      have foundSpace : workingWords found ≤ space graph := searchTrace.final_le_peak.trans searchSpace
      refine ⟨found, searchTicks, searchPeak, searchTrace, ?_, searchSpace, ?_, ?_⟩
      · simp only [trace, returned, List.length_nil, Nat.zero_mul, Nat.add_zero]
        have generous := Nat.mul_le_mul_right (delay parameters graph) (show 1 ≤ fuel + 1 by omega)
        simp only [Nat.one_mul] at generous
        exact searchTime.trans generous
      · simpa only [trace, returned, words, List.flatMap_nil, List.reverse_nil, List.nil_append] using searchOutput
      · simpa only [finish, returned, Runtime] using And.intro halted foundSpace
    | some K =>
      have foundReady : Ready parameters packet parameters.channels parameters.channels K found ∧ found.pc = word w (l).emit := by
        simpa only [returned, EnumerationDriverStart.Endpoint] using endpoint
      have detects := result_detecting parameters graph context.guarded logical K returned
      have drive : parameters.drive = true := detects.1
      have detectsTrue : Detecting graph parameters.buses parameters.bridge.target true K := by
        simpa only [drive] using detects
      obtain ⟨emitted, emitTicks, emitPeak, emitTrace, emitTime, emitSpace, emitReady, emitPC, emitOutput⟩ :=
        EnumerationDriverWorking.emission parameters graph retained entry rows roots program context K found foundReady.1 detectsTrue foundReady.2
      have emittedRuntime : Runtime parameters graph packet entry (l).seek (.after K) emitted := ⟨emitReady, emitPC, detects⟩
      obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, restOutput, finalRuntime⟩ := ih (.after K) emitted emittedRuntime
      have continuation := next_continuation_some graph parameters.buses parameters.bridge.target parameters.drive logical K returned
      refine ⟨final, searchTicks + (emitTicks + restTicks), _, searchTrace.append (emitTrace.append restTrace), ?_, ?_, ?_, ?_⟩
      · simp only [trace, returned, continuation, List.length_cons, Nat.add_mul, Nat.one_mul]
        change emitTicks ≤ emitBudget parameters at emitTime
        clear * - searchTime emitTime restTime
        omega
      · have emissionBound := emitSpace.trans (searchTrace.final_le_peak.trans searchSpace)
        exact max_le searchSpace (max_le emissionBound restSpace)
      · rw [restOutput, emitOutput, searchOutput]
        simp only [trace, returned, continuation, words, List.flatMap_cons, List.reverse_append, List.append_assoc]
      · simpa only [finish, returned, continuation] using finalRuntime

end
end Controller.Cost.EnumerationDriverStream
