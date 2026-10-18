module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Producers

@[expose] public section

/-! Exact producer-trace coverage for order-independent recovery.

These consumers derive selected-producer coverage from the checked run itself.
Candidate completeness remains the explicit promise of the recovery theorem.
-/

namespace Controller.Recognition.IntendedDAG
variable [DecidableEq α]

theorem Run.known_iff (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) (v : α) :
    v ∈ known ↔ v ∈ dag.roots ∨ ∃ p ∈ trace, p.output.1 = v := by
  induction run with
  | start => simp
  | step previous p candidate ready ih =>
    rw [Finset.mem_insert, ih]
    constructor
    · rintro (new | root | ⟨q, member, outputEq⟩)
      · exact Or.inr ⟨p, List.mem_cons_self .., new.symm⟩
      · exact Or.inl root
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ member, outputEq⟩
    · rintro (root | ⟨q, member, outputEq⟩)
      · exact Or.inr (Or.inl root)
      · rcases List.mem_cons.mp member with same | old
        · subst q
          exact Or.inl outputEq.symm
        · exact Or.inr (Or.inr ⟨q, old, outputEq⟩)

theorem Run.trace_candidates (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) :
    ∀ p ∈ trace, p ∈ promise.candidates := by
  induction run with
  | start => simp
  | step _ p member _ ih =>
    intro q selected
    rcases List.mem_cons.mp selected with same | earlier
    · simpa only [same] using member
    · exact ih q earlier

theorem Run.no_root_output (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) :
    ∀ p ∈ trace, p.output.1 ∉ dag.roots := by
  intro p member
  exact promise.no_root p (Run.trace_candidates dag promise run p member)

/-- Every nonroot intended producer actually occurs in the recovered trace. -/
theorem Run.nonroot_selected (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace)
    (saturated : ∀ p ∈ promise.candidates, ¬p.Ready known)
    (v : α) (nonroot : v ∉ dag.roots) : dag.producer v ∈ trace := by
  have knownV := dag.saturated_complete promise run saturated v
  rcases (Run.known_iff dag promise run v).mp knownV with root | ⟨p, member, outputEq⟩
  · exact False.elim (nonroot root)
  · have intended := Run.intended dag promise run p member
    have producerEq : p = dag.producer v := by simpa only [outputEq] using intended
    simpa only [producerEq] using member

/-- Fresh ready steps cannot select one output twice. -/
theorem Run.outputs_nodup (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace) :
    (trace.map (fun p => p.output.1)).Nodup := by
  induction run with
  | start => simp
  | step previous p _ ready ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro member
    obtain ⟨q, selected, same⟩ := List.mem_map.mp member
    have knownOutput : p.output.1 ∈ _ :=
      (Run.known_iff dag promise previous p.output.1).mpr (Or.inr ⟨q, selected, same⟩)
    exact ready.1 knownOutput

/-- Literal producer-recovery conclusion: all and only intended nonroot
producers occur, independently of the sequence of ready choices. -/
theorem recovery_exact (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    {known trace} (run : dag.Run promise known trace)
    (saturated : ∀ p ∈ promise.candidates, ¬p.Ready known) :
    (∀ p ∈ trace, p = dag.producer p.output.1 ∧ p.output.1 ∉ dag.roots) ∧
    (∀ v, v ∉ dag.roots → dag.producer v ∈ trace) ∧
    (trace.map (fun p => p.output.1)).Nodup := by
  refine ⟨?_, ?_, Run.outputs_nodup dag promise run⟩
  · intro p member
    exact ⟨Run.intended dag promise run p member, Run.no_root_output dag promise run p member⟩
  · exact fun v nonroot => Run.nonroot_selected dag promise run saturated v nonroot

end Controller.Recognition.IntendedDAG
