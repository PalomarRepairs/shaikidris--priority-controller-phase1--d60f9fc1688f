module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.SourceLiftEligible
public import Controller.NativeProof.HornTrail

@[expose] public section

/-! Healthy-one semantic premises for native proof construction. The zero
system projection and physical model lift establish inconsistency independently
of resolution proof generation. Selected outputs need not include every root. -/
namespace Controller.NativeProof.Decoder
open Controller

/-- Discrepancy absence on the selected output occurrences only. -/
def NoDiscrepancy (parameters : Native.Parameters)
    (selected : Finset (Fin parameters.decoder.roots.length)) : Prop :=
  ∀ output ∈ selected, ∀ K, Admissible parameters.buses parameters.bridge.target K →
    parameters.observations output (assignmentOfSet K) =
      parameters.observations output (assignmentOfSet {parameters.bridge.target})

/-- A healthy-one zero-system model gives a complete checked native SAT model.
No resolution compiler or native observation-derived lemma is used. -/
theorem healthyOne_model_checked (parameters : Native.Parameters)
    (guarded : parameters.decoder.Guarded) (drive : parameters.drive = true)
    (output : Fin parameters.decoder.roots.length)
    (healthy : parameters.observations output
      (assignmentOfSet {parameters.bridge.target}) = true)
    (model : CNF.Satisfiable (parameters.decoder.zeroSystem parameters.buses
      parameters.bridge.target (parameters.decoder.roots.get output) ∅ ∅)) :
    ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
      Certificate.ModelCheck.check parameters.specificationFormula
        (Native.Lift.named parameters
          (Physical.realizeBridge parameters.bridge parameters.positiveBuses K) true) = true := by
  obtain ⟨K, eligible, _, faulty⟩ :=
    (parameters.decoder.zeroSystem_satisfiable_iff guarded parameters.buses
      parameters.bridge.target (parameters.decoder.roots.get output) ∅ ∅).mp model
  refine ⟨K, eligible, Native.Lift.eligible_checked parameters K eligible drive ?_⟩
  refine ⟨output, ?_⟩
  change parameters.decoder.eval (assignmentOfSet {parameters.bridge.target})
    (parameters.decoder.roots.get output) ≠ parameters.decoder.eval (assignmentOfSet K)
      (parameters.decoder.roots.get output)
  change parameters.decoder.eval (assignmentOfSet {parameters.bridge.target})
    (parameters.decoder.roots.get output) = true at healthy
  rw [healthy, faulty]
  decide

/-- Selected-output discrepancy absence makes every selected healthy-one zero
system inconsistent, including its finite dual-Horn implementation. -/
theorem healthyOne_zeroSystem_unsatisfiable (parameters : Native.Parameters)
    (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output
      (assignmentOfSet {parameters.bridge.target}) = true) :
    CNF.Unsatisfiable (parameters.decoder.zeroSystem parameters.buses
      parameters.bridge.target (parameters.decoder.roots.get output) ∅ ∅) := by
  intro model
  obtain ⟨K, eligible, _, faulty⟩ :=
    (parameters.decoder.zeroSystem_satisfiable_iff guarded parameters.buses
      parameters.bridge.target (parameters.decoder.roots.get output) ∅ ∅).mp model
  have equal := absent output accepted K eligible
  change parameters.decoder.eval (assignmentOfSet K)
    (parameters.decoder.roots.get output) = _ at equal
  rw [faulty, healthy] at equal
  exact Bool.false_ne_true equal

/-- The actual finite worklist reports contradiction; the result follows from
the independent zero-system semantics, rather than a proof producer result. -/
theorem healthyOne_worklist_none (parameters : Native.Parameters)
    (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output
      (assignmentOfSet {parameters.bridge.target}) = true) :
    parameters.decoder.solveZero parameters.buses parameters.bridge.target
      (parameters.decoder.roots.get output) ∅ ∅ = none := by
  apply (parameters.decoder.solveZero_none_iff guarded parameters.buses
    parameters.bridge.target (parameters.decoder.roots.get output) ∅ ∅).mpr
  rintro ⟨K, eligible, fixed, faulty⟩
  exact healthyOne_zeroSystem_unsatisfiable parameters guarded selected absent output
    accepted healthy ((parameters.decoder.zeroSystem_satisfiable_iff guarded parameters.buses
      parameters.bridge.target (parameters.decoder.roots.get output) ∅ ∅).mpr
        ⟨K, eligible, fixed, faulty⟩)

/-- Native UNSAT supplies discrepancy absence through the independent SAT lift. -/
theorem native_unsat_noDiscrepancy (parameters : Native.Parameters)
    (drive : parameters.drive = true)
    (unsat : CNF.Unsatisfiable parameters.specificationFormula)
    (selected : Finset (Fin parameters.decoder.roots.length)) :
    NoDiscrepancy parameters selected := by
  intro output _ K eligible
  by_contra differs
  have checked := Native.Lift.eligible_checked parameters K eligible drive
    ⟨output, Ne.symm differs⟩
  exact unsat ⟨_, (Certificate.ModelCheck.check_iff _ _).mp checked⟩

/-- The original raw source CNF has the same discrepancy-absence consequence.
The premise is UNSAT of that exact formula, not success of a proof producer. -/
theorem source_unsat_noDiscrepancy (parameters : Native.Parameters)
    (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (unsat : CNF.Unsatisfiable (Native.SourceController.formula parameters))
    (selected : Finset (Fin parameters.decoder.roots.length)) :
    NoDiscrepancy parameters selected := by
  intro output _ K eligible
  by_contra differs
  have checked := Native.SourceLift.eligible_checked parameters raw K eligible drive
    ⟨output, Ne.symm differs⟩
  exact unsat ⟨_, (Certificate.ModelCheck.check_iff _ _).mp checked⟩

/-- Native compiler callers obtain a contradictory healthy-one query directly
from the exact raw input CNF and the independent physical SAT model lift. -/
theorem source_unsat_healthyOne_worklist_none (parameters : Native.Parameters)
    (raw : parameters.layout = .raw) (guarded : parameters.decoder.Guarded)
    (drive : parameters.drive = true)
    (unsat : CNF.Unsatisfiable (Native.SourceController.formula parameters))
    (output : Fin parameters.decoder.roots.length)
    (healthy : parameters.observations output
      (assignmentOfSet {parameters.bridge.target}) = true) :
    parameters.decoder.solveZero parameters.buses parameters.bridge.target
      (parameters.decoder.roots.get output) ∅ ∅ = none :=
  healthyOne_worklist_none parameters guarded {output}
    (source_unsat_noDiscrepancy parameters raw drive unsat {output}) output
    (Finset.mem_singleton_self output) healthy

/-- Selected healthy-one queries produce ordinary checked resolution traces
over their finite zero systems, with one inference per declared zero-system
variable. Transport to the native physical/decoder prefix is a separate step. -/
theorem healthyOne_zeroSystem_certificate (parameters : Native.Parameters)
    (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output
      (assignmentOfSet {parameters.bridge.target}) = true) :
    ∃ trace, HornTrail.certificate (parameters.decoder.finiteZeroSystem parameters.buses
        parameters.bridge.target (parameters.decoder.roots.get output) ∅ ∅) = some trace ∧
      Resolution.check (parameters.decoder.finiteZeroSystem parameters.buses
        parameters.bridge.target (parameters.decoder.roots.get output) ∅ ∅) trace = true ∧
      trace.steps.length ≤ parameters.channels + parameters.decoder.nodeCount := by
  apply HornTrail.certificate_complete
  · exact parameters.decoder.finiteZeroSystem_dualHorn guarded _ _ _ _ _
  · apply (CNF.unsatisfiable_relabel_iff parameters.decoder.zeroIndex.injective _).mpr
    exact healthyOne_zeroSystem_unsatisfiable parameters guarded selected absent output accepted healthy

end Controller.NativeProof.Decoder
