module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Basic.Admissible
public import Controller.Physical.CandidateInvariant
public import Controller.Physical.BridgeCofactors

@[expose] public section

/-!
# Image inclusion for separated drive-one bridge inputs

The faulty selector first keeps the enabled non-target channels. If that seed
is nonempty, a suffix survivor qualifies. If the seed is empty, all suffix flags
are zero and the enabled target qualifies. These are separate cases because
the final qualifier vector can contain a channel absent from the selector seed.
-/

namespace Controller.Physical

/-- Separated drive-one inputs have a zero faulty first flag. -/
theorem separated_drive_one_faultyFirstFlag {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    bridgeFirstFlag bridge input wire = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact changed ((firstFlag_drive_one bridge input h).trans htrue.symm)

/-- The faulty first-mask seed consists precisely of the enabled non-target channels. -/
theorem separated_drive_one_faultySeed {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    nextActive input.enable (input.request input.firstBus) false =
      (fun i => input.enable i && decide (i ≠ bridge.target)) := by
  obtain ⟨ht, hother⟩ := separated_drive_one_pattern bridge input h changed
  funext i
  change (input.enable i && (false ^^ !(firstTerms input i))) = _
  by_cases hi : i = bridge.target
  · subst i
    simp [ht]
  · simp [hother i hi, hi]

/-- Every separated healthy eligible vector is the target singleton, for every suffix. -/
theorem separated_drive_one_healthy {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    healthyQualifiers input = assignmentOfSet {bridge.target} := by
  obtain ⟨ht, hother⟩ := separated_drive_one_pattern bridge input h changed
  apply healthyQualifiers_eq_singleton_of_firstTerms input bridge.target
  change firstTerms input = assignmentOfSet {bridge.target}
  funext i
  by_cases hi : i = bridge.target
  · subst i
    simp [ht, assignmentOfSet]
  · simp [hother i hi, assignmentOfSet, hi]

/-- A zero first flag leaves some qualifier whenever some channel is enabled.
The empty first-mask seed is handled by the all-zero suffix flags. -/
theorem qualifiersFromFirst_false_nonempty {n b : ℕ} (input : PrimaryInput n b)
    (henabled : ∃ i, input.enable i = true) :
    ∃ i, qualifiersFromFirst input false i = true := by
  cases b with
  | zero => exact (Nat.lt_irrefl 0 input.positiveBuses).elim
  | succ b =>
      let seed := nextActive input.enable (input.request 0) false
      let suffix := fun j : Fin b => input.request j.succ
      by_cases hseed : ∃ i, seed i = true
      · have hfinal : ∃ i, (runMasks b seed suffix none).finalActive i = true := by
          rw [(runMasks_refines_candidates b seed suffix).2]
          exact (runCandidates_nonempty_iff b seed suffix).mpr hseed
        obtain ⟨i, hi⟩ := hfinal
        refine ⟨i, ?_⟩
        exact runMasks_finalActive_imp_qualifiers (b + 1) input.enable input.request
          (some false) i hi
      · have hempty : seed = (fun _ => false) := by
          funext i
          apply Bool.eq_false_iff.mpr
          intro hi
          exact hseed ⟨i, hi⟩
        have hflags : (runFromFirst input false).flags = (fun _ => false) := by
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · rfl
          · change (runMasks b seed suffix none).flags k = false
            rw [hempty, (runMasks_refines_candidates b (fun _ => false) suffix).1,
              (runCandidates_empty b suffix).1]
        obtain ⟨i, hi⟩ := henabled
        refine ⟨i, ?_⟩
        unfold qualifiersFromFirst
        rw [hflags]
        simp [qualifiers, hi]

/-- With one bus and zero first flag, qualification is exactly enablement. -/
theorem qualifiersFromFirst_one_false {n : ℕ} (input : PrimaryInput n 1) :
    qualifiersFromFirst input false = input.enable := by
  funext i
  simp [qualifiersFromFirst, qualifiers, runFromFirst, runMasks, Fin.forall_fin_succ]

/-- A separated faulty eligible vector is nonempty, including an empty non-target seed. -/
theorem separated_drive_one_faulty_nonempty {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    ∃ i, bridgeQualifiers bridge input wire i = true := by
  unfold bridgeQualifiers
  rw [separated_drive_one_faultyFirstFlag bridge input h changed]
  apply qualifiersFromFirst_false_nonempty
  exact ⟨bridge.target, (separated_drive_one_target_enabled bridge input h changed).1⟩

/-- The target is faulty-eligible in every separated one-bus input. -/
theorem separated_drive_one_faulty_target_one {n : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n 1) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    bridgeQualifiers bridge input wire bridge.target = true := by
  unfold bridgeQualifiers
  rw [separated_drive_one_faultyFirstFlag bridge input h changed,
    qualifiersFromFirst_one_false]
  exact (separated_drive_one_target_enabled bridge input h changed).1

/-- Every separated faulty eligible set obeys the exact image restriction. -/
theorem separated_drive_one_admissible {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    Admissible b bridge.target (setOfAssignment (bridgeQualifiers bridge input wire)) := by
  constructor
  · obtain ⟨i, hi⟩ := separated_drive_one_faulty_nonempty bridge input h changed
    exact ⟨i, (mem_setOfAssignment _ i).mpr hi⟩
  · intro hb
    subst b
    apply (mem_setOfAssignment _ bridge.target).mpr
    exact separated_drive_one_faulty_target_one bridge input h changed

/-- Universal inclusion in the bridge pair image, without any decoder assumptions. -/
theorem separated_drive_one_image {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    healthyQualifiers input = assignmentOfSet {bridge.target} ∧
      Admissible b bridge.target (setOfAssignment (bridgeQualifiers bridge input wire)) :=
  ⟨separated_drive_one_healthy bridge input h changed,
    separated_drive_one_admissible bridge input h changed⟩

end Controller.Physical
