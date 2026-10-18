module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.Faults

@[expose] public section

/-! Bridge cofactors and congruence of the unchanged selector suffix. -/
namespace Controller.Physical

theorem all_firstTerms_false_iff {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) :
    (∀ i, firstTerms input i = false) ↔
      firstTerms input bridge.target = false ∧
      (∀ i ∈ bridge.drivers, firstTerms input i = false) ∧
      (∀ i ∈ bridge.remaining, firstTerms input i = false) := by
  constructor
  · intro h
    exact ⟨h _, fun i _ => h i, fun i _ => h i⟩
  · rintro ⟨ht, hd, hr⟩ i
    by_cases hit : i = bridge.target
    · simpa [hit] using ht
    · by_cases hid : i ∈ bridge.drivers
      · exact hd i hid
      · exact hr i ((bridge.mem_remaining i).mpr ⟨hit, hid⟩)

theorem firstFlag_eq_cofactor {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) :
    stageFlag input.enable (input.request input.firstBus) =
      !(bridgeU bridge input && bridgeD bridge input && bridgeR bridge input) := by
  have hall := all_firstTerms_false_iff bridge input
  have hc : (bridgeU bridge input && bridgeD bridge input && bridgeR bridge input) = true ↔
      ∀ i, firstTerms input i = false := by
    rw [hall]
    simp [bridgeU, bridgeD, bridgeR, and_assoc]
  have hp : stageFlag input.enable (input.request input.firstBus) = false ↔
      ∀ i, firstTerms input i = false := by
    simp [stageFlag, anyTrue, firstTerms, stageTerms]
  have heq : (bridgeU bridge input && bridgeD bridge input && bridgeR bridge input) =
      !(stageFlag input.enable (input.request input.firstBus)) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.not_eq_true'] using hc.trans hp.symm
  rw [heq]
  simp

theorem bridgeFirstFlag_drive_zero {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input false wire) :
    bridgeFirstFlag bridge input wire = true := by
  simp [BridgeInterfaceSatisfied] at h
  simp [bridgeFirstFlag, h.2.2]

theorem firstFlag_drive_zero {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input false wire) :
    stageFlag input.enable (input.request input.firstBus) = true := by
  rw [firstFlag_eq_cofactor bridge input]
  simp [BridgeInterfaceSatisfied] at h
  simp [h.2.1]

theorem bridgeFirstFlag_drive_one {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire) :
    bridgeFirstFlag bridge input wire = !(bridgeR bridge input) := by
  simp [BridgeInterfaceSatisfied] at h
  simp [bridgeFirstFlag, h.2.1, h.2.2]

theorem firstFlag_drive_one {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire) :
    stageFlag input.enable (input.request input.firstBus) = true := by
  rw [firstFlag_eq_cofactor bridge input]
  simp [BridgeInterfaceSatisfied] at h
  simp [h.1]

/-- The complete literal suffix is a function of the supplied first flag. -/
theorem runFromFirst_congr {n b : ℕ} (input : PrimaryInput n b) {p q : Bool}
    (h : p = q) : runFromFirst input p = runFromFirst input q := by rw [h]

theorem qualifiersFromFirst_congr {n b : ℕ} (input : PrimaryInput n b) {p q : Bool}
    (h : p = q) : qualifiersFromFirst input p = qualifiersFromFirst input q := by rw [h]

theorem healthyRun_eq_runFromFirst {n b : ℕ} (input : PrimaryInput n b) :
    healthyRun input = runFromFirst input
      (stageFlag input.enable (input.request input.firstBus)) := by
  cases b with
  | zero => exact False.elim (Nat.not_lt_zero _ input.positiveBuses)
  | succ b => rfl

theorem bridgeQualifiers_eq_of_firstFlag_eq {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) (wire : Bool)
    (h : stageFlag input.enable (input.request input.firstBus) =
      bridgeFirstFlag bridge input wire) :
    healthyQualifiers input = bridgeQualifiers bridge input wire := by
  unfold healthyQualifiers bridgeQualifiers qualifiersFromFirst
  rw [healthyRun_eq_runFromFirst input, h]

theorem bridgeQualifiers_drive_zero {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input false wire) :
    healthyQualifiers input = bridgeQualifiers bridge input wire := by
  apply bridgeQualifiers_eq_of_firstFlag_eq
  exact (firstFlag_drive_zero bridge input h).trans
    (bridgeFirstFlag_drive_zero bridge input h).symm

theorem no_observation_change_of_firstFlag_eq {n b q : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) (wire : Bool) (outputs : Fin q → Assignment n → Bool)
    (h : stageFlag input.enable (input.request input.firstBus) =
      bridgeFirstFlag bridge input wire) :
    ¬ ObservationsDiffer outputs (healthyQualifiers input) (bridgeQualifiers bridge input wire) := by
  rw [bridgeQualifiers_eq_of_firstFlag_eq bridge input wire h]
  simp [ObservationsDiffer]

theorem not_bridgeDetectable_drive_zero {n b q : ℕ} (bridge : Bridge n)
    (outputs : Fin q → Assignment n → Bool) :
    ¬ BridgeDetectable (b := b) bridge false outputs := by
  rintro ⟨input, wire, interface, k, changed⟩
  rw [bridgeQualifiers_drive_zero bridge input interface] at changed
  exact changed rfl

theorem separated_drive_one_pattern {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    firstTerms input bridge.target = true ∧
      ∀ i, i ≠ bridge.target → firstTerms input i = false := by
  have ht : firstTerms input bridge.target = true := by
    simpa [BridgeInterfaceSatisfied, bridgeU] using h.1
  have hd : ∀ i ∈ bridge.drivers, firstTerms input i = false := by
    simpa [bridgeD] using h.2.1
  have hr : bridgeR bridge input = true := by
    rw [firstFlag_drive_one bridge input h, bridgeFirstFlag_drive_one bridge input h] at changed
    cases hv : bridgeR bridge input <;> simp_all
  have hrem : ∀ i ∈ bridge.remaining, firstTerms input i = false := by
    simpa [bridgeR] using hr
  refine ⟨ht, ?_⟩
  intro i hit
  by_cases hid : i ∈ bridge.drivers
  · exact hd i hid
  · exact hrem i ((bridge.mem_remaining i).mpr ⟨hit, hid⟩)

theorem separated_drive_one_target_enabled {n b : ℕ} (bridge : Bridge n)
    (input : PrimaryInput n b) {wire : Bool}
    (h : BridgeInterfaceSatisfied bridge input true wire)
    (changed : stageFlag input.enable (input.request input.firstBus) ≠
      bridgeFirstFlag bridge input wire) :
    input.enable bridge.target = true ∧ input.request input.firstBus bridge.target = true := by
  simpa [firstTerms, stageTerms] using (separated_drive_one_pattern bridge input h changed).1

end Controller.Physical
