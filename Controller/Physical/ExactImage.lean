module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.ImageInclusion
public import Controller.Physical.Realize

@[expose] public section

/-! # Exact pair image of separated drive-one bridge inputs -/

namespace Controller.Physical

/-- The pair image is stated over actual interface-satisfying primary inputs.
Every Boolean faulty vector is permitted exactly when its true coordinates
form an admissible set, while the healthy vector must be the target singleton. -/
theorem separated_drive_one_pair_image_iff {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (healthy faulty : Assignment n) :
    (∃ input : PrimaryInput n b, ∃ wire : Bool,
      BridgeInterfaceSatisfied bridge input true wire ∧
      stageFlag input.enable (input.request input.firstBus) ≠ bridgeFirstFlag bridge input wire ∧
      healthyQualifiers input = healthy ∧ bridgeQualifiers bridge input wire = faulty) ↔
      healthy = assignmentOfSet {bridge.target} ∧
        Admissible b bridge.target (setOfAssignment faulty) := by
  constructor
  · rintro ⟨input, wire, interface, changed, hh, hf⟩
    obtain ⟨hhealthy, hadmissible⟩ := separated_drive_one_image bridge input interface changed
    exact ⟨hh.symm.trans hhealthy, by simpa [hf] using hadmissible⟩
  · rintro ⟨hhealthy, hadmissible⟩
    let K := setOfAssignment faulty
    let input := realizeBridge bridge hb K
    have hrealize := realizeBridge_spec bridge hb K hadmissible
    refine ⟨input, true, hrealize.1, ?_, ?_, ?_⟩
    · change stageFlag (realizeBridge bridge hb K).enable
        ((realizeBridge bridge hb K).request (realizeBridge bridge hb K).firstBus) ≠ _
      rw [firstFlag_drive_one bridge _ hrealize.1, realizeBridge_faultyFirstFlag]
      decide
    · exact (realizeBridge_healthy bridge hb K).trans hhealthy.symm
    · exact hrealize.2.2.2.2.trans (assignmentOfSet_setOfAssignment faulty)

/-- The same pair-image theorem in finite-set coordinates. -/
theorem separated_drive_one_set_pair_image_iff {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (H K : Finset (Channel n)) :
    (∃ input : PrimaryInput n b, ∃ wire : Bool,
      BridgeInterfaceSatisfied bridge input true wire ∧
      stageFlag input.enable (input.request input.firstBus) ≠ bridgeFirstFlag bridge input wire ∧
      healthyQualifiers input = assignmentOfSet H ∧
      bridgeQualifiers bridge input wire = assignmentOfSet K) ↔
      H = {bridge.target} ∧ Admissible b bridge.target K := by
  rw [separated_drive_one_pair_image_iff bridge hb, setOfAssignment_assignmentOfSet]
  constructor
  · rintro ⟨hh, hk⟩
    have hsets := congrArg setOfAssignment hh
    exact ⟨by simpa using hsets, hk⟩
  · rintro ⟨rfl, hk⟩
    exact ⟨rfl, hk⟩

end Controller.Physical
