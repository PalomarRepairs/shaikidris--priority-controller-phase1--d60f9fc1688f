module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.ExactImage

@[expose] public section

/-!
# Bridge detection through arbitrary Boolean observations

Detection remains defined by the literal controller copies and the bridge
interface. The equivalence below is a theorem about that physical definition;
it places no syntax, monotonicity, or complexity restriction on the observations.
-/

namespace Controller.Physical

/-- The canonical physical witness detects exactly the output difference of its
admissible eligible set from the healthy singleton. -/
theorem realizeBridge_detects_iff {n b q : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (K : Finset (Channel n)) (hK : Admissible b bridge.target K)
    (outputs : Fin q → Assignment n → Bool) :
    BridgeInputDetects bridge true outputs (realizeBridge bridge hb K) true ↔
      ObservationsDiffer outputs (assignmentOfSet {bridge.target}) (assignmentOfSet K) := by
  have hrealize := realizeBridge_spec bridge hb K hK
  unfold BridgeInputDetects
  rw [hrealize.2.2.2.1, hrealize.2.2.2.2]
  exact ⟨fun h => h.2, fun h => ⟨hrealize.1, h⟩⟩

/-- Physical bridge detection is equivalent to an admissible eligible witness,
for every finite family of Boolean functions and every positive bus count. -/
theorem bridge_detectable_iff {n b q : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (outputs : Fin q → Assignment n → Bool) :
    BridgeDetectable (b := b) bridge drive outputs ↔
      drive = true ∧ ∃ K : Finset (Channel n), Admissible b bridge.target K ∧
        ObservationsDiffer outputs (assignmentOfSet {bridge.target}) (assignmentOfSet K) := by
  constructor
  · intro hdetect
    cases drive with
    | false => exact False.elim (not_bridgeDetectable_drive_zero bridge outputs hdetect)
    | true =>
        obtain ⟨input, wire, interface, observations⟩ := hdetect
        have changed : stageFlag input.enable (input.request input.firstBus) ≠
            bridgeFirstFlag bridge input wire := by
          intro heq
          exact no_observation_change_of_firstFlag_eq bridge input wire outputs heq observations
        obtain ⟨hhealthy, hadmissible⟩ := separated_drive_one_image bridge input interface changed
        refine ⟨rfl, setOfAssignment (bridgeQualifiers bridge input wire), hadmissible, ?_⟩
        rw [assignmentOfSet_setOfAssignment, ← hhealthy]
        exact observations
  · rintro ⟨rfl, K, hK, observations⟩
    exact ⟨realizeBridge bridge hb K, true,
      (realizeBridge_detects_iff bridge hb K hK outputs).mpr observations⟩

/-- Corollary 4.2 with an explicit changed observation and the paper's ordering
of faulty and healthy output values. -/
theorem bridge_detectable_iff_exists_output {n b q : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (outputs : Fin q → Assignment n → Bool) :
    BridgeDetectable (b := b) bridge drive outputs ↔
      drive = true ∧ ∃ K : Finset (Channel n), Admissible b bridge.target K ∧
        ∃ k : Fin q, outputs k (assignmentOfSet K) ≠ outputs k (assignmentOfSet {bridge.target}) := by
  rw [bridge_detectable_iff bridge hb]
  constructor
  · rintro ⟨hd, K, hK, k, hneq⟩
    exact ⟨hd, K, hK, k, Ne.symm hneq⟩
  · rintro ⟨hd, K, hK, k, hneq⟩
    exact ⟨hd, K, hK, k, Ne.symm hneq⟩

/-- An empty observation family cannot detect any physical bridge input. -/
theorem not_bridgeDetectable_empty {n b : ℕ} (bridge : Bridge n) (drive : Bool)
    (outputs : Fin 0 → Assignment n → Bool) :
    ¬ BridgeDetectable (b := b) bridge drive outputs := by
  rintro ⟨input, wire, _, observations⟩
  exact not_observationsDiffer_empty outputs _ _ observations

end Controller.Physical
