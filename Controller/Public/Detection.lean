module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.DetectCorrect
public import Controller.Physical.GlobalProjection
public import Controller.Physical.StuckAtImage

@[expose] public section

/-!
# Physical detection and the guarded-decoder decision procedure

The public statements connect literal controller inputs to their exact eligible
sets and to the executable detector on a supplied guarded DAG. Output indices
refer to the original root list, including repeated observations. The stuck-at
classification concerns only the specified active-low qualifier occurrence.

These statements establish semantic correctness and witness construction. Their
types contain no runtime bound or claim of recognition from a native encoding.
-/

namespace Controller.Public

open Physical

/-- Theorem 4.1: the complete pair image of separated drive-one inputs. -/
theorem bridge_image_iff {n b : Nat} (bridge : Bridge n) (hb : 0 < b)
    (H K : Finset (Channel n)) :
    (∃ input : PrimaryInput n b, ∃ wire : Bool,
      BridgeInterfaceSatisfied bridge input true wire ∧
      stageFlag input.enable (input.request input.firstBus) ≠ bridgeFirstFlag bridge input wire ∧
      healthyQualifiers input = assignmentOfSet H ∧
      bridgeQualifiers bridge input wire = assignmentOfSet K) ↔
      H = {bridge.target} ∧ Admissible b bridge.target K :=
  separated_drive_one_set_pair_image_iff bridge hb H K

/-- Corollary 4.2 for any finite family of Boolean observations. -/
theorem bridge_detection_iff {n b q : Nat} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (outputs : Fin q → Assignment n → Bool) :
    BridgeDetectable (b := b) bridge drive outputs ↔
      drive = true ∧ ∃ K : Finset (Channel n), Admissible b bridge.target K ∧
        ∃ observation, outputs observation (assignmentOfSet K) ≠
          outputs observation (assignmentOfSet {bridge.target}) :=
  bridge_detectable_iff_exists_output bridge hb drive outputs

/-- Lemma 4.3: every proper-coordinate row has a nonzero extension. -/
theorem nonzero_projection_full {n : Nat} (scope : Finset (Channel n))
    (proper : scope ≠ Finset.univ) (row : LocalAssignment scope) :
    ∃ h : Assignment n, Nonzero h ∧ projectAssignment scope h = row :=
  proper_projection_full scope proper row

/-- Proper-scope relations valid on all nonzero vectors also admit zero.
Each relation receives only its own coordinate row. -/
theorem local_relations_accept_zero {n : Nat} {ι : Type*}
    (scopes : ι → Finset (Channel n)) (proper : ∀ a, scopes a ≠ Finset.univ)
    (relations : (a : ι) → LocalAssignment (scopes a) → Prop)
    (valid : ∀ h : Assignment n, Nonzero h → ∀ a,
      relations a (projectAssignment (scopes a) h)) :
    ∀ a, relations a (projectAssignment (scopes a) (fun _ => false)) :=
  valid_local_relations_accept_zero scopes proper relations valid

/-- Theorem 4.4, including the one-channel exclusion. The bus index itself
certifies that the controller has at least one bus. -/
theorem qualifier_stuck_detection_iff {n b : Nat} (distinguished target : Channel n)
    (bus : Fin b) (stuck : Bool) :
    StuckDetectable distinguished target bus stuck ↔
      2 ≤ n ∧ (stuck = true ∨ target = distinguished) :=
  stuck_detectable_iff distinguished target bus stuck

/-- The semantic and witness-construction part of Theorem 5.1, stated directly
over actual controller copies. `none` excludes every interface-satisfying
primary input, and every returned input changes a listed observation. -/
theorem guarded_bridge_detector_correct {n b : Nat} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (graph : Decoder.DAG n) (guarded : graph.Guarded) :
    (detectInput bridge hb drive graph = none ↔
      ¬ ∃ input : PrimaryInput n b, ∃ wire : Bool,
        BridgeInterfaceSatisfied bridge input drive wire ∧
          ∃ observation : Fin graph.roots.length,
            graph.eval (healthyQualifiers input) (graph.roots.get observation) ≠
              graph.eval (bridgeQualifiers bridge input wire) (graph.roots.get observation)) ∧
    (∀ input : PrimaryInput n b, detectInput bridge hb drive graph = some input →
      BridgeInterfaceSatisfied bridge input drive true ∧
        ∃ observation : Fin graph.roots.length,
          graph.eval (healthyQualifiers input) (graph.roots.get observation) ≠
            graph.eval (bridgeQualifiers bridge input true) (graph.roots.get observation)) := by
  constructor
  · simpa only [BridgeDetectable, BridgeInputDetects, ObservationsDiffer,
      Decoder.DAG.observations] using detectInput_none_iff bridge hb drive graph guarded
  · intro input returned
    simpa only [BridgeInputDetects, ObservationsDiffer, Decoder.DAG.observations] using
      detectInput_some bridge hb drive graph guarded input returned

/-- The executable returns a primary input exactly when a physical detecting
test exists. In the returned test the bridge wire is true. -/
theorem guarded_bridge_detector_complete {n b : Nat} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (graph : Decoder.DAG n) (guarded : graph.Guarded) :
    (∃ input, detectInput bridge hb drive graph = some input) ↔
      BridgeDetectable (b := b) bridge drive graph.observations := by
  constructor
  · rintro ⟨input, returned⟩
    exact ⟨input, true, detectInput_some bridge hb drive graph guarded input returned⟩
  · intro detectable
    cases result : detectInput bridge hb drive graph with
    | none => exact False.elim ((detectInput_none_iff bridge hb drive graph guarded).mp result
        detectable)
    | some input => exact ⟨input, rfl⟩

/-- Drive zero exits without an eligible-set or primary-input witness. -/
@[simp] theorem guarded_bridge_detector_drive_zero {n b : Nat}
    (bridge : Bridge n) (hb : 0 < b) (graph : Decoder.DAG n) :
    detectInput bridge hb false graph = none := by
  simp [detectInput]

/-- An empty observation list cannot produce a detecting primary input. -/
theorem guarded_bridge_detector_no_observations {n b : Nat}
    (bridge : Bridge n) (hb : 0 < b) (drive : Bool) (graph : Decoder.DAG n)
    (empty : graph.roots = []) : detectInput bridge hb drive graph = none := by
  simp [detectInput, graph.detectSet_no_roots b bridge.target drive empty]

end Controller.Public
