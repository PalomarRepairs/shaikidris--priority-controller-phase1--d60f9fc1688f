module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.DetectionBridge

@[expose] public section

/-!
# Proper-coordinate projections of nonempty qualifier vectors

A local relation receives only the Boolean row on its explicitly supplied
coordinate set. The conjunction obstruction below applies to such relations;
it does not quantify over encodings with a shared existential auxiliary.
-/

namespace Controller.Physical

/-- A qualifier vector is nonzero when at least one channel is eligible. -/
def Nonzero {n : ℕ} (h : Assignment n) : Prop := ∃ i, h i = true

/-- A row indexed only by the coordinates in a supplied scope. -/
abbrev LocalAssignment {n : ℕ} (scope : Finset (Channel n)) :=
  {i : Channel n // i ∈ scope} → Bool

/-- Restrict a global qualifier vector to precisely the supplied coordinates. -/
def projectAssignment {n : ℕ} (scope : Finset (Channel n)) (h : Assignment n) :
    LocalAssignment scope := fun i => h i.val

/-- Extend a local row, setting the chosen outside coordinate to one and all
other outside coordinates to zero. -/
def extendLocal {n : ℕ} (scope : Finset (Channel n)) (row : LocalAssignment scope)
    (outside : Channel n) : Assignment n :=
  fun i => if hi : i ∈ scope then row ⟨i, hi⟩ else decide (i = outside)

/-- The local row is preserved coordinate by coordinate by the extension. -/
theorem projectAssignment_extendLocal {n : ℕ} (scope : Finset (Channel n))
    (row : LocalAssignment scope) (outside : Channel n) :
    projectAssignment scope (extendLocal scope row outside) = row := by
  funext i
  simp [projectAssignment, extendLocal, i.property]

/-- An outside coordinate makes the extension nonzero, for every local row. -/
theorem extendLocal_nonzero {n : ℕ} (scope : Finset (Channel n))
    (row : LocalAssignment scope) (outside : Channel n) (hout : outside ∉ scope) :
    Nonzero (extendLocal scope row outside) := by
  exact ⟨outside, by simp [extendLocal, hout]⟩

/-- Every row on a proper coordinate subset is the projection of a nonzero vector. -/
theorem proper_projection_full {n : ℕ} (scope : Finset (Channel n))
    (hproper : scope ≠ Finset.univ) (row : LocalAssignment scope) :
    ∃ h : Assignment n, Nonzero h ∧ projectAssignment scope h = row := by
  have hexists : ∃ outside : Channel n, outside ∉ scope := by
    by_contra hnone
    apply hproper
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact hnone ⟨i, hi⟩
  obtain ⟨outside, hout⟩ := hexists
  exact ⟨extendLocal scope row outside, extendLocal_nonzero scope row outside hout,
    projectAssignment_extendLocal scope row outside⟩

/-- Any conjunction of proper-scope relations valid on every nonzero vector
also accepts the all-zero vector. The outside witness may depend on the relation. -/
theorem valid_local_relations_accept_zero {n : ℕ} {ι : Type*}
    (scopes : ι → Finset (Channel n)) (proper : ∀ a, scopes a ≠ Finset.univ)
    (relations : (a : ι) → LocalAssignment (scopes a) → Prop)
    (valid : ∀ h : Assignment n, Nonzero h → ∀ a,
      relations a (projectAssignment (scopes a) h)) :
    ∀ a, relations a (projectAssignment (scopes a) (fun _ => false)) := by
  intro a
  obtain ⟨h, hn, hproject⟩ := proper_projection_full (scopes a) (proper a)
    (projectAssignment (scopes a) (fun _ => false))
  have hrelation := valid h hn a
  rwa [hproject] at hrelation

/-- Nonemptiness cannot be characterized by a conjunction of proper-scope
relations without shared existential auxiliary variables. -/
theorem not_nonzero_iff_local_conjunction {n : ℕ} {ι : Type*}
    (scopes : ι → Finset (Channel n)) (proper : ∀ a, scopes a ≠ Finset.univ)
    (relations : (a : ι) → LocalAssignment (scopes a) → Prop) :
    ¬ ∀ h : Assignment n,
      Nonzero h ↔ ∀ a, relations a (projectAssignment (scopes a) h) := by
  intro hiff
  have hzero := valid_local_relations_accept_zero scopes proper relations
    (fun h hn => (hiff h).mp hn)
  have hnonzero := (hiff (fun _ => false)).mpr hzero
  simp [Nonzero] at hnonzero

/-- Observing only the OR of qualifiers never detects a bridge, since every
reachable faulty eligible set and the healthy singleton are nonempty. -/
theorem not_bridgeDetectable_anyTrue {n b : ℕ} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) :
    ¬ BridgeDetectable (b := b) bridge drive (fun _ : Fin 1 => anyTrue) := by
  intro hdetect
  obtain ⟨_, K, hK, k, hneq⟩ :=
    (bridge_detectable_iff bridge hb drive (fun _ : Fin 1 => anyTrue)).mp hdetect
  have hsingleton : anyTrue (assignmentOfSet {bridge.target}) = true :=
    (anyTrue_eq_true _).mpr ⟨bridge.target, by simp⟩
  have hnonempty : anyTrue (assignmentOfSet K) = true := by
    obtain ⟨i, hi⟩ := hK.1
    exact (anyTrue_eq_true _).mpr ⟨i, by simpa using hi⟩
  exact hneq (hsingleton.trans hnonempty.symm)

/-- For at least two buses, proper-scope relations valid on all admissible
eligible sets permit a spurious OR-decoder witness even though physical detection
is impossible. -/
theorem proper_local_relaxation_false_positive {n b : ℕ} {ι : Type*}
    (bridge : Bridge n) (hb : 2 ≤ b)
    (scopes : ι → Finset (Channel n)) (proper : ∀ a, scopes a ≠ Finset.univ)
    (relations : (a : ι) → LocalAssignment (scopes a) → Prop)
    (valid : ∀ K : Finset (Channel n), Admissible b bridge.target K →
      ∀ a, relations a (projectAssignment (scopes a) (assignmentOfSet K))) :
    (¬ BridgeDetectable (b := b) bridge true (fun _ : Fin 1 => anyTrue)) ∧
      ∃ faulty : Assignment n,
        (∀ a, relations a (projectAssignment (scopes a) faulty)) ∧
        ObservationsDiffer (fun _ : Fin 1 => anyTrue)
          (assignmentOfSet {bridge.target}) faulty := by
  have hpositive : 0 < b := by omega
  refine ⟨not_bridgeDetectable_anyTrue bridge hpositive true, (fun _ => false), ?_, ?_⟩
  · apply valid_local_relations_accept_zero scopes proper relations
    intro h hn
    have hK : Admissible b bridge.target (setOfAssignment h) := by
      apply (admissible_many hb bridge.target _).mpr
      obtain ⟨i, hi⟩ := hn
      exact ⟨i, (mem_setOfAssignment h i).mpr hi⟩
    simpa using valid (setOfAssignment h) hK
  · refine ⟨0, ?_⟩
    change anyTrue (assignmentOfSet {bridge.target}) ≠ anyTrue (fun _ : Channel n => false)
    simp [anyTrue]

/-- A shared existential auxiliary can express the two-coordinate OR even
when each clause mentions only one original coordinate. -/
theorem shared_auxiliary_encodes_or (h₀ h₁ : Bool) :
    (∃ a : Bool, (h₀ || a) = true ∧ ((!a) || h₁) = true) ↔ (h₀ || h₁) = true := by
  cases h₀ <;> cases h₁ <;> decide

end Controller.Physical
