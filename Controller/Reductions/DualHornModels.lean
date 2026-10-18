module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Reductions.DualHornDecoder

@[expose] public section

/-!
# Source assignments and eligible detecting sets

All declared source variables participate in the bijection, including variables
absent from the clauses. A set contains the target and helper and precisely the
source channels assigned true. This is a correspondence of eligible sets,
not a count of all physical input assignments.
-/
namespace Controller.Reductions.DualHorn

open Controller.CNF Controller.Decoder

@[simp] theorem sourceChannel_injective : Function.Injective (@sourceChannel n) := by
  intro a b equality
  apply Fin.ext
  exact congrArg (fun c : Channel (n + 2) => c.val) equality

theorem source_ne_target (i : Fin n) : sourceChannel i ≠ targetChannel n := by
  intro same
  have equal := congrArg Fin.val same
  simp only [sourceChannel, targetChannel] at equal
  omega

theorem source_ne_helper (i : Fin n) : sourceChannel i ≠ helperChannel n := by
  intro same
  have equal := congrArg Fin.val same
  simp only [sourceChannel, helperChannel] at equal
  omega

theorem helper_ne_target : helperChannel n ≠ targetChannel n := by
  intro same
  have equal := congrArg Fin.val same
  simp only [helperChannel, targetChannel] at equal
  omega

/-- The canonical eligible set for a source assignment. -/
def modelSet (values : Fin n → Bool) : Finset (Channel (n + 2)) :=
  insert (targetChannel n) (insert (helperChannel n)
    ((Finset.univ.filter fun i => values i = true).image sourceChannel))

@[simp] theorem modelSet_target (values : Fin n → Bool) : targetChannel n ∈ modelSet values := by
  simp [modelSet]

@[simp] theorem modelSet_helper (values : Fin n → Bool) : helperChannel n ∈ modelSet values := by
  simp [modelSet]

@[simp] theorem modelSet_variable (values : Fin n → Bool) (i : Fin n) :
    sourceChannel i ∈ modelSet values ↔ values i = true := by
  simp [modelSet, source_ne_target, source_ne_helper, sourceChannel_injective.eq_iff]

/-- Read all declared source coordinates from an eligible set. -/
def sourceValues (K : Finset (Channel (n + 2))) : Fin n → Bool :=
  fun i => assignmentOfSet K (sourceChannel i)

@[simp] theorem sourceValues_modelSet (values : Fin n → Bool) : sourceValues (modelSet values) = values := by
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [sourceValues, assignmentOfSet]

/-- Target/helper membership leaves no additional channels outside the source coordinates. -/
theorem modelSet_sourceValues (K : Finset (Channel (n + 2)))
    (target : targetChannel n ∈ K) (helper : helperChannel n ∈ K) : modelSet (sourceValues K) = K := by
  ext channel
  refine Fin.lastCases ?_ (fun middle => ?_) channel
  · change helperChannel n ∈ modelSet (sourceValues K) ↔ helperChannel n ∈ K
    simp [helper]
  · refine Fin.lastCases ?_ (fun i => ?_) middle
    · change targetChannel n ∈ modelSet (sourceValues K) ↔ targetChannel n ∈ K
      simp [target]
    · change sourceChannel i ∈ modelSet (sourceValues K) ↔ sourceChannel i ∈ K
      simp [sourceValues, assignmentOfSet]

/-- The actual stored decoder output, viewed on eligible sets. -/
def setOutput (formula : FiniteFormula n) (K : Finset (Channel (n + 2))) : Bool :=
  (decoder formula).eval (assignmentOfSet K)
    ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩

/-- Detection zeros have precisely the required source models and helper membership. -/
theorem setOutput_zero_iff (formula : FiniteFormula n) (horn : Controller.Horn.DualHorn formula)
    (K : Finset (Channel (n + 2))) (target : targetChannel n ∈ K) :
    setOutput formula K = false ↔ helperChannel n ∈ K ∧ Satisfies (sourceValues K) formula := by
  have targetOne : assignmentOfSet K (targetChannel n) = true := by simp [assignmentOfSet, target]
  change (decoder formula).eval (assignmentOfSet K) _ = false ↔
    helperChannel n ∈ K ∧ Satisfies (fun i => decide (sourceChannel i ∈ K)) formula
  simpa only [assignmentOfSet, Function.comp_def, decide_eq_true_eq] using
    decoder_zero_iff formula horn (assignmentOfSet K) targetOne


/-- The helper guard makes the target-only healthy output one. -/
theorem setOutput_healthy (formula : FiniteFormula n) (horn : Controller.Horn.DualHorn formula) :
    setOutput formula {targetChannel n} = true := by
  have impossible : setOutput formula {targetChannel n} ≠ false := by
    intro zero
    have helper := ((setOutput_zero_iff formula horn {targetChannel n} (by simp)).mp zero).1
    exact helper_ne_target (Finset.mem_singleton.mp helper)
  cases value : setOutput formula {targetChannel n} <;> simp_all

theorem modelSet_zero_iff (formula : FiniteFormula n) (horn : Controller.Horn.DualHorn formula)
    (values : Fin n → Bool) :
    setOutput formula (modelSet values) = false ↔ Satisfies values formula := by
  simpa only [modelSet_helper, true_and, sourceValues_modelSet] using
    setOutput_zero_iff formula horn (modelSet values) (modelSet_target values)

abbrev SourceModels (formula : FiniteFormula n) :=
  {values : Fin n → Bool // Satisfies values formula}

abbrev DetectingSets (formula : FiniteFormula n) :=
  {K : Finset (Channel (n + 2)) // Admissible 1 (targetChannel n) K ∧
    setOutput formula K ≠ setOutput formula {targetChannel n}}

theorem detecting_set_model (formula : FiniteFormula n) (horn : Controller.Horn.DualHorn formula)
    (K : DetectingSets formula) :
    helperChannel n ∈ K.val ∧ Satisfies (sourceValues K.val) formula := by
  have target := (admissible_one _ _).mp K.property.1
  have notTrue : setOutput formula K.val ≠ true := by
    simpa only [setOutput_healthy formula horn] using K.property.2
  have zero : setOutput formula K.val = false := by
    cases value : setOutput formula K.val with
    | false => rfl
    | true => exact False.elim (notTrue value)
  exact (setOutput_zero_iff formula horn K.val target).mp zero

/-- Exact bijection, retaining the entire declared source variable universe. -/
noncomputable def modelDetectionEquiv (formula : FiniteFormula n)
    (horn : Controller.Horn.DualHorn formula) : SourceModels formula ≃ DetectingSets formula where
  toFun values := ⟨modelSet values.val,
    (admissible_one _ _).mpr (modelSet_target values.val), by
      have zero := (modelSet_zero_iff formula horn values.val).mpr values.property
      rw [setOutput_healthy formula horn, zero]
      decide⟩
  invFun K := ⟨sourceValues K.val, (detecting_set_model formula horn K).2⟩
  left_inv values := by
    apply Subtype.ext
    exact sourceValues_modelSet values.val
  right_inv K := by
    apply Subtype.ext
    exact modelSet_sourceValues K.val ((admissible_one _ _).mp K.property.1)
      (detecting_set_model formula horn K).1

/-- One bus and one helper driver suffice for the source-model reduction. -/
def modelBridge (n : ℕ) : Physical.Bridge (n + 2) where
  target := targetChannel n
  drivers := {helperChannel n}
  drivers_nonempty := by simp
  target_not_mem := by
    simp only [Finset.mem_singleton]
    exact Ne.symm helper_ne_target

/-- The sole observed coordinate is the actual stored decoder root. -/
def modelObservation (formula : FiniteFormula n) :
    Fin 1 → Assignment (n + 2) → Bool := fun _ values =>
  (decoder formula).eval values
    ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩

@[simp] theorem modelObservation_set (formula : FiniteFormula n)
    (K : Finset (Channel (n + 2))) (output : Fin 1) :
    modelObservation formula output (assignmentOfSet K) = setOutput formula K := rfl

/-- Physical detectability holds exactly when the declared source has a model. -/
theorem model_bridge_detectable_iff (formula : FiniteFormula n)
    (horn : Controller.Horn.DualHorn formula) :
    Physical.BridgeDetectable (b := 1) (modelBridge n) true (modelObservation formula) ↔
      ∃ values : Fin n → Bool, Satisfies values formula := by
  rw [Physical.bridge_detectable_iff_exists_output (modelBridge n) (by decide : 0 < 1)]
  constructor
  · rintro ⟨_, K, legal, output, different⟩
    let detected : DetectingSets formula := ⟨K, legal, different⟩
    refine ⟨sourceValues K, ?_⟩
    simpa only [detected] using (detecting_set_model formula horn detected).2
  · rintro ⟨values, satisfies⟩
    have detected := modelDetectionEquiv formula horn ⟨values, satisfies⟩
    exact ⟨rfl, detected.val, detected.property.1, 0, detected.property.2⟩

/-- Each source model has the canonical actual primary-input detecting witness. -/
theorem model_realizer_detects (formula : FiniteFormula n)
    (horn : Controller.Horn.DualHorn formula) (values : Fin n → Bool)
    (satisfies : Satisfies values formula) :
    Physical.BridgeInputDetects (modelBridge n) true (modelObservation formula)
      (Physical.realizeBridge (modelBridge n) (by decide : 0 < 1) (modelSet values)) true := by
  apply (Physical.realizeBridge_detects_iff (modelBridge n) (by decide : 0 < 1)
    (modelSet values) ((admissible_one _ _).mpr (modelSet_target values))
    (modelObservation formula)).mpr
  refine ⟨0, ?_⟩
  change setOutput formula {targetChannel n} ≠ setOutput formula (modelSet values)
  rw [setOutput_healthy formula horn, (modelSet_zero_iff formula horn values).mpr satisfies]
  decide

/-- Helper eligibility does not require a positive helper request. -/
theorem model_realizer_helper_request_zero (K : Finset (Channel (n + 2)))
    (bus : Fin 1) :
    (Physical.realizeBridge (modelBridge n) (by decide : 0 < 1) K).request
      bus (helperChannel n) = false := by
  have busZero : bus = 0 := Subsingleton.elim _ _
  subst bus
  simp [Physical.realizeBridge, Physical.realizeRequests, modelBridge,
    assignmentOfSet, helper_ne_target]

end Controller.Reductions.DualHorn
