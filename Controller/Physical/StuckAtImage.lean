module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.Faults
public import Controller.Physical.CandidateInvariant

@[expose] public section

/-!
# Qualifier-only stuck-at classification

Only the specified final-qualifier request occurrence changes. The healthy
selector flags remain fixed. A single requesting bus supports the three explicit
detecting witnesses; nonemptiness of the healthy qualifiers proves the ordinary
stuck-zero exclusion.
-/

namespace Controller.Physical

private theorem runMasks_none_flags_eq {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (j : Fin b) :
    (runMasks b active request none).flags j = anyTrue ((runMasks b active request none).terms j) := by
  induction b generalizing active with
  | zero => exact Fin.elim0 j
  | succ b ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · exact ih _ _ k

/-- Enable a supplied set and let a supplied request set request only on one bus. -/
def singleBusInput {n b : ℕ} (bus : Fin b) (enabled requests : Finset (Channel n)) :
    PrimaryInput n b where
  positiveBuses := by have := bus.isLt; omega
  enable := assignmentOfSet enabled
  request := fun j => if j = bus then assignmentOfSet requests else (fun _ => false)

/-- A nonempty enabled request group selects exactly its sole requesting bus. -/
theorem singleBusInput_flags {n b : ℕ} (bus : Fin b) (enabled requests : Finset (Channel n))
    (hsub : requests ⊆ enabled) (hne : requests.Nonempty) :
    (healthyRun (singleBusInput bus enabled requests)).flags = (fun j => decide (j = bus)) := by
  let input := singleBusInput bus enabled requests
  let run := healthyRun input
  have hflag_eq (j : Fin b) : run.flags j = anyTrue (run.terms j) :=
    runMasks_none_flags_eq b input.enable input.request j
  have hterms (j : Fin b) (hj : j ≠ bus) : run.terms j = (fun _ => false) := by
    funext i
    change (runMasks b input.enable input.request none).terms j i = false
    rw [runMasks_terms_eq]
    simp [stageTerms, input, singleBusInput, hj]
  have hflags (j : Fin b) (hj : j ≠ bus) : run.flags j = false := by
    rw [hflag_eq, hterms j hj]
    simp [anyTrue]
  have hmasks (j : Fin b) (hj : j ≠ bus) : run.masks j = (fun _ => true) := by
    funext i
    change (runMasks b input.enable input.request none).masks j i = true
    rw [runMasks_masks_eq]
    change stageMask (run.flags j) (run.terms j) i = true
    rw [hflags j hj, hterms j hj]
    rfl
  have hselected : run.terms bus = assignmentOfSet requests := by
    funext i
    apply Bool.eq_iff_iff.mpr
    change (runMasks b input.enable input.request none).terms bus i = true ↔
      assignmentOfSet requests i = true
    rw [runMasks_terms_true_iff]
    have hrequest : input.request bus = assignmentOfSet requests := by
      simp [input, singleBusInput]
    rw [hrequest]
    constructor
    · rintro ⟨_, hi, _⟩
      exact hi
    · intro hi
      refine ⟨(assignmentOfSet_eq_true enabled i).mpr (hsub ((assignmentOfSet_eq_true requests i).mp hi)), hi, ?_⟩
      intro j hj
      exact congrFun (hmasks j (ne_of_lt hj)) i
  have hselectedFlag : run.flags bus = true := by
    rw [hflag_eq, hselected]
    obtain ⟨i, hi⟩ := hne
    exact (anyTrue_eq_true _).mpr ⟨i, by simpa using hi⟩
  funext j
  change run.flags j = decide (j = bus)
  by_cases hj : j = bus
  · subst j
    simp [hselectedFlag]
  · simp [hflags j hj, hj]

/-- The single requesting group is exactly the healthy eligible set. -/
theorem singleBusInput_healthy {n b : ℕ} (bus : Fin b) (enabled requests : Finset (Channel n))
    (hsub : requests ⊆ enabled) (hne : requests.Nonempty) :
    healthyQualifiers (singleBusInput bus enabled requests) = assignmentOfSet requests := by
  unfold healthyQualifiers
  rw [singleBusInput_flags bus enabled requests hsub hne]
  funext i
  by_cases hi : i ∈ requests
  · have he := hsub hi
    simp [qualifiers, singleBusInput, assignmentOfSet, hi, he]
  · simp [qualifiers, singleBusInput, assignmentOfSet, hi]

/-- The stuck occurrence affects only the chosen target in the single-bus input. -/
theorem singleBusInput_stuck {n b : ℕ} (bus : Fin b) (enabled requests : Finset (Channel n))
    (hsub : requests ⊆ enabled) (hne : requests.Nonempty) (target : Channel n) (stuck : Bool) :
    stuckQualifiers (singleBusInput bus enabled requests) target bus stuck =
      (fun i => if i = target then assignmentOfSet enabled i && !stuck else assignmentOfSet requests i) := by
  funext i
  by_cases hi : i = target
  · subst i
    unfold stuckQualifiers
    rw [singleBusInput_flags bus enabled requests hsub hne]
    simp [qualifiers, stuckRequests, singleBusInput]
  · rw [stuckQualifiers_eq_of_ne _ target i bus stuck hi,
      singleBusInput_healthy bus enabled requests hsub hne]
    simp [hi]

/-- On the single requesting bus, stuck zero adds an enabled target. -/
theorem singleBusInput_stuck_zero {n b : ℕ} (bus : Fin b)
    (enabled requests : Finset (Channel n)) (hsub : requests ⊆ enabled)
    (hne : requests.Nonempty) (target : Channel n) (henabled : target ∈ enabled) :
    stuckQualifiers (singleBusInput bus enabled requests) target bus false =
      assignmentOfSet (insert target requests) := by
  rw [singleBusInput_stuck bus enabled requests hsub hne target false]
  funext i
  by_cases hi : i = target
  · subst i
    simp [assignmentOfSet, henabled]
  · simp [assignmentOfSet, hi]

/-- On the single requesting bus, stuck one deletes the target. -/
theorem singleBusInput_stuck_one {n b : ℕ} (bus : Fin b)
    (enabled requests : Finset (Channel n)) (hsub : requests ⊆ enabled)
    (hne : requests.Nonempty) (target : Channel n) :
    stuckQualifiers (singleBusInput bus enabled requests) target bus true =
      assignmentOfSet (requests.erase target) := by
  rw [singleBusInput_stuck bus enabled requests hsub hne target true]
  funext i
  by_cases hi : i = target
  · subst i
    simp [assignmentOfSet]
  · simp [assignmentOfSet, hi]

/-- The distinguished-channel output is true exactly when its qualifier is
false and some qualifier is true. -/
theorem qualifierOutput_eq_true_iff {n : ℕ} (distinguished : Channel n) (h : Assignment n) :
    qualifierOutput distinguished h = true ↔
      h distinguished = false ∧ ∃ i, h i = true := by
  have hbase : qualifierOutput distinguished h = true ↔
      h distinguished = false ∧ ∃ i, i ≠ distinguished ∧ h i = true := by
    simp [qualifierOutput]
  rw [hbase]
  constructor
  · rintro ⟨hs, i, _, hi⟩
    exact ⟨hs, i, hi⟩
  · rintro ⟨hs, i, hi⟩
    refine ⟨hs, i, ?_, hi⟩
    intro his
    subst i
    simp [hs] at hi

/-- Every faulty qualifier still requires its channel's enable input. -/
theorem stuckQualifiers_implies_enabled {n b : ℕ} (input : PrimaryInput n b)
    (target i : Channel n) (bus : Fin b) (stuck : Bool)
    (hi : stuckQualifiers input target bus stuck i = true) : input.enable i = true :=
  ((qualifiers_eq_true input.enable (stuckRequests input target bus stuck)
    (healthyRun input).flags i).mp hi).1

/-- Asserting a qualifier request can only add eligible channels. -/
theorem stuck_zero_qualifiers_mono {n b : ℕ} (input : PrimaryInput n b)
    (target i : Channel n) (bus : Fin b) (hi : healthyQualifiers input i = true) :
    stuckQualifiers input target bus false i = true := by
  obtain ⟨he, hr⟩ := (qualifiers_eq_true input.enable input.request (healthyRun input).flags i).mp hi
  apply (qualifiers_eq_true input.enable (stuckRequests input target bus false)
    (healthyRun input).flags i).mpr
  refine ⟨he, ?_⟩
  intro j hj
  by_cases hhit : i = target ∧ j = bus
  · simp [stuckRequests, hhit]
  · simpa [stuckRequests, hhit] using hr j hj

/-- An ordinary-channel stuck-zero fault preserves the observed output on
every primary input, whether or not the raw branch fault is activated. -/
theorem qualifierOutput_stuck_zero_of_ne {n b : ℕ} (input : PrimaryInput n b)
    (distinguished target : Channel n) (bus : Fin b) (ht : target ≠ distinguished) :
    qualifierOutput distinguished (healthyQualifiers input) =
      qualifierOutput distinguished (stuckQualifiers input target bus false) := by
  have hs := stuckQualifiers_eq_of_ne input target distinguished bus false (Ne.symm ht)
  apply Bool.eq_iff_iff.mpr
  rw [qualifierOutput_eq_true_iff, qualifierOutput_eq_true_iff]
  constructor
  · rintro ⟨hzero, i, hi⟩
    exact ⟨hs.trans hzero, i, stuck_zero_qualifiers_mono input target i bus hi⟩
  · rintro ⟨hzero, i, hi⟩
    refine ⟨hs.symm.trans hzero, ?_⟩
    apply (healthyQualifiers_nonempty_iff input).mpr
    exact ⟨i, stuckQualifiers_implies_enabled input target i bus false hi⟩

/-- The negative ordinary-channel row of the stuck-at classification. -/
theorem not_stuckDetectable_zero_of_ne {n b : ℕ} (distinguished target : Channel n)
    (bus : Fin b) (ht : target ≠ distinguished) :
    ¬ StuckDetectable distinguished target bus false := by
  rintro ⟨input, _, changed⟩
  exact changed (qualifierOutput_stuck_zero_of_ne input distinguished target bus ht)

/-- A detecting stuck-zero input at the distinguished channel: the other
channel requests on the selected bus and the target requests nowhere. -/
def stuckZeroDistinguishedInput {n b : ℕ} (target other : Channel n) (bus : Fin b) :
    PrimaryInput n b := singleBusInput bus {target, other} {other}

/-- A detecting stuck-one input at an ordinary channel uses only that channel. -/
def stuckOneOrdinaryInput {n b : ℕ} (target : Channel n) (bus : Fin b) :
    PrimaryInput n b := singleBusInput bus {target} {target}

/-- A detecting stuck-one input at the distinguished channel makes it tie
with one other enabled channel on the selected bus. -/
def stuckOneDistinguishedInput {n b : ℕ} (target other : Channel n) (bus : Fin b) :
    PrimaryInput n b := singleBusInput bus {target, other} {target, other}

/-- The stuck-zero distinguished witness activates the fault and changes the
eligible set from the other singleton to the enabled pair. -/
theorem stuckZeroDistinguished_spec {n b : ℕ} (target other : Channel n) (bus : Fin b)
    (hother : other ≠ target) :
    StuckActivated (stuckZeroDistinguishedInput target other bus) target bus false ∧
      healthyQualifiers (stuckZeroDistinguishedInput target other bus) = assignmentOfSet {other} ∧
      stuckQualifiers (stuckZeroDistinguishedInput target other bus) target bus false =
        assignmentOfSet {target, other} := by
  refine ⟨?_, ?_, ?_⟩
  · simp [StuckActivated, stuckZeroDistinguishedInput, singleBusInput, assignmentOfSet,
      Ne.symm hother]
  · exact singleBusInput_healthy bus {target, other} {other} (by simp) (by simp)
  · exact singleBusInput_stuck_zero bus {target, other} {other} (by simp) (by simp)
      target (by simp)

/-- The ordinary stuck-one witness activates the fault and removes its only
eligible channel. -/
theorem stuckOneOrdinary_spec {n b : ℕ} (target : Channel n) (bus : Fin b) :
    StuckActivated (stuckOneOrdinaryInput target bus) target bus true ∧
      healthyQualifiers (stuckOneOrdinaryInput target bus) = assignmentOfSet {target} ∧
      stuckQualifiers (stuckOneOrdinaryInput target bus) target bus true =
        assignmentOfSet ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [StuckActivated, stuckOneOrdinaryInput, singleBusInput, assignmentOfSet]
  · exact singleBusInput_healthy bus {target} {target} (Finset.Subset.refl _) (by simp)
  · simpa [stuckOneOrdinaryInput] using
      singleBusInput_stuck_one bus {target} {target} (Finset.Subset.refl _) (by simp) target

/-- The distinguished stuck-one witness activates the fault and leaves the
other member of its two-channel eligible set. -/
theorem stuckOneDistinguished_spec {n b : ℕ} (target other : Channel n) (bus : Fin b)
    (hother : other ≠ target) :
    StuckActivated (stuckOneDistinguishedInput target other bus) target bus true ∧
      healthyQualifiers (stuckOneDistinguishedInput target other bus) = assignmentOfSet {target, other} ∧
      stuckQualifiers (stuckOneDistinguishedInput target other bus) target bus true =
        assignmentOfSet {other} := by
  refine ⟨?_, ?_, ?_⟩
  · simp [StuckActivated, stuckOneDistinguishedInput, singleBusInput, assignmentOfSet]
  · exact singleBusInput_healthy bus {target, other} {target, other} (Finset.Subset.refl _) (by simp)
  · simpa [stuckOneDistinguishedInput, hother, Ne.symm hother] using
      singleBusInput_stuck_one bus {target, other} {target, other}
        (Finset.Subset.refl _) (by simp) target

/-- Positive stuck-zero row: the fault is at the distinguished channel. -/
theorem stuckZeroDistinguished_detectable {n b : ℕ} (target other : Channel n) (bus : Fin b)
    (hother : other ≠ target) : StuckDetectable target target bus false := by
  obtain ⟨hactivated, hhealthy, hfaulty⟩ := stuckZeroDistinguished_spec target other bus hother
  refine ⟨stuckZeroDistinguishedInput target other bus, hactivated, ?_⟩
  rw [hhealthy, hfaulty]
  simp [qualifierOutput, assignmentOfSet, hother, Ne.symm hother]

/-- Positive stuck-one row at an ordinary channel. -/
theorem stuckOneOrdinary_detectable {n b : ℕ} (distinguished target : Channel n)
    (bus : Fin b) (ht : target ≠ distinguished) : StuckDetectable distinguished target bus true := by
  obtain ⟨hactivated, hhealthy, hfaulty⟩ := stuckOneOrdinary_spec target bus
  refine ⟨stuckOneOrdinaryInput target bus, hactivated, ?_⟩
  rw [hhealthy, hfaulty]
  simp [qualifierOutput, assignmentOfSet, ht, Ne.symm ht]

/-- Positive stuck-one row at the distinguished channel. -/
theorem stuckOneDistinguished_detectable {n b : ℕ} (target other : Channel n) (bus : Fin b)
    (hother : other ≠ target) : StuckDetectable target target bus true := by
  obtain ⟨hactivated, hhealthy, hfaulty⟩ := stuckOneDistinguished_spec target other bus hother
  refine ⟨stuckOneDistinguishedInput target other bus, hactivated, ?_⟩
  rw [hhealthy, hfaulty]
  simp [qualifierOutput, assignmentOfSet, hother, Ne.symm hother]

/-- Choose channel one when the target is channel zero, and channel zero otherwise. -/
def otherChannel {n : ℕ} (hn : 2 ≤ n) (target : Channel n) : Channel n :=
  if target.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

/-- The explicit alternative channel differs from the target. -/
theorem otherChannel_ne {n : ℕ} (hn : 2 ≤ n) (target : Channel n) :
    otherChannel hn target ≠ target := by
  unfold otherChannel
  split
  · intro h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega

/-- Complete detectability classification for the specified active-low branch
fault at every channel and bus. -/
theorem stuck_detectable_iff {n b : ℕ} (distinguished target : Channel n)
    (bus : Fin b) (stuck : Bool) :
    StuckDetectable distinguished target bus stuck ↔
      2 ≤ n ∧ (stuck = true ∨ target = distinguished) := by
  constructor
  · intro hdetect
    have hn : 2 ≤ n := by
      by_contra hsmall
      have hn1 : n = 1 := by
        have ht := target.isLt
        omega
      subst n
      exact not_stuckDetectable_one distinguished target bus stuck hdetect
    refine ⟨hn, ?_⟩
    cases stuck with
    | false =>
        right
        by_contra ht
        exact not_stuckDetectable_zero_of_ne distinguished target bus ht hdetect
    | true => exact Or.inl rfl
  · rintro ⟨hn, hcase⟩
    cases stuck with
    | false =>
        have htarget : target = distinguished := by simpa using hcase
        subst distinguished
        exact stuckZeroDistinguished_detectable target (otherChannel hn target) bus
          (otherChannel_ne hn target)
    | true =>
        by_cases htarget : target = distinguished
        · subst distinguished
          exact stuckOneDistinguished_detectable target (otherChannel hn target) bus
            (otherChannel_ne hn target)
        · exact stuckOneOrdinary_detectable distinguished target bus htarget

end Controller.Physical
