module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.Controller

@[expose] public section

/-!
# Candidate-fold refinement of the literal selector

The fold works for arbitrary initial candidates and for every suffix length,
including zero. The literal accumulator is proved to equal the enable-and-mask
prefix product. Honest stages retain precisely the candidates covering every
selected one-bit; an overridden first flag is not assumed to have this property.
-/

namespace Controller.Physical

/-- The literal accumulated mask before a bus is its initial value conjoined
with exactly the earlier source XOR masks. -/
theorem runMasks_activeBefore_true_iff {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (override : Option Bool)
    (j : Fin b) (i : Channel n) :
    (runMasks b active request override).activeBefore j i = true ↔
      active i = true ∧ ∀ k : Fin b, k < j →
        (runMasks b active request override).masks k i = true := by
  induction b generalizing active override i with
  | zero => exact Fin.elim0 j
  | succ b ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [runMasks]
      · simpa [runMasks, nextActive, Fin.forall_fin_succ, and_assoc] using
          ih (nextActive active (request 0) (override.getD (stageFlag active (request 0))))
            (fun l => request l.succ) none k i

/-- The final accumulated mask is the initial value conjoined with every
source XOR mask, even when the first flag is externally overridden. -/
theorem runMasks_finalActive_true_iff_masks {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (override : Option Bool) (i : Channel n) :
    (runMasks b active request override).finalActive i = true ↔
      active i = true ∧ ∀ j : Fin b, (runMasks b active request override).masks j i = true := by
  induction b generalizing active override i with
  | zero => simp [runMasks]
  | succ b ih =>
      simpa [runMasks, nextActive, Fin.forall_fin_succ, and_assoc] using
        ih (nextActive active (request 0) (override.getD (stageFlag active (request 0))))
          (fun j => request j.succ) none i

/-- The recorded local terms satisfy the paper's enable/request/prior-mask
conjunction, with no independent assumption about the accumulator. -/
theorem runMasks_terms_true_iff {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (override : Option Bool)
    (j : Fin b) (i : Channel n) :
    (runMasks b active request override).terms j i = true ↔
      active i = true ∧ request j i = true ∧
        ∀ k : Fin b, k < j → (runMasks b active request override).masks k i = true := by
  rw [runMasks_terms_eq]
  simp only [stageTerms, Bool.and_eq_true, runMasks_activeBefore_true_iff]
  constructor
  · rintro ⟨⟨ha, hm⟩, hr⟩
    exact ⟨ha, hr, hm⟩
  · rintro ⟨ha, hr, hm⟩
    exact ⟨⟨ha, hm⟩, hr⟩

/-- Surviving all masks implies qualification, including for a first-flag override.
The converse can fail for an overridden first flag. -/
theorem runMasks_finalActive_imp_qualifiers {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (override : Option Bool) (i : Channel n)
    (hi : (runMasks b active request override).finalActive i = true) :
    qualifiers active request (runMasks b active request override).flags i = true := by
  obtain ⟨ha, hm⟩ := (runMasks_finalActive_true_iff_masks b active request override i).mp hi
  apply (qualifiers_eq_true active request _ i).mpr
  refine ⟨ha, ?_⟩
  intro j hp
  have hmask := hm j
  rw [runMasks_masks_eq] at hmask
  have hterm : (runMasks b active request override).terms j i = true := by
    simpa [stageMask, hp] using hmask
  rw [runMasks_terms_eq] at hterm
  have hpair : (runMasks b active request override).activeBefore j i = true ∧
      request j i = true := by simpa [stageTerms] using hterm
  exact hpair.2

/-- Retain requesting candidates if some candidate requests; otherwise retain all. -/
def candidateStep {n : ℕ} (active request : Assignment n) : Assignment n :=
  fun i => active i && (!(stageFlag active request) || request i)

/-- Honest XOR-mask update and candidate retention are identical. -/
theorem nextActive_eq_candidateStep {n : ℕ} (active request : Assignment n) :
    nextActive active request (stageFlag active request) = candidateStep active request := by
  funext i
  cases hflag : stageFlag active request with
  | false =>
      have hterm : stageTerms active request i = false :=
        eq_false_of_anyTrue_eq_false hflag i
      simp [nextActive, stageMask, candidateStep, hflag, hterm]
  | true =>
      cases ha : active i <;> cases hr : request i <;>
        simp [nextActive, stageMask, stageTerms, candidateStep, hflag, ha, hr]

/-- A retained candidate is enabled in the previous set and covers the selected bit. -/
@[simp] theorem candidateStep_eq_true {n : ℕ} (active request : Assignment n)
    (i : Channel n) :
    candidateStep active request i = true ↔
      active i = true ∧ (stageFlag active request = true → request i = true) := by
  cases hp : stageFlag active request <;> simp [candidateStep, hp]

/-- An honest stage never introduces a candidate outside its initial seed. -/
theorem candidateStep_subset {n : ℕ} (active request : Assignment n) (i : Channel n)
    (hi : candidateStep active request i = true) : active i = true :=
  ((candidateStep_eq_true active request i).mp hi).1

/-- A zero flag retains every initial candidate. -/
theorem candidateStep_of_flag_false {n : ℕ} (active request : Assignment n)
    (hflag : stageFlag active request = false) : candidateStep active request = active := by
  funext i
  simp [candidateStep, hflag]

/-- A one flag retains precisely the requesting initial candidates. -/
theorem candidateStep_of_flag_true {n : ℕ} (active request : Assignment n)
    (hflag : stageFlag active request = true) :
    candidateStep active request = stageTerms active request := by
  funext i
  simp [candidateStep, stageTerms, hflag]

/-- The flag selected from a singleton seed equals that channel's request. -/
theorem stageFlag_singleton {n : ℕ} (target : Channel n) (request : Assignment n) :
    stageFlag (assignmentOfSet {target}) request = request target := by
  apply Bool.eq_iff_iff.mpr
  simp [stageFlag, stageTerms, anyTrue, assignmentOfSet]

/-- Every honest stage preserves a singleton seed. -/
theorem candidateStep_singleton {n : ℕ} (target : Channel n) (request : Assignment n) :
    candidateStep (assignmentOfSet {target}) request = assignmentOfSet {target} := by
  funext i
  by_cases hi : i = target
  · subst i
    cases hr : request target <;>
      simp [candidateStep, stageFlag_singleton, assignmentOfSet, hr]
  · simp [candidateStep, assignmentOfSet, hi]

/-- One honest stage preserves nonemptiness in both directions. -/
theorem candidateStep_nonempty_iff {n : ℕ} (active request : Assignment n) :
    (∃ i, candidateStep active request i = true) ↔ ∃ i, active i = true := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, ((candidateStep_eq_true active request i).mp hi).1⟩
  · rintro ⟨i, hi⟩
    by_cases hflag : stageFlag active request = true
    · obtain ⟨k, hk⟩ := (anyTrue_eq_true (stageTerms active request)).mp hflag
      have hk' : active k = true ∧ request k = true := by
        simpa [stageTerms] using hk
      exact ⟨k, (candidateStep_eq_true active request k).mpr ⟨hk'.1, fun _ => hk'.2⟩⟩
    · exact ⟨i, (candidateStep_eq_true active request i).mpr ⟨hi, fun hp => False.elim (hflag hp)⟩⟩

/-- Every surviving candidate's request equals the selected flag, including zero flags. -/
theorem candidateStep_request_eq_flag {n : ℕ} (active request : Assignment n)
    (i : Channel n) (hi : candidateStep active request i = true) :
    request i = stageFlag active request := by
  have hactive := ((candidateStep_eq_true active request i).mp hi).1
  cases hflag : stageFlag active request with
  | false =>
      have hterm : stageTerms active request i = false :=
        eq_false_of_anyTrue_eq_false hflag i
      simpa [stageTerms, hactive] using hterm
  | true =>
      exact ((candidateStep_eq_true active request i).mp hi).2 hflag

/-- Flags and survivors of a candidate scan of a finite suffix. -/
structure CandidateRun (n b : ℕ) where
  flags : Fin b → Bool
  finalActive : Assignment n

/-- Scan request columns from an arbitrary candidate seed, including an empty suffix. -/
def runCandidates {n : ℕ} : (b : ℕ) → Assignment n → (Fin b → Assignment n) →
    CandidateRun n b
  | 0, active, _ => { flags := Fin.elim0, finalActive := active }
  | b + 1, active, request =>
      let rest := runCandidates b (candidateStep active (request 0)) (fun j => request j.succ)
      { flags := Fin.cases (stageFlag active (request 0)) rest.flags
        finalActive := rest.finalActive }

/-- The honest literal run and the candidate scan have identical flags and survivors. -/
theorem runMasks_refines_candidates {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) :
    (runMasks b active request none).flags = (runCandidates b active request).flags ∧
      (runMasks b active request none).finalActive = (runCandidates b active request).finalActive := by
  induction b generalizing active with
  | zero => exact ⟨rfl, rfl⟩
  | succ b ih =>
      have hrest := ih (candidateStep active (request 0)) (fun j => request j.succ)
      constructor
      · funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · simpa [runMasks, runCandidates, nextActive_eq_candidateStep] using congrFun hrest.1 k
      · simpa [runMasks, runCandidates, nextActive_eq_candidateStep] using hrest.2

/-- A finite suffix preserves nonemptiness for every initial candidate set. -/
theorem runCandidates_nonempty_iff {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) :
    (∃ i, (runCandidates b active request).finalActive i = true) ↔
      ∃ i, active i = true := by
  induction b generalizing active with
  | zero => rfl
  | succ b ih =>
      change (∃ i, (runCandidates b (candidateStep active (request 0))
        (fun j => request j.succ)).finalActive i = true) ↔ _
      exact (ih _ _).trans (candidateStep_nonempty_iff active (request 0))

/-- Final candidates are exactly the initial candidates covering all selected one-bits. -/
theorem runCandidates_finalActive_true_iff {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (i : Channel n) :
    (runCandidates b active request).finalActive i = true ↔
      active i = true ∧ ∀ j, (runCandidates b active request).flags j = true →
        request j i = true := by
  induction b generalizing active i with
  | zero => simp [runCandidates]
  | succ b ih =>
      simpa [runCandidates, candidateStep_eq_true, Fin.forall_fin_succ, and_assoc] using
        ih (candidateStep active (request 0)) (fun j => request j.succ) i

/-- A surviving request row agrees with every selected flag, not only its one-bits. -/
theorem runCandidates_request_eq_flags {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (i : Channel n)
    (hi : (runCandidates b active request).finalActive i = true) (j : Fin b) :
    request j i = (runCandidates b active request).flags j := by
  induction b generalizing active with
  | zero => exact Fin.elim0 j
  | succ b ih =>
      have hnext : candidateStep active (request 0) i = true :=
        ((runCandidates_finalActive_true_iff b (candidateStep active (request 0))
          (fun k => request k.succ) i).mp hi).1
      refine Fin.cases ?_ (fun k => ?_) j
      · exact candidateStep_request_eq_flag active (request 0) i hnext
      · exact ih _ _ hi k

/-- For an honest run, its final accumulated mask equals the independently defined qualifiers. -/
theorem runMasks_finalActive_eq_qualifiers {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) :
    (runMasks b active request none).finalActive =
      qualifiers active request (runMasks b active request none).flags := by
  have hrun := runMasks_refines_candidates b active request
  funext i
  apply Bool.eq_iff_iff.mpr
  rw [hrun.2, qualifiers_eq_true, hrun.1]
  exact runCandidates_finalActive_true_iff b active request i

/-- The physical healthy qualifiers are precisely the honest selector's final candidates. -/
theorem healthyQualifiers_eq_finalActive {n b : ℕ} (input : PrimaryInput n b) :
    healthyQualifiers input = (healthyRun input).finalActive :=
  (runMasks_finalActive_eq_qualifiers b input.enable input.request).symm

/-- Some healthy qualifier is true exactly when some channel is enabled. -/
theorem healthyQualifiers_nonempty_iff {n b : ℕ} (input : PrimaryInput n b) :
    (∃ i, healthyQualifiers input i = true) ↔ ∃ i, input.enable i = true := by
  rw [healthyQualifiers_eq_finalActive]
  unfold healthyRun
  rw [(runMasks_refines_candidates b input.enable input.request).2]
  exact runCandidates_nonempty_iff b input.enable input.request

/-- With no initial candidates every selected flag and every final candidate is false. -/
theorem runCandidates_empty {n : ℕ} (b : ℕ) (request : Fin b → Assignment n) :
    (runCandidates b (fun _ => false) request).flags = (fun _ => false) ∧
      (runCandidates b (fun _ => false) request).finalActive = (fun _ => false) := by
  induction b with
  | zero =>
      constructor
      · funext j
        exact Fin.elim0 j
      · rfl
  | succ b ih =>
      have hrest := ih (fun j => request j.succ)
      have hstep : candidateStep (fun _ => false) (request 0) = (fun _ => false) := by
        funext i
        simp [candidateStep]
      constructor
      · funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [runCandidates, stageFlag, stageTerms, anyTrue]
        · simpa [runCandidates, hstep] using congrFun hrest.1 k
      · simpa [runCandidates, hstep] using hrest.2

/-- A singleton seed survives every suffix and determines all selected flags. -/
theorem runCandidates_singleton {n : ℕ} (b : ℕ) (target : Channel n)
    (request : Fin b → Assignment n) :
    (runCandidates b (assignmentOfSet {target}) request).flags = (fun j => request j target) ∧
      (runCandidates b (assignmentOfSet {target}) request).finalActive =
        assignmentOfSet {target} := by
  induction b with
  | zero =>
      constructor
      · funext j
        exact Fin.elim0 j
      · rfl
  | succ b ih =>
      have hrest := ih (fun j => request j.succ)
      constructor
      · funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [runCandidates, stageFlag_singleton]
        · simpa [runCandidates, candidateStep_singleton] using congrFun hrest.1 k
      · simpa [runCandidates, candidateStep_singleton] using hrest.2

/-- A singleton enabled first request gives the same singleton healthy eligible
set for every request suffix. -/
theorem healthyQualifiers_eq_singleton_of_firstTerms {n b : ℕ}
    (input : PrimaryInput n b) (target : Channel n)
    (hfirst : stageTerms input.enable (input.request input.firstBus) = assignmentOfSet {target}) :
    healthyQualifiers input = assignmentOfSet {target} := by
  cases b with
  | zero => exact (Nat.lt_irrefl 0 input.positiveBuses).elim
  | succ b =>
      have hflag : stageFlag input.enable (input.request 0) = true := by
        change anyTrue (stageTerms input.enable (input.request input.firstBus)) = true
        rw [hfirst]
        exact (anyTrue_eq_true _).mpr ⟨target, by simp [assignmentOfSet]⟩
      have hstep : nextActive input.enable (input.request 0)
          (stageFlag input.enable (input.request 0)) = assignmentOfSet {target} := by
        rw [nextActive_eq_candidateStep, candidateStep_of_flag_true _ _ hflag]
        exact hfirst
      rw [healthyQualifiers_eq_finalActive]
      change (runMasks b (nextActive input.enable (input.request 0)
        (stageFlag input.enable (input.request 0))) (fun j => input.request j.succ) none).finalActive = _
      rw [hstep, (runMasks_refines_candidates b (assignmentOfSet {target})
        (fun j => input.request j.succ)).2]
      exact (runCandidates_singleton b target (fun j => input.request j.succ)).2

/-- The target can qualify despite not surviving the faulty first selector mask. -/
theorem faultyQualifier_need_not_survive :
    ∃ input : PrimaryInput 2 1,
      (runFromFirst input false).finalActive 0 = false ∧
        qualifiersFromFirst input false 0 = true := by
  refine ⟨{ positiveBuses := by decide
            enable := fun i => decide (i = 0)
            request := fun _ i => decide (i = 0) }, ?_⟩
  decide

end Controller.Physical
