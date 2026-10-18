module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.DualHorn

@[expose] public section

/-! Greatest-model semantics and the safe downward-forcing rule. No worklist
implementation or running-time bound is asserted by these existence lemmas. -/
namespace Controller.Horn
open CNF

noncomputable def greatestCandidate (f : Formula α) : α → Bool := by
  classical
  exact fun i => decide (∃ a, Satisfies a f ∧ a i = true)

@[simp] theorem greatestCandidate_true_iff (f : Formula α) (i : α) :
    greatestCandidate f i = true ↔ ∃ a, Satisfies a f ∧ a i = true := by
  classical
  simp [greatestCandidate]

theorem model_below_greatest {f : Formula α} {a : α → Bool} (ha : Satisfies a f) :
    Below a (greatestCandidate f) := by
  intro i hi
  exact (greatestCandidate_true_iff f i).mpr ⟨a, ha, hi⟩

theorem greatestCandidate_satisfies {f : Formula α} (hf : DualHorn f)
    (hs : Satisfiable f) : Satisfies (greatestCandidate f) f := by
  classical
  obtain ⟨a, ha⟩ := hs
  intro c hc
  rcases hf c hc with ht | hn
  · obtain ⟨l, hl, hneg⟩ := ht
    exact tautology_holds _ hl hneg
  · obtain ⟨⟨i, p⟩, hl, hli⟩ := ha c hc
    cases p with
    | true =>
      refine ⟨(i, true), hl, ?_⟩
      exact (greatestCandidate_true_iff f i).mpr ⟨a, ha, hli⟩
    | false =>
      by_cases hg : greatestCandidate f i = false
      · exact ⟨(i, false), hl, hg⟩
      · have hgt : greatestCandidate f i = true := Bool.eq_true_of_not_eq_false hg
        obtain ⟨b, hb, hbi⟩ := (greatestCandidate_true_iff f i).mp hgt
        obtain ⟨⟨j, q⟩, hk, hkj⟩ := hb c hc
        cases q with
        | true =>
          exact ⟨(j, true), hk, (greatestCandidate_true_iff f j).mpr ⟨b, hb, hkj⟩⟩
        | false =>
          have hij : i = j := hn (i, false) hl (j, false) hk rfl rfl
          exact False.elim (Bool.false_ne_true (hkj.symm.trans (hij ▸ hbi)))

theorem exists_greatest_model {f : Formula α} (hf : DualHorn f) (hs : Satisfiable f) :
    ∃ g, Satisfies g f ∧ ∀ a, Satisfies a f → Below a g :=
  ⟨greatestCandidate f, greatestCandidate_satisfies hf hs, fun _ ha => model_below_greatest ha⟩

/-- A clause with no true positive literal forces its unique negative variable
off in every model below the current assignment. -/
theorem downward_forcing_safe {f : Formula α} {c : Clause α} {current a : α → Bool}
    {i : α} (hc : c ∈ f.clauses) (hn : NegativeUnique c)
    (hi : (i, false) ∈ c) (hpositive : ∀ l ∈ c, l.2 = true → current l.1 = false)
    (ha : Satisfies a f) (hbelow : Below a current) : a i = false := by
  obtain ⟨⟨j, q⟩, hl, haj⟩ := ha c hc
  cases q with
  | true =>
    have hj := hbelow j haj
    have hfalse := hpositive (j, true) hl rfl
    exact False.elim (Bool.false_ne_true (hfalse.symm.trans hj))
  | false =>
    have hij : i = j := hn (i, false) hi (j, false) hl rfl rfl
    simpa [LiteralHolds, hij] using haj

theorem positive_conflict_unsatisfiable {f : Formula α} {c : Clause α}
    {current : α → Bool} (hc : c ∈ f.clauses)
    (hpositive : ∀ l ∈ c, l.2 = true)
    (hallfalse : ∀ l ∈ c, current l.1 = false)
    (hupper : ∀ a, Satisfies a f → Below a current) : Unsatisfiable f := by
  rintro ⟨a, ha⟩
  obtain ⟨l, hl, hal⟩ := ha c hc
  have htrue : a l.1 = true := hal.trans (hpositive l hl)
  have hcur := hupper a ha l.1 htrue
  exact Bool.false_ne_true ((hallfalse l hl).symm.trans hcur)

def forceFalse [DecidableEq α] (current : α → Bool) (i : α) : α → Bool :=
  fun j => if j = i then false else current j

theorem forcing_preserves_upper [DecidableEq α] {f : Formula α} {c : Clause α}
    {current : α → Bool} {i : α} (hc : c ∈ f.clauses) (hn : NegativeUnique c)
    (hi : (i, false) ∈ c) (hpositive : ∀ l ∈ c, l.2 = true → current l.1 = false)
    (hupper : ∀ a, Satisfies a f → Below a current) :
    ∀ a, Satisfies a f → Below a (forceFalse current i) := by
  intro a ha j haj
  by_cases hji : j = i
  · subst j
    have hfalse := downward_forcing_safe hc hn hi hpositive ha (hupper a ha)
    exact False.elim (Bool.false_ne_true (hfalse.symm.trans haj))
  · simpa [forceFalse, hji] using hupper a ha j haj

/-- A state with neither a positive-clause conflict nor an enabled negative
forcing step. Tautologies are ignored. This is a semantic terminal invariant. -/
def RulesClosed (f : Formula α) (current : α → Bool) : Prop :=
  ∀ c ∈ f.clauses, ¬Tautological c →
    ((∀ l ∈ c, l.2 = true) → ∃ l ∈ c, current l.1 = true) ∧
    (∀ i, (i, false) ∈ c →
      (∀ l ∈ c, l.2 = true → current l.1 = false) → current i = false)

theorem rulesClosed_satisfies {f : Formula α} {current : α → Bool}
    (hclosed : RulesClosed f current) : Satisfies current f := by
  classical
  intro c hc
  by_cases ht : Tautological c
  · obtain ⟨l, hl, hn⟩ := ht
    exact tautology_holds _ hl hn
  · obtain ⟨hpositive, hnegative⟩ := hclosed c hc ht
    by_cases hpos : ∃ l ∈ c, l.2 = true ∧ current l.1 = true
    · obtain ⟨l, hl, hp, hv⟩ := hpos
      exact ⟨l, hl, hv.trans hp.symm⟩
    · have hoff : ∀ l ∈ c, l.2 = true → current l.1 = false := by
        intro l hl hp
        apply Bool.eq_false_iff.mpr
        exact fun hv => hpos ⟨l, hl, hp, hv⟩
      by_cases hneg : ∃ i, (i, false) ∈ c
      · obtain ⟨i, hi⟩ := hneg
        exact ⟨(i, false), hi, hnegative i hi hoff⟩
      · have hallpos : ∀ l ∈ c, l.2 = true := by
          intro l hl
          apply Bool.eq_true_of_not_eq_false
          intro hp
          apply hneg
          refine ⟨l.1, ?_⟩
          simpa [← hp] using hl
        obtain ⟨l, hl, hv⟩ := hpositive hallpos
        exact False.elim (Bool.false_ne_true ((hoff l hl (hallpos l hl)).symm.trans hv))

theorem terminal_state_greatest {f : Formula α} {current : α → Bool}
    (hclosed : RulesClosed f current)
    (hupper : ∀ a, Satisfies a f → Below a current) :
    Satisfies current f ∧ ∀ a, Satisfies a f → Below a current :=
  ⟨rulesClosed_satisfies hclosed, hupper⟩

/-- The all-true initial state bounds every possible model. -/
theorem below_allTrue (a : α → Bool) : Below a (fun _ => true) :=
  fun _ _ => rfl

theorem forceFalse_below [DecidableEq α] (current : α → Bool) (i : α) :
    Below (forceFalse current i) current := by
  intro j hj
  by_cases hji : j = i
  · simp [forceFalse, hji] at hj
  · simpa [forceFalse, hji] using hj

/-- A successful terminal worklist result agrees with the independently defined
greatest model, rather than with a particular arbitrary satisfying witness. -/
theorem terminal_state_eq_greatest {f : Formula α} {current : α → Bool}
    (hclosed : RulesClosed f current)
    (hupper : ∀ a, Satisfies a f → Below a current) :
    current = greatestCandidate f := by
  apply below_antisymm
  · exact model_below_greatest (rulesClosed_satisfies hclosed)
  · intro i hi
    obtain ⟨a, ha, hai⟩ := (greatestCandidate_true_iff f i).mp hi
    exact hupper a ha i hai

end Controller.Horn
