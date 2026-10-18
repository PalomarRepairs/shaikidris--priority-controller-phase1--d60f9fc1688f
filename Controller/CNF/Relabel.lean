module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Basic

@[expose] public section

/-! Renaming preserves assignments, restriction fixes an assignment, and
projection quantifies hidden assignments. These operations have separate
contracts; projection does not assert a bijection of full models.
-/

namespace Controller.CNF

abbrev relabel (r : α → β) (f : Formula α) : Formula β := Controller.CNF.OrderedFormula.relabel r f

theorem satisfies_relabel (r : α → β) (a : β → Bool) (f : Formula α) :
    Satisfies a (relabel r f) ↔ Satisfies (a ∘ r) f := by
  simp only [satisfies_iff_stdSat, Controller.CNF.OrderedFormula.Sat, relabel, Controller.CNF.OrderedFormula.eval_relabel]

theorem unsatisfiable_relabel_iff {r : α → β} (hr : Function.Injective r)
    (f : Formula α) : Unsatisfiable (relabel r f) ↔ Unsatisfiable f := by
  rw [unsatisfiable_iff_stdUnsat, unsatisfiable_iff_stdUnsat]
  exact Controller.CNF.OrderedFormula.unsat_relabel_iff (fun _ _ h => hr h)

theorem satisfiable_relabel_equiv (e : α ≃ β) (f : Formula α) :
    Satisfiable (relabel e f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a ∘ e, (satisfies_relabel e a f).mp ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨a ∘ e.symm, (satisfies_relabel e (a ∘ e.symm) f).mpr ?_⟩
    simpa [Function.comp_def] using ha

/-- A false phase complements the renamed variable; a true phase preserves it. -/
def signedLiteral (r : α → β) (phase : α → Bool) (l : Literal α) : Literal β :=
  (r l.1, phase l.1 == l.2)

def signedPullback (r : α → β) (phase : α → Bool) (a : β → Bool) : α → Bool :=
  fun i => a (r i) == phase i

theorem literalHolds_signedLiteral (r : α → β) (phase : α → Bool)
    (a : β → Bool) (l : Literal α) :
    LiteralHolds a (signedLiteral r phase l) ↔
      LiteralHolds (signedPullback r phase a) l := by
  rcases l with ⟨i, p⟩
  simp only [LiteralHolds, signedLiteral, signedPullback]
  cases p <;> cases phase i <;> cases a (r i) <;>
    decide

theorem clauseHolds_signedLiteral (r : α → β) (phase : α → Bool)
    (a : β → Bool) (c : Clause α) :
    ClauseHolds a (c.map (signedLiteral r phase)) ↔
      ClauseHolds (signedPullback r phase a) c := by
  constructor
  · rintro ⟨l, hl, ha⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
    exact ⟨k, hk, (literalHolds_signedLiteral r phase a k).mp ha⟩
  · rintro ⟨l, hl, ha⟩
    exact ⟨signedLiteral r phase l, List.mem_map.mpr ⟨l, hl, rfl⟩,
      (literalHolds_signedLiteral r phase a l).mpr ha⟩

def signedRelabel (r : α → β) (phase : α → Bool) (f : Formula α) : Formula β :=
  ⟨f.clauses.map (List.map (signedLiteral r phase))⟩

theorem satisfies_signedRelabel (r : α → β) (phase : α → Bool)
    (a : β → Bool) (f : Formula α) :
    Satisfies a (signedRelabel r phase f) ↔ Satisfies (signedPullback r phase a) f := by
  constructor
  · intro h c hc
    apply (clauseHolds_signedLiteral r phase a c).mp
    exact h _ (Array.mem_map.mpr ⟨c, hc, rfl⟩)
  · intro h c hc
    obtain ⟨d, hd, rfl⟩ := Array.mem_map.mp hc
    exact (clauseHolds_signedLiteral r phase a d).mpr (h d hd)

theorem signedPullback_inverse (e : α ≃ β) (phase : α → Bool) (a : α → Bool) :
    signedPullback e phase (fun i => a (e.symm i) == phase (e.symm i)) = a := by
  funext i
  simp only [signedPullback, Equiv.symm_apply_apply]
  cases a i <;> cases phase i <;> rfl

theorem satisfiable_signedRelabel_equiv (e : α ≃ β) (phase : α → Bool)
    (f : Formula α) : Satisfiable (signedRelabel e phase f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨signedPullback e phase a, (satisfies_signedRelabel e phase a f).mp ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a (e.symm i) == phase (e.symm i), ?_⟩
    rw [satisfies_signedRelabel, signedPullback_inverse]
    exact ha

def toNatFormula (f : FiniteFormula v) : Formula Nat := relabel Fin.val f

def restrictNat (a : Nat → Bool) : Fin v → Bool := fun i => a i.val

def extendNat (a : Fin v → Bool) : Nat → Bool :=
  fun i => if h : i < v then a ⟨i, h⟩ else false

@[simp] theorem restrictNat_extendNat (a : Fin v → Bool) : restrictNat (extendNat a) = a := by
  funext i
  simp [restrictNat, extendNat, i.isLt]

theorem satisfies_toNatFormula (a : Nat → Bool) (f : FiniteFormula v) :
    Satisfies a (toNatFormula f) ↔ Satisfies (restrictNat a) f := by
  exact satisfies_relabel Fin.val a f

theorem unsatisfiable_toNatFormula (f : FiniteFormula v) :
    Unsatisfiable (toNatFormula f) ↔ Unsatisfiable f :=
  unsatisfiable_relabel_iff (fun _ _ h => Fin.ext h) f

/-- Variable zero is encoded as DIMACS variable one; zero is a terminator. -/
def encodeDimacs (l : Literal (Fin v)) : Int :=
  if l.2 then Int.ofNat (l.1.val + 1) else Int.negSucc l.1.val

def decodeDimacs (v : Nat) : Int → Option (Literal (Fin v))
  | .ofNat 0 => none
  | .ofNat (k + 1) => if h : k < v then some (⟨k, h⟩, true) else none
  | .negSucc k => if h : k < v then some (⟨k, h⟩, false) else none

@[simp] theorem decodeDimacs_zero (v : Nat) : decodeDimacs v 0 = none := rfl

@[simp] theorem decodeDimacs_encodeDimacs (l : Literal (Fin v)) :
    decodeDimacs v (encodeDimacs l) = some l := by
  rcases l with ⟨i, p⟩
  cases p
  · change decodeDimacs v (Int.negSucc i.val) = some (i, false)
    simp only [decodeDimacs, dite_eq_left i.isLt]
  · change decodeDimacs v (Int.ofNat (i.val + 1)) = some (i, true)
    simp only [decodeDimacs, dite_eq_left i.isLt]

theorem encodeDimacs_of_decode {z : Int} {l : Literal (Fin v)}
    (h : decodeDimacs v z = some l) : encodeDimacs l = z := by
  cases z with
  | ofNat k =>
    cases k with
    | zero => simp [decodeDimacs] at h
    | succ k =>
      by_cases hk : k < v
      · simp [decodeDimacs, hk] at h
        subst l
        rfl
      · simp [decodeDimacs, hk] at h
  | negSucc k =>
    by_cases hk : k < v
    · simp [decodeDimacs, hk] at h
      subst l
      rfl
    · simp [decodeDimacs, hk] at h

@[simp] theorem encodeDimacs_natAbs (l : Literal (Fin v)) :
    (encodeDimacs l).natAbs = l.1.val + 1 := by
  rcases l with ⟨i, p⟩
  cases p <;> rfl

theorem encodeDimacs_ne_zero (l : Literal (Fin v)) : encodeDimacs l ≠ 0 := by
  intro h
  have := encodeDimacs_natAbs l
  simp [h] at this

theorem encodeDimacs_injective : Function.Injective (@encodeDimacs v) := by
  intro l k h
  have := congrArg (decodeDimacs v) h
  simpa using this

@[simp] theorem encodeDimacs_negate (l : Literal (Fin v)) :
    encodeDimacs (negate l) = -encodeDimacs l := by
  rcases l with ⟨i, p⟩
  cases p <;> rfl

def combine (a : α → Bool) (b : β → Bool) : Sum α β → Bool := Sum.elim a b

def Projects (f : Formula (Sum α β)) (a : α → Bool) : Prop :=
  ∃ b, Satisfies (combine a b) f

def ExactProjection (f : Formula (Sum α β)) (g : Formula α) : Prop :=
  ∀ a, Projects f a ↔ Satisfies a g

theorem combine_restrictions (a : Sum α β → Bool) :
    combine (a ∘ Sum.inl) (a ∘ Sum.inr) = a := by
  funext i
  cases i <;> rfl

theorem satisfiable_iff_projects (f : Formula (Sum α β)) :
    Satisfiable f ↔ ∃ a, Projects f a := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ∘ Sum.inl, a ∘ Sum.inr, ?_⟩
    simpa [combine_restrictions] using ha
  · rintro ⟨a, b, h⟩
    exact ⟨combine a b, h⟩

theorem ExactProjection.satisfiable_iff {f : Formula (Sum α β)} {g : Formula α}
    (h : ExactProjection f g) : Satisfiable f ↔ Satisfiable g := by
  rw [satisfiable_iff_projects]
  exact exists_congr h

/-- `none` means the fixed hidden assignment already satisfies the clause. -/
def restrictClause (b : β → Bool) : Clause (Sum α β) → Option (Clause α)
  | [] => some []
  | (Sum.inl i, p) :: c => (restrictClause b c).map ((i, p) :: ·)
  | (Sum.inr i, p) :: c => if b i = p then none else restrictClause b c

def restrictedClauseHolds (a : α → Bool) : Option (Clause α) → Prop
  | none => True
  | some c => ClauseHolds a c

theorem restrictClause_correct (a : α → Bool) (b : β → Bool)
    (c : Clause (Sum α β)) :
    restrictedClauseHolds a (restrictClause b c) ↔ ClauseHolds (combine a b) c := by
  induction c with
  | nil => simp [restrictClause, restrictedClauseHolds]
  | cons l c ih =>
    rcases l with ⟨i, p⟩
    cases i with
    | inl i =>
      cases h : restrictClause b c with
      | none =>
        simp [h, restrictedClauseHolds] at ih
        simp [restrictClause, h, restrictedClauseHolds, ih]
      | some d =>
        simp only [h, restrictedClauseHolds] at ih
        simp [restrictClause, h, restrictedClauseHolds, ih, LiteralHolds, combine]
    | inr i =>
      by_cases hp : b i = p
      · simp [restrictClause, hp, restrictedClauseHolds, LiteralHolds, combine]
      · simp [restrictClause, hp, ih, LiteralHolds, combine]

def restrictFormula (b : β → Bool) (f : Formula (Sum α β)) : Formula α :=
  ⟨f.clauses.filterMap (restrictClause b)⟩

theorem satisfies_restrictFormula (a : α → Bool) (b : β → Bool)
    (f : Formula (Sum α β)) :
    Satisfies a (restrictFormula b f) ↔ Satisfies (combine a b) f := by
  constructor
  · intro h c hc
    apply (restrictClause_correct a b c).mp
    cases hr : restrictClause b c with
    | none => trivial
    | some d =>
      exact h d (Array.mem_filterMap.mpr ⟨c, hc, hr⟩)
  · intro h d hd
    obtain ⟨c, hc, hr⟩ := Array.mem_filterMap.mp hd
    have := (restrictClause_correct a b c).mpr (h c hc)
    simpa [hr, restrictedClauseHolds] using this

theorem projects_iff_restrictFormula (a : α → Bool) (f : Formula (Sum α β)) :
    Projects f a ↔ ∃ b, Satisfies a (restrictFormula b f) := by
  simp [Projects, satisfies_restrictFormula]

end Controller.CNF
