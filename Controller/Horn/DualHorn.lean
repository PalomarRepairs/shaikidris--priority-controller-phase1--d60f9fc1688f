module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Basic

@[expose] public section

/-! Dual-Horn clauses after literal factoring. Duplicate negative occurrences
of one variable are permitted; tautologies are semantically unrestricted. -/
namespace Controller.Horn
open CNF

def Tautological (c : Clause α) : Prop := ∃ l, l ∈ c ∧ negate l ∈ c

def NegativeUnique (c : Clause α) : Prop :=
  ∀ l ∈ c, ∀ k ∈ c, l.2 = false → k.2 = false → l.1 = k.1

def DualHornClause (c : Clause α) : Prop := Tautological c ∨ NegativeUnique c

def DualHorn (f : Formula α) : Prop := ∀ c ∈ f.clauses, DualHornClause c

def Below (a b : α → Bool) : Prop := ∀ i, a i = true → b i = true

def join (a b : α → Bool) : α → Bool := fun i => a i || b i

theorem below_refl (a : α → Bool) : Below a a := fun _ h => h

theorem below_trans {a b c : α → Bool} (hab : Below a b) (hbc : Below b c) :
    Below a c := fun i hi => hbc i (hab i hi)

theorem below_antisymm {a b : α → Bool} (hab : Below a b) (hba : Below b a) : a = b := by
  funext i
  apply Bool.eq_iff_iff.mpr
  exact ⟨hab i, hba i⟩

@[simp] theorem negativeUnique_normalize [DecidableEq α] (c : Clause α) :
    NegativeUnique (normalizeClause c) ↔ NegativeUnique c := by
  simp [NegativeUnique]

@[simp] theorem tautological_normalize [DecidableEq α] (c : Clause α) :
    Tautological (normalizeClause c) ↔ Tautological c := by
  simp [Tautological]

@[simp] theorem dualHornClause_normalize [DecidableEq α] (c : Clause α) :
    DualHornClause (normalizeClause c) ↔ DualHornClause c := by
  simp [DualHornClause]

theorem below_join_left (a b : α → Bool) : Below a (join a b) := by
  intro i hi
  simp [join, hi]

theorem below_join_right (a b : α → Bool) : Below b (join a b) := by
  intro i hi
  simp [join, hi]

theorem clauseHolds_join {c : Clause α} (hc : DualHornClause c)
    {a b : α → Bool} (ha : ClauseHolds a c) (hb : ClauseHolds b c) :
    ClauseHolds (join a b) c := by
  rcases hc with ht | hn
  · obtain ⟨l, hl, hneg⟩ := ht
    exact tautology_holds _ hl hneg
  · obtain ⟨⟨i, p⟩, hl, hli⟩ := ha
    cases p with
    | true =>
      refine ⟨(i, true), hl, ?_⟩
      simp [LiteralHolds, join, LiteralHolds] at hli ⊢
      exact Or.inl hli
    | false =>
      by_cases hbi : b i = false
      · refine ⟨(i, false), hl, ?_⟩
        simp [LiteralHolds] at hli
        simp [LiteralHolds, join, hli, hbi]
      · have hbit : b i = true := Bool.eq_true_of_not_eq_false hbi
        obtain ⟨⟨j, q⟩, hk, hkj⟩ := hb
        cases q with
        | true =>
          refine ⟨(j, true), hk, ?_⟩
          simp only [LiteralHolds] at hkj ⊢
          simp [join, hkj]
        | false =>
          have hij : i = j := hn (i, false) hl (j, false) hk rfl rfl
          simp only [LiteralHolds] at hkj
          exact False.elim (Bool.false_ne_true (hkj.symm.trans (hij ▸ hbit)))

theorem satisfies_join {f : Formula α} (hf : DualHorn f) {a b : α → Bool}
    (ha : Satisfies a f) (hb : Satisfies b f) : Satisfies (join a b) f := by
  intro c hc
  exact clauseHolds_join (hf c hc) (ha c hc) (hb c hc)

@[simp] theorem dualHornClause_empty : DualHornClause ([] : Clause α) := by
  right
  simp [NegativeUnique]

@[simp] theorem dualHornClause_singleton (l : Literal α) : DualHornClause [l] := by
  right
  simp [NegativeUnique]

theorem dualHornClause_positive {c : Clause α} (h : ∀ l ∈ c, l.2 = true) :
    DualHornClause c := by
  right
  intro l hl k hk hlf _
  have : false = true := hlf.symm.trans (h l hl)
  exact False.elim (Bool.false_ne_true this)

end Controller.Horn
