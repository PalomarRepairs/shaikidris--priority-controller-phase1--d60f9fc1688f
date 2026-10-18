module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Std.Sat.CNF
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-! CNF semantics with an explicit declared variable type.

Clauses use the standard `(variable, polarity)` convention: a literal is true
when the assignment agrees with its polarity. Formula rows remain an array;
normalizing literals never merges duplicate input rows or changes their IDs.
-/

namespace Controller.CNF

abbrev Literal (α : Type*) := Std.Sat.Literal α

/-
The ordered-list CNF API below is adapted from Lean 4.33.0, Std/Sat/CNF/Basic.lean
and Std/Sat/CNF/Relabel.lean.
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/--
A clause in a OrderedFormula.

The literal `(i, b)` is satisfied if the assignment to `i` agrees with `b`.
-/
abbrev OrderedFormula.Clause (α : Type u) : Type u := List (Literal α)

/--
A OrderedFormula formula.

Literals are identified by members of `α`.
-/
structure OrderedFormula (α : Type u) where
  clauses : Array (OrderedFormula.Clause α)

namespace OrderedFormula

/--
Evaluating a `Clause` with respect to an assignment `a`.
-/
def Clause.eval (a : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => a i == n

@[simp] theorem Clause.eval_nil (a : α → Bool) : Clause.eval a [] = false := rfl
@[simp] theorem Clause.eval_cons (a : α → Bool) :
    Clause.eval a (i :: c) = (a i.1 == i.2 || Clause.eval a c) := rfl

/--
Evaluating a `OrderedFormula` formula with respect to an assignment `a`.
-/
def eval (a : α → Bool) (f : OrderedFormula α) : Bool := f.clauses.all fun c => c.eval a

@[inline]
def empty : OrderedFormula α := { clauses := #[] }

@[inline]
def emptyWithCapacity (n : Nat) : OrderedFormula α := { clauses := .emptyWithCapacity n }

@[inline]
def add (c : OrderedFormula.Clause α) (f : OrderedFormula α) : OrderedFormula α := { f with clauses := f.clauses.push c }

@[inline]
def append (f1 f2 : OrderedFormula α) : OrderedFormula α :=
  { clauses := f1.clauses ++ f2.clauses }

instance : Append (OrderedFormula α) where
  append := append

@[simp] theorem eval_empty (a : α → Bool) : eval a .empty = true := by simp [eval, empty]
@[simp] theorem eval_add (a : α → Bool) : eval a (f.add c) = (c.eval a && eval a f) := by
  rw [Bool.and_comm]
  simp [add, eval]

@[simp] theorem eval_append (a : α → Bool) (f1 f2 : OrderedFormula α) :
    eval a (f1 ++ f2) = (eval a f1 && eval a f2) := Array.all_append

def Sat (a : α → Bool) (f : OrderedFormula α) : Prop := eval a f = true
def Unsat (f : OrderedFormula α) : Prop := ∀ a, eval a f = false

theorem sat_def (a : α → Bool) (f : OrderedFormula α) : Sat a f ↔ (eval a f = true) := by rfl
theorem unsat_def (f : OrderedFormula α) : Unsat f ↔ (∀ a, eval a f = false) := by rfl


@[simp] theorem not_unsat_empty : ¬Unsat (.empty : OrderedFormula α) :=
  fun h => by simp [unsat_def] at h

@[simp] theorem sat_empty {assign : α → Bool} : Sat assign (.empty : OrderedFormula α) := by
  simp [sat_def]

@[simp] theorem unsat_add_nil {g : OrderedFormula α} : Unsat (g.add []) := by
  simp [unsat_def]

namespace Clause

/--
Variable `v` occurs in `Clause` `c`.
-/
def Mem (v : α) (c : Clause α) : Prop := (v, false) ∈ c ∨ (v, true) ∈ c

instance {v : α} {c : Clause α} [DecidableEq α] : Decidable (Mem v c) :=
  inferInstanceAs <| Decidable (_ ∨ _)

@[simp] theorem not_mem_nil {v : α} : ¬Mem v ([] : Clause α) := by simp [Mem]
@[simp] theorem mem_cons {v : α} : Mem v (l :: c : Clause α) ↔ (v = l.1 ∨ Mem v c) := by
  rcases l with ⟨b, (_|_)⟩
  · simp [Mem, or_assoc]
  · simp [Mem]
    rw [or_left_comm]

theorem mem_of (h : (v, p) ∈ c) : Mem v c := by
  cases p
  · left; exact h
  · right; exact h

theorem eval_congr (a1 a2 : α → Bool) (c : Clause α) (hw : ∀ i, Mem i c → a1 i = a2 i) :
    eval a1 c = eval a2 c := by
  induction c
  case nil => rfl
  case cons i c ih =>
    simp only [eval_cons]
    rw [ih, hw]
    · rcases i with ⟨b, (_|_)⟩ <;> simp [Mem]
    · intro j h
      apply hw
      rcases h with h | h
      · left
        apply List.mem_cons_of_mem _ h
      · right
        apply List.mem_cons_of_mem _ h

end Clause

/--
`Clause` `c` occurs in `OrderedFormula` formula `f`.
-/
def Mem (f : OrderedFormula α) (c : Clause α) : Prop := c ∈ f.clauses

instance : Membership (Clause α) (OrderedFormula α) where
  mem := Mem

instance {c : Clause α} {f : OrderedFormula α} [DecidableEq α] : Decidable (c ∈ f) :=
    inferInstanceAs <| Decidable (c ∈ f.clauses)

/--
Variable `v` occurs in `OrderedFormula` formula `f`.
-/
def VarMem (v : α) (f : OrderedFormula α) : Prop := ∃ c, c ∈ f.clauses ∧ c.Mem v

instance {v : α} {f : OrderedFormula α} [DecidableEq α] : Decidable (VarMem v f) :=
  inferInstanceAs <| Decidable (∃ _, _)

theorem Internal.any_not_isEmpty_iff_exists_mem {f : OrderedFormula α} :
    (f.clauses.any fun c => !List.isEmpty c) = true ↔ ∃ v, VarMem v f := by
  simp only [Array.any_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, VarMem,
    Clause.Mem]
  constructor
  · intro h
    rcases h with ⟨idx, ⟨hclause1, hclause2⟩⟩
    rcases hclause2 with ⟨lit, hlit⟩
    exists lit.fst, f.clauses[idx]
    constructor
    · simp
    · rcases lit with ⟨_, ⟨_ | _⟩⟩ <;> simp_all
  · intro h
    rcases h with ⟨lit, clause, ⟨hclause1, hclause2⟩⟩
    rw [Array.mem_iff_getElem] at hclause1
    rcases hclause1 with ⟨i, h, hi⟩
    cases hclause2 with
    | inl hl =>
      exists i, h, (lit, false)
      rw [hi]
      assumption
    | inr hr =>
      exists i, h, (lit, true)
      rw [hi]
      assumption

@[no_expose]
instance {f : OrderedFormula α} [DecidableEq α] : Decidable (∃ v, VarMem v f) :=
  decidable_of_iff (f.clauses.any fun c => !c.isEmpty) Internal.any_not_isEmpty_iff_exists_mem

theorem not_VarMem_empty {v : α} : ¬VarMem v (.empty : OrderedFormula α) := by simp [VarMem, empty]

@[local simp] theorem VarMem_add {v : α} {c} {f : OrderedFormula α} :
    VarMem v (f.add c : OrderedFormula α) ↔ (Clause.Mem v c ∨ VarMem v f) := by
  simp only [VarMem, add, Array.mem_push]
  constructor
  · intro h
    rcases h with ⟨c, ⟨hc1 | hc1, hc2⟩⟩
    · right
      exists c
    · simp_all
  · intro h
    rcases h with hc1 | ⟨c, hc1, hc2⟩
    · exists c
      simp [hc1]
    · exists c
      simp [hc1, hc2]

theorem VarMem_of (h : c ∈ f) (w : Clause.Mem v c) : VarMem v f := by
  apply Exists.intro c
  constructor <;> assumption

theorem Internal.mem_iff {f : OrderedFormula α} : c ∈ f ↔ c ∈ f.clauses := by
  rfl

theorem Internal.clauses_append {f1 f2 : OrderedFormula α} : (f1 ++ f2).clauses = f1.clauses ++ f2.clauses := rfl

theorem Internal.ext_iff {f1 f2 : OrderedFormula α} : f1 = f2 ↔ f1.clauses = f2.clauses := by
  cases f1; cases f2; simp

@[simp]
theorem emptyWithCapacity_eq_empty (n : Nat) :
    OrderedFormula.emptyWithCapacity n = (OrderedFormula.empty : OrderedFormula α) := by
  simp [empty, emptyWithCapacity]

@[simp] theorem VarMem_append {v : α} {f1 f2 : OrderedFormula α} :
    VarMem v (f1 ++ f2) ↔ VarMem v f1 ∨ VarMem v f2 := by
  simp [VarMem, Array.mem_append, Internal.clauses_append]
  constructor
  · rintro ⟨c, (mf1 | mf2), mc⟩
    · left
      exact ⟨c, mf1, mc⟩
    · right
      exact ⟨c, mf2, mc⟩
  · rintro (⟨c, mf1, mc⟩ | ⟨c, mf2, mc⟩)
    · exact ⟨c, Or.inl mf1, mc⟩
    · exact ⟨c, Or.inr mf2, mc⟩

theorem eval_congr (a1 a2 : α → Bool) (f : OrderedFormula α) (hw : ∀ v, VarMem v f → a1 v = a2 v) :
    eval a1 f = eval a2 f := by
  rcases f with ⟨clauses⟩
  simp only [eval]
  rw [Bool.eq_iff_iff, Array.all_eq_true, Array.all_eq_true]
  constructor
  · intro h x hx
    rw [Clause.eval_congr a2 a1 clauses[x]]
    · exact h x hx
    · intro i hi
      symm
      exact hw _ (VarMem_of (by simp [Internal.mem_iff]) hi)
  · intro h x hx
    rw [Clause.eval_congr a1 a2 clauses[x]]
    · exact h x hx
    · intro i hi
      exact hw _ (VarMem_of (by simp [Internal.mem_iff]) hi)

end OrderedFormula

namespace OrderedFormula

namespace Clause

/--
Change the literal type in a `Clause` from `α` to `β` by using `r`.
-/
def relabel (r : α → β) (c : Clause α) : Clause β := c.map (fun (i, n) => (r i, n))

@[simp]
theorem relabel_nil (r : α → β) : Clause.relabel r [] = [] := by simp [relabel]

@[simp] theorem eval_relabel {r : α → β} {a : β → Bool} {c : Clause α} :
    (relabel r c).eval a = c.eval (a ∘ r) := by
  induction c <;> simp_all [relabel]

@[simp] theorem relabel_id' : relabel (id : α → α) = id := by funext; simp [relabel]

theorem relabel_congr {c : Clause α} {r1 r2 : α → β} (hw : ∀ v, Mem v c → r1 v = r2 v) :
    relabel r1 c = relabel r2 c := by
  simp only [relabel]
  rw [List.map_congr_left]
  intro ⟨v, p⟩ h
  congr
  apply hw _ (mem_of h)

-- We need the unapplied equality later.
@[simp] theorem relabel_relabel' : relabel r1 ∘ relabel r2 = relabel (r1 ∘ r2) := by
  funext i
  simp only [Function.comp_apply, relabel, List.map_map]
  rfl

end Clause

/-! ### Relabelling

It is convenient to be able to construct a OrderedFormula using a more complicated literal type,
but eventually we need to embed in `Nat`.
-/

/--
Change the literal type in a `OrderedFormula` formula from `α` to `β` by using `r`.
-/
def relabel (r : α → β) (f : OrderedFormula α) : OrderedFormula β := ⟨f.clauses.map (Clause.relabel r)⟩

@[simp] theorem relabel_empty {r : α → β} : relabel r .empty = .empty := by
  simp [relabel, empty]

@[simp] theorem relabel_add {r : α → β} :
    relabel r (f.add c) = (relabel r f).add (c.relabel r) := by
  simp [relabel, add]

@[simp] theorem eval_relabel (r : α → β) (a : β → Bool) (f : OrderedFormula α) :
    (relabel r f).eval a = f.eval (a ∘ r) := by
  unfold relabel eval
  simp

@[simp] theorem relabel_append : relabel r (f1 ++ f2) = relabel r f1 ++ relabel r f2 := by
  unfold relabel
  simp [Internal.clauses_append, Internal.ext_iff]

@[simp] theorem relabel_relabel : relabel r1 (relabel r2 f) = relabel (r1 ∘ r2) f := by
  simp only [relabel, Array.map_map, Clause.relabel_relabel']

@[simp] theorem relabel_id : relabel id x = x := by simp [relabel]

theorem relabel_congr {f : OrderedFormula α} {r1 r2 : α → β} (hw : ∀ v, VarMem v f → r1 v = r2 v) :
    relabel r1 f = relabel r2 f := by
  dsimp only [relabel]
  rw [Array.map_congr_left]
  intro c h
  apply Clause.relabel_congr
  intro v m
  exact hw _ (VarMem_of h m)

theorem sat_relabel {f : OrderedFormula α} (h : Sat (r1 ∘ r2) f) : Sat r1 (relabel r2 f) := by
  simp_all [sat_def]

theorem unsat_relabel {f : OrderedFormula α} (r : α → β) (h : Unsat f) :
    Unsat (relabel r f) := by
  simp_all [unsat_def]

private theorem nonempty_or_impossible (f : OrderedFormula α) :
    Nonempty α ∨ ∃ n, f = ⟨Array.replicate n []⟩ := by
  apply Classical.byContradiction
  intro h
  simp only [Internal.ext_iff, not_or, not_exists] at h
  rcases h with ⟨h1, h2⟩
  specialize h2 f.clauses.size
  simp only [Array.eq_replicate_iff, true_and, Classical.not_forall] at h2
  rcases h2 with ⟨x, ⟨_, hx⟩⟩
  apply h1
  apply Nonempty.intro
  exact (x.head hx).fst

theorem unsat_relabel_iff {f : OrderedFormula α} {r : α → β}
    (hw : ∀ {v1 v2}, VarMem v1 f → VarMem v2 f → r v1 = r v2 → v1 = v2) :
    Unsat (relabel r f) ↔ Unsat f := by
  rcases nonempty_or_impossible f with (⟨⟨a₀⟩⟩ | ⟨n, rfl⟩)
  · refine ⟨fun h => ?_, unsat_relabel r⟩
    have em := Classical.propDecidable
    let g : β → α := fun b =>
      if h : ∃ a, VarMem a f ∧ r a = b then h.choose else a₀
    have h' := unsat_relabel g h
    suffices w : relabel g (relabel r f) = f by
      rwa [w] at h'
    have : ∀ a, VarMem a f → g (r a) = a := by
      intro v h
      dsimp [g]
      rw [dite_eq_left ⟨v, h, rfl⟩]
      apply hw _ h
      · exact (Exists.choose_spec (⟨v, h, rfl⟩ : ∃ a', VarMem a' f ∧ r a' = r v)).2
      · exact (Exists.choose_spec (⟨v, h, rfl⟩ : ∃ a', VarMem a' f ∧ r a' = r v)).1
    rw [relabel_relabel, relabel_congr, relabel_id]
    exact this
  · cases n
    · rw [Array.replicate_zero, ← OrderedFormula.empty]
      simp
    · rw [Array.replicate_succ, ← OrderedFormula.add]
      simp

end OrderedFormula

abbrev Clause (α : Type*) := Controller.CNF.OrderedFormula.Clause α
abbrev Formula (α : Type*) := Controller.CNF.OrderedFormula α
abbrev FiniteFormula (v : Nat) := Formula (Fin v)

namespace OrderedFormula

def toStd (formula : OrderedFormula α) : Std.Sat.CNF α :=
  ⟨formula.clauses.map Std.Sat.CNF.Clause.ofLiterals⟩

def ofStd (formula : Std.Sat.CNF α) : OrderedFormula α :=
  ⟨formula.clauses.map Std.Sat.CNF.Clause.literals⟩

theorem list_roundtrip (formula : OrderedFormula α) : ofStd (toStd formula) = formula := by
  cases formula
  simp [ofStd, toStd, Array.map_map, Function.comp_def]

theorem std_roundtrip (formula : Std.Sat.CNF α) : toStd (ofStd formula) = formula := by
  cases formula
  simp [ofStd, toStd, Array.map_map, Function.comp_def]

def formulaEquiv : OrderedFormula α ≃ Std.Sat.CNF α where
  toFun := toStd
  invFun := ofStd
  left_inv := list_roundtrip
  right_inv := std_roundtrip

theorem row_count (formula : OrderedFormula α) : (toStd formula).clauses.size = formula.clauses.size := by
  simp [toStd]

theorem row_literals (formula : OrderedFormula α) (index : Nat) (valid : index < formula.clauses.size) :
    ((toStd formula).clauses[index]'(by simpa [toStd] using valid)).literals = formula.clauses[index] := by
  simp [toStd]

theorem clause_size (clause : List (Std.Sat.Literal α)) :
    (Std.Sat.CNF.Clause.ofLiterals clause).size = clause.length := by
  rw [← Std.Sat.CNF.Clause.length_literals, Std.Sat.CNF.Clause.literals_ofLiterals]

theorem literal_count (formula : OrderedFormula α) :
    ((toStd formula).clauses.toList.map Std.Sat.CNF.Clause.size).sum =
      (formula.clauses.toList.map List.length).sum := by
  simp [toStd, List.map_map, Function.comp_def, clause_size]

theorem clause_sat (assignment : α → Bool) (clause : List (Std.Sat.Literal α)) :
    Std.Sat.CNF.Clause.Sat assignment (Std.Sat.CNF.Clause.ofLiterals clause) ↔
      ∃ literal ∈ clause, assignment literal.1 = literal.2 := by
  rw [Std.Sat.CNF.Clause.sat_iff_exists_mem_eq]
  simp only [← Std.Sat.CNF.Clause.mem_literals_iff, Std.Sat.CNF.Clause.literals_ofLiterals]

theorem formula_sat (assignment : α → Bool) (formula : OrderedFormula α) :
    Std.Sat.CNF.Sat assignment (toStd formula) ↔
      ∀ clause ∈ formula.clauses, ∃ literal ∈ clause, assignment literal.1 = literal.2 := by
  rw [Std.Sat.CNF.sat_iff_all_mem_sat]
  constructor
  · intro satisfied clause member
    have present : Std.Sat.CNF.Clause.ofLiterals clause ∈ (toStd formula).clauses :=
      Array.mem_map.mpr ⟨clause, member, rfl⟩
    exact (clause_sat assignment clause).mp (satisfied _ (Std.Sat.CNF.Internal.mem_iff.mpr present))
  · intro satisfied clause member
    have present : clause ∈ formula.clauses.map Std.Sat.CNF.Clause.ofLiterals :=
      Std.Sat.CNF.Internal.mem_iff.mp member
    obtain ⟨original, rowMember, rfl⟩ := Array.mem_map.mp present
    exact (clause_sat assignment original).mpr (satisfied original rowMember)

end OrderedFormula

abbrev negate (l : Literal α) : Literal α := Std.Sat.Literal.negate l

def LiteralHolds (a : α → Bool) (l : Literal α) : Prop := a l.1 = l.2

def ClauseHolds (a : α → Bool) (c : Clause α) : Prop :=
  ∃ l, l ∈ c ∧ LiteralHolds a l

def Satisfies (a : α → Bool) (f : Formula α) : Prop :=
  ∀ c, c ∈ f.clauses → ClauseHolds a c

def Satisfiable (f : Formula α) : Prop := ∃ a, Satisfies a f

def Unsatisfiable (f : Formula α) : Prop := ¬Satisfiable f

def Entails (f : Formula α) (c : Clause α) : Prop :=
  ∀ a, Satisfies a f → ClauseHolds a c

@[simp] theorem negate_negate (l : Literal α) : negate (negate l) = l := by
  rcases l with ⟨i, p⟩
  cases p <;> rfl

@[simp] theorem literalHolds_negate (a : α → Bool) (l : Literal α) :
    LiteralHolds a (negate l) ↔ ¬LiteralHolds a l := by
  rcases l with ⟨i, p⟩
  cases p <;> cases a i <;> simp [LiteralHolds, negate, Std.Sat.Literal.negate]

@[simp] theorem clauseHolds_nil (a : α → Bool) : ¬ClauseHolds a [] := by
  simp [ClauseHolds]

@[simp] theorem clauseHolds_cons (a : α → Bool) (l : Literal α) (c : Clause α) :
    ClauseHolds a (l :: c) ↔ LiteralHolds a l ∨ ClauseHolds a c := by
  simp [ClauseHolds, or_and_right, exists_or]

@[simp] theorem clauseHolds_append (a : α → Bool) (c d : Clause α) :
    ClauseHolds a (c ++ d) ↔ ClauseHolds a c ∨ ClauseHolds a d := by
  simp [ClauseHolds, or_and_right, exists_or]

theorem clauseHolds_iff_eval (a : α → Bool) (c : Clause α) :
    ClauseHolds a c ↔ Controller.CNF.OrderedFormula.Clause.eval a c = true := by
  simp [ClauseHolds, LiteralHolds, Controller.CNF.OrderedFormula.Clause.eval, List.any_eq_true]

theorem satisfies_iff_stdSat (a : α → Bool) (f : Formula α) :
    Satisfies a f ↔ Controller.CNF.OrderedFormula.Sat a f := by
  simp only [Satisfies, Controller.CNF.OrderedFormula.Sat, Controller.CNF.OrderedFormula.eval,
    Array.all_eq_true_iff_forall_mem, clauseHolds_iff_eval]

theorem unsatisfiable_iff_stdUnsat (f : Formula α) :
    Unsatisfiable f ↔ Controller.CNF.OrderedFormula.Unsat f := by
  simp only [Unsatisfiable, Satisfiable, not_exists, satisfies_iff_stdSat,
    Controller.CNF.OrderedFormula.Sat, Controller.CNF.OrderedFormula.Unsat, Bool.not_eq_true]

def ClauseSubset (c d : Clause α) : Prop := ∀ l, l ∈ c → l ∈ d

def SameLiterals (c d : Clause α) : Prop := ∀ l, l ∈ c ↔ l ∈ d

theorem clauseHolds_mono {a : α → Bool} {c d : Clause α}
    (h : ClauseSubset c d) (hc : ClauseHolds a c) : ClauseHolds a d := by
  rcases hc with ⟨l, hl, ha⟩
  exact ⟨l, h l hl, ha⟩

theorem clauseHolds_congr {a : α → Bool} {c d : Clause α}
    (h : SameLiterals c d) : ClauseHolds a c ↔ ClauseHolds a d := by
  constructor
  · exact clauseHolds_mono (fun l hl => (h l).mp hl)
  · exact clauseHolds_mono (fun l hl => (h l).mpr hl)

theorem tautology_holds (a : α → Bool) {c : Clause α} {l : Literal α}
    (hl : l ∈ c) (hn : negate l ∈ c) : ClauseHolds a c := by
  by_cases h : LiteralHolds a l
  · exact ⟨l, hl, h⟩
  · exact ⟨negate l, hn, (literalHolds_negate a l).mpr h⟩

def normalizeClause [DecidableEq α] (c : Clause α) : Clause α := c.eraseDups

@[simp] theorem mem_normalizeClause [DecidableEq α] (l : Literal α) (c : Clause α) :
    l ∈ normalizeClause c ↔ l ∈ c := by
  exact List.mem_eraseDups

@[simp] theorem clauseHolds_normalizeClause [DecidableEq α]
    (a : α → Bool) (c : Clause α) : ClauseHolds a (normalizeClause c) ↔ ClauseHolds a c := by
  exact clauseHolds_congr (fun l => mem_normalizeClause l c)

def normalizeFormula [DecidableEq α] (f : Formula α) : Formula α :=
  ⟨f.clauses.map normalizeClause⟩

@[simp] theorem normalizeFormula_size [DecidableEq α] (f : Formula α) :
    (normalizeFormula f).clauses.size = f.clauses.size := by
  simp [normalizeFormula]

theorem normalizeFormula_row [DecidableEq α] (f : Formula α)
    (i : Nat) (hi : i < f.clauses.size) :
    (normalizeFormula f).clauses[i]'(by simpa using hi) = normalizeClause f.clauses[i] := by
  simp [normalizeFormula]

@[simp] theorem satisfies_normalizeFormula [DecidableEq α]
    (a : α → Bool) (f : Formula α) : Satisfies a (normalizeFormula f) ↔ Satisfies a f := by
  simp [Satisfies, normalizeFormula]

def ofClauses (cs : List (Clause α)) : Formula α := ⟨cs.toArray⟩

@[simp] theorem satisfies_ofClauses (a : α → Bool) (cs : List (Clause α)) :
    Satisfies a (ofClauses cs) ↔ ∀ c ∈ cs, ClauseHolds a c := by
  simp [Satisfies, ofClauses]

@[simp] theorem clauseHolds_iff_finset [DecidableEq α]
    (a : α → Bool) (c : Clause α) :
    ClauseHolds a c ↔ ∃ l ∈ c.toFinset, LiteralHolds a l := by
  simp [ClauseHolds]

theorem satisfies_iff_rows (a : α → Bool) (f : Formula α) :
    Satisfies a f ↔ ∀ i : Fin f.clauses.size, ClauseHolds a f.clauses[i] := by
  constructor
  · intro h i
    exact h _ (Array.getElem_mem ..)
  · intro h c hc
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc
    exact h ⟨i, hi⟩

@[simp] theorem satisfies_empty (a : α → Bool) :
    Satisfies a (Controller.CNF.OrderedFormula.empty : Formula α) := by
  simp [Satisfies, Controller.CNF.OrderedFormula.empty]

theorem empty_satisfiable : Satisfiable (Controller.CNF.OrderedFormula.empty : Formula α) :=
  ⟨fun _ => false, satisfies_empty _⟩

theorem unsatisfiable_of_empty_row {f : Formula α} (h : [] ∈ f.clauses) :
    Unsatisfiable f := by
  rintro ⟨a, ha⟩
  exact clauseHolds_nil a (ha [] h)

theorem singleton_empty_unsatisfiable : Unsatisfiable (ofClauses [[]] : Formula α) := by
  apply unsatisfiable_of_empty_row
  simp [ofClauses]


/-- Packed-standard interoperability preserves the complete ordered formula. -/
theorem satisfies_iff_packedSat (a : α → Bool) (f : Formula α) :
    Satisfies a f ↔ Std.Sat.CNF.Sat a (OrderedFormula.toStd f) :=
  (OrderedFormula.formula_sat a f).symm

/-- Unsatisfiability transports through the formula equivalence. -/
theorem unsatisfiable_iff_packedUnsat (f : Formula α) :
    Unsatisfiable f ↔ Std.Sat.CNF.Unsat (OrderedFormula.toStd f) := by
  rw [Std.Sat.CNF.unsat_iff_not_sat]
  simp only [Unsatisfiable, Satisfiable, not_exists, satisfies_iff_packedSat]

end Controller.CNF
