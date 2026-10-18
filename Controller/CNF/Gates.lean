module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Relabel
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-! Complete native gate blocks.

The clause lists for AND, OR, NOT and binary XOR follow
`experiments/c432-family/selector_fault_family.py`, `Circuit.cnf`.
Both input and output literals may be signed. An alias uses the paper's
two-clause equality block. Empty AND is true and empty OR is false.
-/

namespace Controller.CNF

def literalValue (a : α → Bool) (l : Literal α) : Bool := a l.1 == l.2

@[simp] theorem literalValue_eq_true (a : α → Bool) (l : Literal α) :
    literalValue a l = true ↔ LiteralHolds a l := by simp [literalValue, LiteralHolds]

@[simp] theorem literalValue_eq_false (a : α → Bool) (l : Literal α) :
    literalValue a l = false ↔ ¬LiteralHolds a l := by simp [literalValue, LiteralHolds]

@[simp] theorem literalValue_negate (a : α → Bool) (l : Literal α) :
    literalValue a (negate l) = !literalValue a l := by
  rcases l with ⟨i, p⟩
  simp only [literalValue, negate, Std.Sat.Literal.negate]
  cases p <;> cases a i <;> rfl

theorem value_from_signed {x phase value : Bool} :
    (x == phase) = value ↔ x = (value == phase) := by
  cases x <;> cases phase <;> cases value <;> decide

theorem satisfies_append (a : α → Bool) (f g : Formula α) :
    Satisfies a (f ++ g) ↔ Satisfies a f ∧ Satisfies a g := by
  simp only [satisfies_iff_stdSat, Controller.CNF.OrderedFormula.Sat, Controller.CNF.OrderedFormula.eval_append, Bool.and_eq_true]

theorem clauseHolds_negated (a : α → Bool) (ls : List (Literal α)) :
    ClauseHolds a (ls.map negate) ↔ ∃ l ∈ ls, ¬LiteralHolds a l := by
  constructor
  · rintro ⟨l, hl, ha⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
    exact ⟨k, hk, (literalHolds_negate a k).mp ha⟩
  · rintro ⟨l, hl, ha⟩
    exact ⟨negate l, List.mem_map.mpr ⟨l, hl, rfl⟩, (literalHolds_negate a l).mpr ha⟩

theorem clauseHolds_of_toFinset_eq [DecidableEq α] (a : α → Bool) {c d : Clause α}
    (h : c.toFinset = d.toFinset) : ClauseHolds a c ↔ ClauseHolds a d := by
  apply clauseHolds_congr
  intro l
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp h l

inductive Gate (α : Type*) where
  | and (inputs : List (Literal α))
  | or (inputs : List (Literal α))
  | xor (left right : Literal α)
  | alias (input : Literal α)
  | not (input : Literal α)
  | constant (value : Bool)
  deriving DecidableEq, Repr

namespace Gate

def inputs : Gate α → List (Literal α)
  | .and ls | .or ls => ls
  | .xor l r => [l, r]
  | .alias l | .not l => [l]
  | .constant _ => []

def eval (a : α → Bool) : Gate α → Bool
  | .and ls => ls.all (literalValue a)
  | .or ls => ls.any (literalValue a)
  | .xor l r => literalValue a l ^^ literalValue a r
  | .alias l => literalValue a l
  | .not l => !literalValue a l
  | .constant b => b

def clauses (out : Literal α) : Gate α → List (Clause α)
  | .and ls => ls.map (fun l => [negate out, l]) ++ [out :: ls.map negate]
  | .or ls => ls.map (fun l => [out, negate l]) ++ [negate out :: ls]
  | .xor l r =>
      [[l, r, negate out], [negate l, negate r, negate out],
       [l, negate r, out], [negate l, r, out]]
  | .alias l => [[negate out, l], [out, negate l]]
  | .not l => [[out, l], [negate out, negate l]]
  | .constant b => [[if b then out else negate out]]

def block (out : Literal α) (g : Gate α) : Formula α := ofClauses (g.clauses out)

@[simp] theorem and_empty_clauses (out : Literal α) :
    clauses out (.and []) = [[out]] := rfl

@[simp] theorem or_empty_clauses (out : Literal α) :
    clauses out (.or []) = [[negate out]] := rfl

@[simp] theorem constant_true_clauses (out : Literal α) :
    clauses out (.constant true) = clauses out (.and []) := rfl

@[simp] theorem constant_false_clauses (out : Literal α) :
    clauses out (.constant false) = clauses out (.or []) := rfl

theorem and_block_correct (a : α → Bool) (out : Literal α) (ls : List (Literal α)) :
    Satisfies a (block out (.and ls)) ↔ literalValue a out = eval a (.and ls) := by
  simp only [block, clauses, satisfies_ofClauses, List.forall_mem_append,
    List.forall_mem_map, List.forall_mem_singleton, clauseHolds_cons, clauseHolds_nil,
    or_false, literalHolds_negate, clauseHolds_negated, eval]
  by_cases ho : LiteralHolds a out
  · have hv := (literalValue_eq_true a out).mpr ho
    simp [ho, hv, List.all_eq_true]
  · have hv := (literalValue_eq_false a out).mpr ho
    simp [ho, hv, List.all_eq_false]

theorem or_block_correct (a : α → Bool) (out : Literal α) (ls : List (Literal α)) :
    Satisfies a (block out (.or ls)) ↔ literalValue a out = eval a (.or ls) := by
  simp only [block, clauses, satisfies_ofClauses, List.forall_mem_append,
    List.forall_mem_map, List.forall_mem_singleton, clauseHolds_cons, clauseHolds_nil,
    or_false, literalHolds_negate, eval]
  by_cases ho : LiteralHolds a out
  · have hv := (literalValue_eq_true a out).mpr ho
    simp [ho, hv, ClauseHolds, List.any_eq_true]
  · have hv := (literalValue_eq_false a out).mpr ho
    simp [ho, hv, ClauseHolds, List.any_eq_false]

theorem block_correct (a : α → Bool) (out : Literal α) (g : Gate α) :
    Satisfies a (block out g) ↔ literalValue a out = eval a g := by
  cases g with
  | and ls => exact and_block_correct a out ls
  | or ls => exact or_block_correct a out ls
  | xor l r =>
    simp only [block, clauses, satisfies_ofClauses, List.forall_mem_cons,
      clauseHolds_cons, clauseHolds_nil, or_false,
      literalHolds_negate, eval]
    simp only [← literalValue_eq_true]
    cases literalValue a l <;> cases literalValue a r <;> cases literalValue a out <;> simp
  | «alias» l =>
    simp only [block, clauses, satisfies_ofClauses, List.forall_mem_cons,
      clauseHolds_cons, clauseHolds_nil, or_false,
      literalHolds_negate, eval]
    simp only [← literalValue_eq_true]
    cases literalValue a l <;> cases literalValue a out <;> simp
  | not l =>
    simp only [block, clauses, satisfies_ofClauses, List.forall_mem_cons,
      clauseHolds_cons, clauseHolds_nil, or_false,
      literalHolds_negate, eval]
    simp only [← literalValue_eq_true]
    cases literalValue a l <;> cases literalValue a out <;> simp
  | constant b =>
    cases b <;> simp [block, clauses, eval]

def relabel (r : α → β) : Gate α → Gate β
  | .and ls => .and (ls.map (fun l => (r l.1, l.2)))
  | .or ls => .or (ls.map (fun l => (r l.1, l.2)))
  | .xor l k => .xor (r l.1, l.2) (r k.1, k.2)
  | .alias l => .alias (r l.1, l.2)
  | .not l => .not (r l.1, l.2)
  | .constant b => .constant b

theorem eval_relabel (r : α → β) (a : β → Bool) (g : Gate α) :
    (g.relabel r).eval a = g.eval (a ∘ r) := by
  cases g <;> simp [relabel, eval, literalValue, Function.comp_def] <;> rfl

/-- Every row in the complete defining block has a matching input-CNF row.
Equality here is equality of literal sets, so factoring and row order are immaterial. -/
def ContainsBlock [DecidableEq α] (f : Formula α) (out : Literal α) (g : Gate α) : Prop :=
  ∀ i : Fin (g.clauses out).length, ∃ j : Fin f.clauses.size,
    (g.clauses out)[i].toFinset = f.clauses[j].toFinset

instance [DecidableEq α] (f : Formula α) (out : Literal α) (g : Gate α) :
    Decidable (ContainsBlock f out g) := inferInstanceAs (Decidable (∀ _, ∃ _, _))

theorem containsBlock_self [DecidableEq α] (out : Literal α) (g : Gate α) :
    ContainsBlock (g.block out) out g := by
  intro i
  refine ⟨⟨i.val, ?_⟩, ?_⟩
  · simp [block, ofClauses]
  · rfl

theorem ContainsBlock.output_correct [DecidableEq α] {f : Formula α}
    {out : Literal α} {g : Gate α} (h : ContainsBlock f out g)
    (a : α → Bool) (ha : Satisfies a f) : literalValue a out = g.eval a := by
  apply (block_correct a out g).mp
  rw [block, satisfies_ofClauses]
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨j, hj⟩ := h ⟨i, hi⟩
  have hs : ClauseHolds a f.clauses[j] := (satisfies_iff_rows a f).mp ha j
  exact (clauseHolds_of_toFinset_eq a hj).mpr hs

/-- The supplied local block has exactly the defining rows, up to literal sets
and duplicate rows. It contains neither a missing direction nor an extra restriction. -/
def CompleteProducer [DecidableEq α] (f : Formula α) (out : Literal α) (g : Gate α) : Prop :=
  ContainsBlock f out g ∧
    ∀ j : Fin f.clauses.size, ∃ i : Fin (g.clauses out).length,
      f.clauses[j].toFinset = (g.clauses out)[i].toFinset

instance [DecidableEq α] (f : Formula α) (out : Literal α) (g : Gate α) :
    Decidable (CompleteProducer f out g) := inferInstanceAs (Decidable (_ ∧ ∀ _, ∃ _, _))

theorem completeProducer_self [DecidableEq α] (out : Literal α) (g : Gate α) :
    CompleteProducer (g.block out) out g := by
  refine ⟨containsBlock_self out g, ?_⟩
  intro j
  refine ⟨⟨j.val, ?_⟩, ?_⟩
  · simpa [block, ofClauses] using j.isLt
  · rfl

theorem CompleteProducer.correct [DecidableEq α] {f : Formula α}
    {out : Literal α} {g : Gate α} (h : CompleteProducer f out g) (a : α → Bool) :
    Satisfies a f ↔ literalValue a out = g.eval a := by
  constructor
  · exact h.1.output_correct a
  · intro hv
    have hb := (block_correct a out g).mpr hv
    rw [satisfies_iff_rows]
    intro j
    obtain ⟨i, hi⟩ := h.2 j
    have hg : ClauseHolds a (g.clauses out)[i] :=
      (satisfies_ofClauses a (g.clauses out)).mp hb _ (List.getElem_mem ..)
    exact (clauseHolds_of_toFinset_eq a hi).mpr hg

example : ¬CompleteProducer
    (ofClauses [[(1, false), (0, true)]] : FiniteFormula 2)
    (1, true) (.and [(0, true)]) := by decide

example : CompleteProducer
    (ofClauses [[(1, false), (0, true)], [(1, true), (0, false)]] : FiniteFormula 2)
    (1, true) (.alias (0, true)) := by decide

example : ¬CompleteProducer
    (ofClauses [[(1, false), (0, true)], [(1, true), (0, false)], [(0, true)]] : FiniteFormula 2)
    (1, true) (.alias (0, true)) := by decide

end Gate
end Controller.CNF
