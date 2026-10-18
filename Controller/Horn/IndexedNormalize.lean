module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistCorrect

@[expose] public section

/-!
# Literal-mark normalization for the dual-Horn worklist

A single finite table stores the positive and negative marks of each declared
variable. Each row scans its literals from right to left, matching the retained
order of `List.dedup`. Only variables touched by that row are cleared before the
table is reused. The resulting rule table equals the semantic compiler exactly.
-/

namespace Controller.Horn.Worklist.IndexedNormalize

open CNF

/-- Positive and negative marks, indexed by the declared variable namespace. -/
abbrev Marks (n : Nat) := Vector (Bool × Bool) n

def Marks.read (marks : Marks n) (literal : Literal (Fin n)) : Bool :=
  if literal.2 then marks[literal.1.val].1 else marks[literal.1.val].2

def Marks.Clean (marks : Marks n) : Prop :=
  ∀ label : Fin n, marks[label.val] = (false, false)

def Marks.initial (n : Nat) : Marks n := Vector.replicate n (false, false)

theorem Marks.initial_clean (n : Nat) : (Marks.initial n).Clean := by
  intro label
  simp [Marks.initial]

/-- Clear exactly the supplied touched labels; no ambient variable scan occurs. -/
def Marks.clear : List (Fin n) → Marks n → Marks n
  | [], marks => marks
  | label :: rest, marks =>
      Marks.clear rest (marks.set label.val (false, false) label.isLt)

theorem Marks.clear_get (labels : List (Fin n)) (marks : Marks n) (label : Fin n) :
    (Marks.clear labels marks)[label.val] =
      if label ∈ labels then (false, false) else marks[label.val] := by
  induction labels generalizing marks with
  | nil => simp [Marks.clear]
  | cons head rest ih =>
    rw [Marks.clear, ih]
    by_cases equal : head = label
    · subst head
      simp
    · have unequal : head.val ≠ label.val := fun same => equal (Fin.ext same)
      simp [List.mem_cons, Ne.symm equal, unequal]

/-- Scratch lists for one row; the mark table is reused between rows. -/
structure Row (n : Nat) where
  marks : Marks n
  positive : List (Fin n)
  negative : List (Fin n)
  touched : List (Fin n)
  tautology : Bool

def Row.empty (marks : Marks n) : Row n :=
  ⟨marks, [], [], [], false⟩

/-- One literal performs indexed mark reads and writes and constant-many list
cons operations. Duplicate signs and opposite signs are distinguished. -/
def Row.record (literal : Literal (Fin n)) (row : Row n) : Row n :=
  let old := row.marks[literal.1.val]
  { marks := row.marks.set literal.1.val
      (if literal.2 then (true, old.2) else (old.1, true)) literal.1.isLt
    positive := if literal.2 && !old.1 then literal.1 :: row.positive else row.positive
    negative := if !literal.2 && !old.2 then literal.1 :: row.negative else row.negative
    touched := if old.1 || old.2 then row.touched else literal.1 :: row.touched
    tautology := row.tautology || (if literal.2 then old.2 else old.1) }

theorem Row.read_record (literal query : Literal (Fin n)) (row : Row n) :
    (row.record literal).marks.read query =
      if query = literal then true else row.marks.read query := by
  rcases literal with ⟨label, polarity⟩
  rcases query with ⟨other, sign⟩
  by_cases equal : label = other
  · subst other
    cases polarity <;> cases sign <;> simp [Row.record, Marks.read]
  · have unequal : label.val ≠ other.val := fun same => equal (Fin.ext same)
    cases polarity <;> cases sign <;>
      simp [Row.record, Marks.read, unequal, Ne.symm equal]

private theorem signedLabels_cons (literal : Literal (Fin n))
    (clause : Clause (Fin n)) (polarity : Bool) :
    signedLabels (literal :: clause) polarity =
      if literal.2 = polarity then
        if (literal.1, polarity) ∈ clause then signedLabels clause polarity
        else literal.1 :: signedLabels clause polarity
      else signedLabels clause polarity := by
  rcases literal with ⟨label, sign⟩
  by_cases equal : sign = polarity
  · subst sign
    simp only [signedLabels, List.filter_cons, decide_true, ite_true, List.map_cons,
      List.dedup_cons']
    change (if label ∈ signedLabels clause polarity then signedLabels clause polarity
      else label :: signedLabels clause polarity) = _
    simp only [mem_signedLabels]
    unfold signedLabels
    split_ifs <;> rfl
  · simp [signedLabels, equal]

private theorem tautological_cons (literal : Literal (Fin n)) (clause : Clause (Fin n)) :
    Tautological (literal :: clause) ↔ Tautological clause ∨ negate literal ∈ clause := by
  have distinct : negate literal ≠ literal := by
    rcases literal with ⟨label, sign⟩
    cases sign <;> simp [negate, Std.Sat.Literal.negate]
  constructor
  · rintro ⟨other, member, opposite⟩
    rcases List.mem_cons.mp member with equal | old
    · subst other
      exact Or.inr ((List.mem_cons.mp opposite).resolve_left distinct)
    · rcases List.mem_cons.mp opposite with equal | oldOpposite
      · right
        have inverse : other = negate literal := by
          simpa only [negate_negate] using congrArg negate equal
        simpa only [inverse] using old
      · exact Or.inl ⟨other, old, oldOpposite⟩
  · rintro (⟨other, member, opposite⟩ | opposite)
    · exact ⟨other, List.mem_cons_of_mem literal member, List.mem_cons_of_mem literal opposite⟩
    · exact ⟨literal, List.mem_cons_self, List.mem_cons_of_mem literal opposite⟩

private theorem tautologyCheck_cons (literal : Literal (Fin n)) (clause : Clause (Fin n)) :
    tautologyCheck (literal :: clause) =
      (tautologyCheck clause || decide (negate literal ∈ clause)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, tautologyCheck_eq_true]
  exact tautological_cons literal clause

/-- Exact suffix invariant, including the order of all retained lists. -/
structure Row.Correct (clause : Clause (Fin n)) (row : Row n) : Prop where
  marked : ∀ literal, row.marks.read literal = decide (literal ∈ clause)
  positive : row.positive = signedLabels clause true
  negative : row.negative = signedLabels clause false
  touched : row.touched = (clause.map Prod.fst).dedup
  tautology : row.tautology = tautologyCheck clause

theorem Row.empty_correct (marks : Marks n) (clean : marks.Clean) :
    (Row.empty marks).Correct [] := by
  constructor
  · rintro ⟨label, sign⟩
    dsimp [Row.empty, Marks.read]
    rw [clean label]
    cases sign <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem Row.any_mark_correct {clause : Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) (label : Fin n) :
    (row.marks[label.val].1 || row.marks[label.val].2) =
      decide (label ∈ clause.map Prod.fst) := by
  have positive : row.marks[label.val].1 = decide ((label, true) ∈ clause) :=
    correct.marked (label, true)
  have negative : row.marks[label.val].2 = decide ((label, false) ∈ clause) :=
    correct.marked (label, false)
  rw [positive, negative]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_map]
  constructor
  · rintro (member | member)
    · exact ⟨(label, true), member, rfl⟩
    · exact ⟨(label, false), member, rfl⟩
  · rintro ⟨⟨other, sign⟩, member, equal⟩
    dsimp at equal
    subst other
    cases sign
    · exact Or.inr member
    · exact Or.inl member

theorem Row.record_correct {clause : Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) (literal : Literal (Fin n)) :
    (row.record literal).Correct (literal :: clause) := by
  constructor
  · intro query
    rw [Row.read_record, correct.marked]
    by_cases equal : query = literal <;> simp [equal, List.mem_cons]
  · have mark : row.marks[literal.1.val].1 = decide ((literal.1, true) ∈ clause) :=
      correct.marked (literal.1, true)
    change (if literal.2 && !row.marks[literal.1.val].1 then
      literal.1 :: row.positive else row.positive) = _
    rw [mark, correct.positive, signedLabels_cons]
    cases literal.2 <;> simp
  · have mark : row.marks[literal.1.val].2 = decide ((literal.1, false) ∈ clause) :=
      correct.marked (literal.1, false)
    change (if !literal.2 && !row.marks[literal.1.val].2 then
      literal.1 :: row.negative else row.negative) = _
    rw [mark, correct.negative, signedLabels_cons]
    cases literal.2 <;> simp
  · change (if row.marks[literal.1.val].1 || row.marks[literal.1.val].2 then row.touched
      else literal.1 :: row.touched) = _
    rw [Row.any_mark_correct correct, correct.touched]
    simp only [List.map_cons, List.dedup_cons, decide_eq_true_eq]
  · have mark := correct.marked (negate literal)
    rw [tautologyCheck_cons]
    change (row.tautology || (if literal.2 then row.marks[literal.1.val].2
      else row.marks[literal.1.val].1)) = _
    rw [correct.tautology]
    congr 1
    rcases literal with ⟨label, sign⟩
    cases sign <;> exact mark

/-- Right-to-left literal traversal preserves the semantic compiler's order. -/
def scan : Clause (Fin n) → Marks n → Row n
  | [], marks => Row.empty marks
  | literal :: clause, marks => (scan clause marks).record literal

theorem scan_correct (clause : Clause (Fin n)) (marks : Marks n) (clean : marks.Clean) :
    (scan clause marks).Correct clause := by
  induction clause with
  | nil => exact Row.empty_correct marks clean
  | cons literal clause ih => exact Row.record_correct ih literal

/-- Finish a row only after every literal has been seen. A tautology can contain
several distinct negative variables and still compiles to an inert row. -/
def Row.rule (row : Row n) : Rule (Fin n) :=
  if row.tautology then .skip else
    match row.negative with
    | [] => .positive row.positive
    | head :: _ => .negative head row.positive

theorem Row.rule_eq_compileClause {clause : Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) : row.rule = compileClause clause := by
  by_cases tautology : tautologyCheck clause = true
  · simp [Row.rule, compileClause, correct.tautology, tautology]
  · cases negatives : signedLabels clause false <;>
      simp [Row.rule, compileClause, correct.tautology, correct.negative,
        correct.positive, tautology, negatives]

theorem Row.touched_nodup {clause : Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) : row.touched.Nodup := by
  rw [correct.touched]
  exact List.nodup_dedup _

theorem Row.touched_length_le {clause : Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) : row.touched.length ≤ clause.length := by
  rw [correct.touched]
  simpa only [List.length_map] using
    (List.dedup_sublist (clause.map Prod.fst)).length_le

theorem Row.clear_clean {clause : Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) : (Marks.clear row.touched row.marks).Clean := by
  intro label
  rw [Marks.clear_get]
  split
  · rfl
  · rename_i untouched
    have absent : label ∉ clause.map Prod.fst := by
      simpa only [correct.touched, List.mem_dedup] using untouched
    have notPositive : (label, true) ∉ clause := fun member =>
      absent (List.mem_map.mpr ⟨(label, true), member, rfl⟩)
    have notNegative : (label, false) ∉ clause := fun member =>
      absent (List.mem_map.mpr ⟨(label, false), member, rfl⟩)
    apply Prod.ext
    · simpa [Marks.read, notPositive] using correct.marked (label, true)
    · simpa [Marks.read, notNegative] using correct.marked (label, false)

/-- Reuse the mark table across all rows, retaining every input row identifier. -/
def compileRows : List (Clause (Fin n)) → Marks n → List (Rule (Fin n)) × Marks n
  | [], marks => ([], marks)
  | clause :: clauses, marks =>
      let row := scan clause marks
      let rest := compileRows clauses (Marks.clear row.touched row.marks)
      (row.rule :: rest.1, rest.2)

theorem compileRows_correct (clauses : List (Clause (Fin n))) (marks : Marks n)
    (clean : marks.Clean) :
    (compileRows clauses marks).1 = clauses.map compileClause ∧
      (compileRows clauses marks).2.Clean := by
  induction clauses generalizing marks with
  | nil => exact ⟨rfl, clean⟩
  | cons clause clauses ih =>
    have rowCorrect := scan_correct clause marks clean
    have restCorrect := ih _ (Row.clear_clean rowCorrect)
    constructor
    · change (scan clause marks).rule :: _ = _
      rw [Row.rule_eq_compileClause rowCorrect, restCorrect.1]
      rfl
    · exact restCorrect.2

/-- The only ambient `n`-sized initialization occurs before row traversal. -/
def compile (formula : Formula (Fin n)) : Array (Rule (Fin n)) :=
  (compileRows formula.clauses.toList (Marks.initial n)).1.toArray

theorem compile_eq_compileFormula (formula : Formula (Fin n)) :
    compile formula = compileFormula formula := by
  rw [compile, (compileRows_correct _ _ (Marks.initial_clean n)).1]
  rw [← List.map_toArray, Array.toArray_toList]
  rfl

theorem compile_size (formula : Formula (Fin n)) :
    (compile formula).size = formula.clauses.size := by
  rw [compile_eq_compileFormula, compileFormula_size]

/-- The indexed compiler supplies exactly the rule table consumed by D04. -/
def table (formula : Formula (Fin n)) : RuleTable n formula.clauses.size :=
  ⟨compile formula, compile_size formula⟩

theorem table_eq_normalizedTable (formula : Formula (Fin n)) :
    table formula = normalizedTable formula := by
  apply Vector.toArray_inj.mp
  exact compile_eq_compileFormula formula

/-- Execute the existing occurrence builder and propagation loop after indexed
normalization. The result is extensionally equal to `solveFormula`. -/
def solve (formula : Formula (Fin n)) : Option (Vector Bool n) :=
  solveRules (table formula)

theorem solve_eq_solveFormula (formula : Formula (Fin n)) :
    solve formula = solveFormula formula := by
  rw [solve, table_eq_normalizedTable]
  rfl

end Controller.Horn.Worklist.IndexedNormalize
