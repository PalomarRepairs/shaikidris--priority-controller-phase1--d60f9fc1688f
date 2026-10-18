module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroModelLift

@[expose] public section

/-! The actual first-touch allocation and bounded Fin conversion preserve
Dual-Horn clauses, including repeated negative occurrences and tautologies.
This supplies the grammar premise for the finite backend without a semantic
satisfiability oracle or support enumeration.
-/
namespace Controller.Cost.ForestZeroGrammar
open Controller.CNF Controller.Cost.ForestZeroCompile
variable {ambient : ℕ}

def localIndex (state : Dictionary ambient) (coordinate : Fin ambient) : ℕ :=
  state.slots[coordinate.val] - 1

private theorem clause_as_map (state : Dictionary ambient) (coherent : Coherent state)
    {produced : Clause ℕ} {original : Clause (Fin ambient)}
    (related : List.Forall₂ (fun output source =>
      state.coordinates[output.1]? = some source.1 ∧ output.2 = source.2) produced original) :
    produced = original.map (fun literal => (localIndex state literal.1, literal.2)) := by
  induction related with
  | nil => rfl
  | @cons output source outputs sources same related ih =>
    have encoded := (coherent source.1 output.1).mpr same.1
    have index : output.1 = localIndex state source.1 := by
      simp only [localIndex, encoded, Nat.add_sub_cancel]
    have literal : output = (localIndex state source.1, source.2) := Prod.ext index same.2
    simp only [List.map_cons, literal, ih]

private theorem related_dualHorn (state : Dictionary ambient) (coherent : Coherent state)
    {produced : List (Clause ℕ)} {original : List (Clause (Fin ambient))}
    (related : List.Forall₂ (fun output source =>
      List.Forall₂ (fun out lit => state.coordinates[out.1]? = some lit.1 ∧ out.2 = lit.2)
        output source) produced original)
    (dual : ∀ clause ∈ original, Controller.Horn.DualHornClause clause) :
    ∀ clause ∈ produced, Controller.Horn.DualHornClause clause := by
  induction related with
  | nil => simp
  | @cons first source rest originals same related ih =>
    intro clause present
    rcases List.mem_cons.mp present with equality | tail
    · subst clause
      rw [clause_as_map state coherent same]
      exact Controller.Decoder.SparseFormula.clause_relabel_dualHorn
        (localIndex state) source (dual source (List.mem_cons_self))
    · exact ih (fun clause present => dual clause (List.mem_cons_of_mem _ present)) clause tail

/-- Dictionary allocation preserves the source Dual-Horn grammar. -/
theorem compiled_dualHorn (state : Dictionary ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient))) (dual : Controller.Horn.DualHorn (ofClauses rows)) :
    Controller.Horn.DualHorn (ofClauses (compileRows state rows).2.1) := by
  have source : ∀ clause ∈ rows, Controller.Horn.DualHornClause clause := by
    simpa only [Controller.Horn.DualHorn, ofClauses, List.mem_toArray] using dual
  have result := related_dualHorn _ (rows_dictionary state coherent rows).1
    (rows_correspondence state coherent rows) source
  simpa only [Controller.Horn.DualHorn, ofClauses, List.mem_toArray] using result

/-- Bounded conversion to finite local IDs preserves both grammar branches. -/
theorem finiteClause_dualHorn (row : Clause ℕ)
    (bound : ∀ literal ∈ row, literal.1 < limit)
    (dual : Controller.Horn.DualHornClause row) :
    Controller.Horn.DualHornClause (finiteClause row bound) := by
  rcases dual with tautology | unique
  · obtain ⟨literal, present, opposite⟩ := tautology
    left
    refine ⟨(⟨literal.1, bound literal present⟩, literal.2), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨⟨literal, present⟩, List.mem_attach _ _, rfl⟩
    · exact List.mem_map.mpr ⟨⟨negate literal, opposite⟩, List.mem_attach _ _, rfl⟩
  · right
    intro left leftMember right rightMember leftNegative rightNegative
    obtain ⟨oldLeft, oldLeftMember, leftEquation⟩ := List.mem_map.mp leftMember
    obtain ⟨oldRight, oldRightMember, rightEquation⟩ := List.mem_map.mp rightMember
    subst left
    subst right
    apply Fin.ext
    exact unique oldLeft.val oldLeft.property oldRight.val oldRight.property leftNegative rightNegative

theorem finiteRows_dualHorn (rows : List (Clause ℕ)) (bound : BoundedRows limit rows)
    (dual : Controller.Horn.DualHorn (ofClauses rows)) :
    Controller.Horn.DualHorn (finiteRows rows bound) := by
  intro clause present
  obtain ⟨original, member, equality⟩ := List.mem_map.mp
    (show clause ∈ rows.attach.map (fun row => finiteClause row.val (bound row.val row.property)) from
      by simpa only [finiteRows, ofClauses, List.mem_toArray] using present)
  subst clause
  exact finiteClause_dualHorn original.val (bound _ original.property)
    (dual _ (by simpa only [ofClauses, List.mem_toArray] using original.property))

/-- The complete executed compiler supplies the exact finite grammar needed
by the already checked worklist model-lift endpoint. -/
theorem compiled_finite_dualHorn (state : Dictionary ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient))) (dual : Controller.Horn.DualHorn (ofClauses rows)) :
    Controller.Horn.DualHorn
      (finiteRows (compileRows state rows).2.1 (rows_bounds state coherent rows)) :=
  finiteRows_dualHorn _ _ (compiled_dualHorn state coherent rows dual)

/-- A source Dual-Horn certificate is transported by the actual allocation
and bounded conversion; no separate local-grammar oracle is needed to lift
an actual returned worklist model. -/
theorem compiled_worklist_greatest (state : Dictionary ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient))) (dual : Controller.Horn.DualHorn (ofClauses rows))
    (values : Vector Bool (compileRows state rows).1.coordinates.size)
    (returned : Controller.Horn.Worklist.solveFormula
      (finiteRows (compileRows state rows).2.1 (rows_bounds state coherent rows)) = some values) :
    Satisfies (ForestZeroModelLift.lift (compileRows state rows).1 true
      (extendNat (fun i : Fin (compileRows state rows).1.coordinates.size => values[i.val]))) (ofClauses rows) ∧
      ∀ alternative, Satisfies alternative (ofClauses rows) →
        Controller.Horn.Below alternative
          (ForestZeroModelLift.lift (compileRows state rows).1 true (extendNat (fun i : Fin (compileRows state rows).1.coordinates.size => values[i.val]))) :=
  ForestZeroModelLift.worklist_greatest_lift state coherent rows
    (compiled_finite_dualHorn state coherent rows dual) values returned

end Controller.Cost.ForestZeroGrammar
