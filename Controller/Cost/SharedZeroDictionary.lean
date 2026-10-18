module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCoordinateTable
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-! Every ambient coordinate is touched before root-specific rows, fixing the reusable solver dictionary size. -/
namespace Controller.Cost.SharedZeroDictionary
open Controller.CNF Controller.Cost.ForestZeroCompile

private theorem related_member {produced : List (Clause Nat)} {original : List (Clause (Fin ambient))}
    (state : Dictionary ambient)
    (related : List.Forall₂ (fun output source => List.Forall₂
      (fun out lit => state.coordinates[out.1]? = some lit.1 ∧ out.2 = lit.2) output source) produced original)
    (row : Clause (Fin ambient)) (member : row ∈ original)
    (literal : Literal (Fin ambient)) (present : literal ∈ row) :
    ∃ index : Nat, state.coordinates[index]? = some literal.1 := by
  induction related with
  | nil => simp at member
  | @cons output source outputs sources same rest ih =>
    rcases List.mem_cons.mp member with equal | tail
    · subst row
      clear ih rest member
      induction same with
      | nil => simp at present
      | @cons out lit outs lits pair pairs ihLit =>
        rcases List.mem_cons.mp present with equal | tail
        · subst literal; exact ⟨out.1, pair.1⟩
        · exact ihLit tail
    · exact ih tail

theorem coordinate_present (clauses : List (Clause (Fin ambient))) (coordinate : Fin ambient) :
    ∃ index : Nat, (compileRows (empty ambient) (SharedZeroTemplate.touchRows ambient ++ clauses)).1.coordinates[index]? =
      some coordinate := by
  apply related_member _ (rows_correspondence _ (empty_coherent ambient) _) [(coordinate, false), (coordinate, true)]
    _ (coordinate, false) (by simp)
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨coordinate, List.mem_finRange coordinate, rfl⟩

theorem dictionary_size (clauses : List (Clause (Fin ambient))) :
    (compileRows (empty ambient) (SharedZeroTemplate.touchRows ambient ++ clauses)).1.coordinates.size = ambient := by
  let state := (compileRows (empty ambient) (SharedZeroTemplate.touchRows ambient ++ clauses)).1
  have coherent : Coherent state := (rows_dictionary _ (empty_coherent ambient) _).1
  let lookup : Fin state.coordinates.size → Fin ambient := fun index => state.coordinates[index.val]
  have injective : Function.Injective lookup := by
    intro left right same
    have leftCell : state.coordinates[left.val]? = some (lookup left) := by simp [lookup]
    have rightCell : state.coordinates[right.val]? = some (lookup right) := by simp [lookup]
    have leftSlot := (coherent (lookup left) left.val).mpr leftCell
    have rightSlot := (coherent (lookup right) right.val).mpr rightCell
    rw [← same] at rightSlot
    apply Fin.ext
    omega
  have surjective : Function.Surjective lookup := by
    intro coordinate
    obtain ⟨index, cell⟩ := coordinate_present clauses coordinate
    obtain ⟨valid, equal⟩ := Array.getElem?_eq_some_iff.mp cell
    exact ⟨⟨index, valid⟩, equal⟩
  have upper := Fintype.card_le_of_injective lookup injective
  have lower := Fintype.card_le_of_surjective lookup surjective
  simpa only [Fintype.card_fin] using Nat.le_antisymm upper lower


theorem clause_dictionary_stable (state : Dictionary ambient)
    (present : ∀ coordinate : Fin ambient, state.slots[coordinate.val] ≠ 0)
    (clause : Clause (Fin ambient)) : (compileClause state clause).1 = state := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
    simpa only [compileClause, touch, ite_eq_right (present literal.1)] using ih

theorem rows_dictionary_stable (state : Dictionary ambient)
    (present : ∀ coordinate : Fin ambient, state.slots[coordinate.val] ≠ 0)
    (clauses : List (Clause (Fin ambient))) : (compileRows state clauses).1 = state := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
    simp only [compileRows, clause_dictionary_stable state present clause, ih]

theorem rows_dictionary_append (state : Dictionary ambient)
    (left right : List (Clause (Fin ambient))) :
    (compileRows state (left ++ right)).1 = (compileRows (compileRows state left).1 right).1 := by
  induction left generalizing state with
  | nil => rfl
  | cons clause rest ih =>
    simp only [List.cons_append, compileRows]
    exact ih _

theorem touch_rows_full : ∀ coordinate : Fin ambient,
    (compileRows (empty ambient) (SharedZeroTemplate.touchRows ambient)).1.slots[coordinate.val] ≠ 0 := by
  intro coordinate
  have coherent := (rows_dictionary (empty ambient) (empty_coherent ambient) (SharedZeroTemplate.touchRows ambient)).1
  obtain ⟨index, cell⟩ := coordinate_present ([] : List (Clause (Fin ambient))) coordinate
  simp only [List.append_nil] at cell
  have slot := (coherent coordinate index).mpr cell
  rw [slot]
  omega

theorem dictionary_fixed (clauses : List (Clause (Fin ambient))) :
    (compileRows (empty ambient) (SharedZeroTemplate.touchRows ambient ++ clauses)).1 =
      (compileRows (empty ambient) (SharedZeroTemplate.touchRows ambient)).1 := by
  rw [rows_dictionary_append]
  exact rows_dictionary_stable _ touch_rows_full clauses

end Controller.Cost.SharedZeroDictionary
