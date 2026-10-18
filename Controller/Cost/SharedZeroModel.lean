module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroQuery

@[expose] public section

/-! Local constructor literals retain their source coordinates through finite conversion and the reserved-row truncation. -/
namespace Controller.Cost.SharedZeroModel
open Controller.CNF Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroEmit

private theorem clause_transport {α β : Type} (left : α → Bool) (right : β → Bool)
    {produced : Clause α} {original : Clause β}
    (same : List.Forall₂ (fun a b => LiteralHolds left a ↔ LiteralHolds right b) produced original) :
    ClauseHolds left produced ↔ ClauseHolds right original := by
  induction same with
  | nil => simp [ClauseHolds]
  | cons head tail ih => simpa only [clauseHolds_cons] using or_congr head ih

private theorem formula_transport {α β : Type} (left : α → Bool) (right : β → Bool)
    {produced : List (Clause α)} {original : List (Clause β)}
    (same : List.Forall₂ (fun a b => ClauseHolds left a ↔ ClauseHolds right b) produced original) :
    Satisfies left (ofClauses produced) ↔ Satisfies right (ofClauses original) := by
  simp only [satisfies_ofClauses]
  induction same with
  | nil => simp
  | cons head tail ih => simpa only [List.forall_mem_cons] using and_congr head ih

theorem original_correspondence (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) :
    let final := (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1
    List.Forall₂ (fun produced original => List.Forall₂ (fun output source =>
      final.coordinates[output.1.val]? = some source.1 ∧ output.2 = source.2) produced original)
      (originalClauses dictionary coherent references) (ForestZeroAssembly.originalRows references) := by
  let rows := ForestZeroAssembly.originalRows (reservedReferences references)
  let final := (compileRows dictionary rows).1
  have raw := rows_correspondence dictionary coherent rows
  have finiteRaw := ForestZeroAssembly.finiteClauses_raw (compileRows dictionary rows).2.1
    (rows_bounds dictionary coherent rows)
  have mapped : List.Forall₂ (fun produced original => List.Forall₂ (fun output source =>
      final.coordinates[output.1]? = some source.1 ∧ output.2 = source.2) produced original)
      ((reservedClauses dictionary coherent references).map
        (List.map (fun literal => (literal.1.val, literal.2)))) rows := by
    rw [show (reservedClauses dictionary coherent references).map
      (List.map (fun literal => (literal.1.val, literal.2))) = (compileRows dictionary rows).2.1 from finiteRaw]
    exact raw
  have outer := List.forall₂_map_left_iff.mp mapped
  have finite : List.Forall₂ (fun produced original => List.Forall₂ (fun output source =>
      final.coordinates[output.1.val]? = some source.1 ∧ output.2 = source.2) produced original)
      (reservedClauses dictionary coherent references) rows :=
    List.Forall₂.imp (fun _ _ related => List.forall₂_map_left_iff.mp related) outer
  have truncated := List.forall₂_take references.length finite
  simpa [originalClauses, final, rows, ForestZeroAssembly.originalRows, reservedReferences,
    List.take_append, List.length_map] using truncated

theorem original_lift_model (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient)))
    (values : Fin (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1.coordinates.size → Bool) :
    Satisfies values (ofClauses (originalClauses dictionary coherent references)) ↔
      Satisfies (ForestZeroModelLift.lift
        (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1 true
        (extendNat values)) (ofClauses (ForestZeroAssembly.originalRows references)) := by
  have finalCoherent := (rows_dictionary dictionary coherent
    (ForestZeroAssembly.originalRows (reservedReferences references))).1
  apply formula_transport
  apply List.Forall₂.imp _ (original_correspondence dictionary coherent references)
  intro produced original related
  apply clause_transport
  apply List.Forall₂.imp _ related
  intro output source pair
  have value := ForestZeroModelLift.lift_used _ finalCoherent true (extendNat values)
    output.1.val source.1 pair.1
  simp only [LiteralHolds, value, pair.2]
  simp [extendNat, output.1.isLt]

theorem original_forward_model (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (assignment : Fin ambient → Bool) :
    let final := (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1
    Satisfies (fun index : Fin final.coordinates.size => assignment final.coordinates[index.val])
      (ofClauses (originalClauses dictionary coherent references)) ↔
      Satisfies assignment (ofClauses (ForestZeroAssembly.originalRows references)) := by
  apply formula_transport
  apply List.Forall₂.imp _ (original_correspondence dictionary coherent references)
  intro produced original related
  apply clause_transport
  apply List.Forall₂.imp _ related
  intro output source pair
  have cell : (compileRows dictionary (ForestZeroAssembly.originalRows (reservedReferences references))).1.coordinates[output.1.val] =
      source.1 := by
    simpa only [Array.getElem?_eq_getElem output.1.isLt, Option.some.injEq] using pair.1
  simp only [LiteralHolds, cell, pair.2]

theorem finite_clause_model (row : Clause Nat) (bound : ∀ literal ∈ row, literal.1 < limit)
    (values : Fin limit → Bool) :
    ClauseHolds values (finiteClause row bound) ↔ ClauseHolds (extendNat values) row := by
  have renamed : relabel Fin.val (ofClauses [finiteClause row bound]) = ofClauses [row] := by
    simp [relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel,
      ofClauses, ForestZeroAssembly.finiteClause_raw]
  have pulled : extendNat values ∘ Fin.val = values := by
    funext index
    simp [Function.comp_def, extendNat, index.isLt]
  have same := satisfies_relabel Fin.val (extendNat values) (ofClauses [finiteClause row bound])
  rw [renamed, pulled] at same
  simpa [satisfies_ofClauses] using same.symm

theorem constructor_lift_model (heap : Array (Word width))
    (layout : Controller.Cost.ForestZeroDictionary.Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (nonempty : ∀ assignment, Satisfies assignment (ofClauses (ForestZeroAssembly.originalRows references)) →
      ∃ channel : Fin channels, assignment ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ = true)
    (values : Fin (constructorDictionary heap layout dictionary references).coordinates.size → Bool) :
    Satisfies values (constructorFormula heap layout dictionary coherent references channels within) ↔
      Satisfies (ForestZeroModelLift.lift (constructorDictionary heap layout dictionary references) true
        (extendNat values)) (ofClauses (ForestZeroAssembly.originalRows references)) := by
  have original := original_lift_model dictionary coherent references values
  simp only [satisfies_ofClauses] at original nonempty
  by_cases covered : (ForestZeroNonempty.search (constructorDictionary heap layout dictionary references)
      ((constructorDictionary heap layout dictionary references).coordinates.size + 1) channels 0).reason = .covered
  · have slots := constructor_covered_slots dictionary coherent references channels within covered
    have positive := ForestZeroPositive.positiveClause_holds
      (constructorDictionary heap layout dictionary references) (extendNat values) true channels within slots
    simp only [constructorFormula, constructorClauses, dite_eq_left covered, satisfies_ofClauses,
      List.forall_mem_append, List.forall_mem_singleton]
    constructor
    · rintro ⟨model, _⟩
      exact original.mp (by simpa only [satisfies_ofClauses] using model)
    · intro model
      refine ⟨by simpa only [satisfies_ofClauses] using original.mpr model, ?_⟩
      apply (finite_clause_model _ _ values).mpr
      exact positive.mpr (nonempty _ model)
  · simpa only [constructorFormula, constructorClauses, dite_eq_right covered, satisfies_ofClauses] using original

theorem constructor_satisfiable (heap : Array (Word width))
    (layout : Controller.Cost.ForestZeroDictionary.Layout ambient heap.size)
    (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (nonempty : ∀ assignment, Satisfies assignment (ofClauses (ForestZeroAssembly.originalRows references)) →
      ∃ channel : Fin channels, assignment ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ = true) :
    Satisfiable (constructorFormula heap layout dictionary coherent references channels within) ↔
      Satisfiable (ofClauses (ForestZeroAssembly.originalRows references)) := by
  constructor
  · rintro ⟨values, model⟩
    exact ⟨_, (constructor_lift_model heap layout dictionary coherent references channels within nonempty values).mp model⟩
  · rintro ⟨assignment, model⟩
    let values : Fin (constructorDictionary heap layout dictionary references).coordinates.size → Bool :=
      fun index => assignment (constructorDictionary heap layout dictionary references).coordinates[index.val]
    have originalModel := (original_forward_model dictionary coherent references assignment).mpr model
    have lifted := (original_lift_model dictionary coherent references values).mp originalModel
    exact ⟨values, (constructor_lift_model heap layout dictionary coherent references channels within nonempty values).mpr lifted⟩

end Controller.Cost.SharedZeroModel
