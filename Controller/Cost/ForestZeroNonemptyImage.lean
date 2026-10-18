module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroPositive
public import Controller.Cost.ForestZeroAdmissibleCaller

@[expose] public section

/-! The actual dictionary coverage scan selects precisely the nonemptiness
constraint needed by a compiled zero-model query. -/
namespace Controller.Cost.ForestZeroNonemptyImage
open Controller.CNF Controller.Cost.ForestZeroCompile
variable {ambient : Nat}

/-- Local rows augmented only when every physical channel has an allocated ID. -/
def nonemptyRows (initial : Dictionary ambient) (rows : List (Clause (Fin ambient)))
    (channels : Nat) : List (Clause Nat) :=
  let final := (compileRows initial rows).1
  if (ForestZeroNonempty.search final (final.coordinates.size + 1) channels 0).reason = .covered
  then (compileRows initial rows).2.1 ++ [ForestZeroPositive.positiveClause final channels]
  else (compileRows initial rows).2.1

/-- Allocated coordinates retain their original truth values under the
forward assignment followed by the same configurable dictionary lift. -/
theorem lift_local_used (state : Dictionary ambient) (coherent : Coherent state)
    (assignment : Fin ambient → Bool) (unused : Bool) (coordinate : Fin ambient)
    (used : state.slots[coordinate.val] ≠ 0) :
    ForestZeroModelLift.lift state unused (localAssignment state assignment) coordinate =
      assignment coordinate := by
  have encoded : state.slots[coordinate.val] = (state.slots[coordinate.val] - 1) + 1 := by omega
  have present := (coherent coordinate (state.slots[coordinate.val] - 1)).mp encoded
  rw [ForestZeroModelLift.lift_used state coherent unused _ _ coordinate present]
  simp only [localAssignment, present]

/-- Existence of a model for the executed optional-row choice is equivalent
to an original zero-row model with a genuinely enabled physical channel. -/
theorem nonemptyRows_satisfiable (initial : Dictionary ambient) (coherent : Coherent initial)
    (rows : List (Clause (Fin ambient))) (channels : Nat) (within : channels ≤ ambient) :
    Satisfiable (ofClauses (nonemptyRows initial rows channels)) ↔
      ∃ assignment : Fin ambient → Bool, Satisfies assignment (ofClauses rows) ∧
        ∃ channel : Fin channels, assignment ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ = true := by
  let final := (compileRows initial rows).1
  have valid : Coherent final := (rows_dictionary initial coherent rows).1
  have outcome := ForestZeroNonempty.search_outcome final valid channels within
  rcases outcome with ⟨unused, channel, unseen⟩ | ⟨covered, _, allUsed⟩
  · have choice : nonemptyRows initial rows channels = (compileRows initial rows).2.1 := by
      have actual := unused
      dsimp only [final] at actual
      simp [nonemptyRows, actual]
    rw [choice]
    constructor
    · rintro ⟨values, model⟩
      exact ⟨_, ForestZeroNonempty.unused_preserves_existing_model initial coherent rows channels within values model unused⟩
    · rintro ⟨assignment, model, _⟩
      exact ⟨_, (rows_forward_model initial coherent rows assignment).mpr model⟩
  · have used : ∀ channel : Fin channels,
        final.slots[(⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ : Fin ambient).val] ≠ 0 := allUsed
    have choice : nonemptyRows initial rows channels = (compileRows initial rows).2.1 ++
        [ForestZeroPositive.positiveClause final channels] := by
      have actual := covered
      dsimp only [final] at actual
      simp only [nonemptyRows, actual, ite_true]
      rfl
    rw [choice]
    constructor
    · rintro ⟨values, model⟩
      have split : Satisfies values (ofClauses (compileRows initial rows).2.1) ∧
          ClauseHolds values (ForestZeroPositive.positiveClause final channels) := by
        rw [satisfies_ofClauses] at model ⊢
        exact ⟨fun row member => model row (List.mem_append_left _ member),
          model _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
      refine ⟨ForestZeroModelLift.lift final true values,
        (ForestZeroModelLift.rows_lift_model initial coherent rows true values).mp split.1, ?_⟩
      exact (ForestZeroPositive.positiveClause_holds final values true channels within used).mp split.2
    · rintro ⟨assignment, model, channel, active⟩
      let values := localAssignment final assignment
      have localModel := (rows_forward_model initial coherent rows assignment).mpr model
      have positive : ClauseHolds values (ForestZeroPositive.positiveClause final channels) := by
        apply (ForestZeroPositive.positiveClause_holds final values true channels within used).mpr
        refine ⟨channel, ?_⟩
        rw [lift_local_used final valid assignment true _ (used channel)]
        exact active
      refine ⟨values, ?_⟩
      rw [satisfies_ofClauses] at localModel ⊢
      intro row member
      rcases List.mem_append.mp member with original | last
      · exact localModel row original
      · have same := List.mem_singleton.mp last
        subst row
        exact positive

/-- The reserved empty directory row allocates no coordinate and remains
separate from the model-bearing prefix. -/
theorem reserved_empty_dictionary (initial : Dictionary ambient)
    (rows : List (Clause (Fin ambient))) :
    (compileRows initial (rows ++ [[]])).1 = (compileRows initial rows).1 := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rest ih =>
      simpa only [List.cons_append, compileRows] using ih (compileClause initial row).1

/-- The compiler preserves the real rows before the reserved EMPTY entry. -/
theorem reserved_empty_rows (initial : Dictionary ambient)
    (rows : List (Clause (Fin ambient))) :
    (compileRows initial (rows ++ [[]])).2.1 = (compileRows initial rows).2.1 ++ [[]] := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.cons_append, compileRows, ih]

/-- Removing the directory reserve recovers exactly the source-model rows. -/
theorem reserved_empty_prefix (initial : Dictionary ambient)
    (rows : List (Clause (Fin ambient))) :
    (compileRows initial (rows ++ [[]])).2.1.take rows.length =
      (compileRows initial rows).2.1 := by
  have lengths : (compileRows initial rows).2.1.length = rows.length := by
    induction rows generalizing initial with
    | nil => rfl
    | cons row rest ih => simp only [compileRows, List.length_cons, ih]
  rw [reserved_empty_rows, ← lengths, List.take_append]
  simp


open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroAssembly Controller.Cost.GateProgram
open Controller.Cost.ForestZeroDictionary

/-- The resident constructor's reserved directory entry preserves exactly the
allocation dictionary of the actual source rows. -/
theorem constructor_dictionary_eq (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (initial : Dictionary ambient) (references : List (List (Reference ambient))) :
    constructorDictionary heap layout initial references =
      (compileRows initial (originalRows references)).1 := by
  unfold constructorDictionary reservedReferences
  simp only [originalRows, List.map_append, List.map_cons, List.map_nil]
  exact reserved_empty_dictionary initial _

/-- Reading the constructor's finite original prefix recovers the literal
pairs produced before its reserved EMPTY row. -/
theorem constructor_original_raw (initial : Dictionary ambient) (coherent : Coherent initial)
    (references : List (List (Reference ambient))) :
    (originalClauses initial coherent references).map
      (List.map (fun literal => (literal.1.val, literal.2))) =
      (compileRows initial (originalRows references)).2.1 := by
  unfold originalClauses reservedClauses
  rw [List.map_take, finiteClauses_raw]
  unfold reservedReferences
  simp only [originalRows, List.map_append, List.map_cons, List.map_nil]
  have actual := reserved_empty_prefix initial (originalRows references)
  simpa only [originalRows, List.length_map] using actual

/-- The actual finite constructor stores precisely the compiled row prefix
and the optional positive row selected by its dictionary scan. -/
theorem constructor_clauses_raw (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (initial : Dictionary ambient) (coherent : Coherent initial)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    (constructorClauses heap layout initial coherent references channels within).map
      (List.map (fun literal => (literal.1.val, literal.2))) =
      nonemptyRows initial (originalRows references) channels := by
  unfold constructorClauses
  dsimp only
  split_ifs with covered
  · rw [List.map_append, constructor_original_raw]
    simp only [List.map_cons, List.map_nil, finiteClause_raw]
    unfold nonemptyRows
    rw [← constructor_dictionary_eq heap layout initial references]
    rw [ite_eq_left covered]
  · rw [constructor_original_raw]
    unfold nonemptyRows
    rw [← constructor_dictionary_eq heap layout initial references]
    rw [ite_eq_right covered]


private theorem raw_clause_model (row : Clause (Fin locals)) (values : Nat → Bool) :
    ClauseHolds values (row.map (fun literal => (literal.1.val, literal.2))) ↔
      ClauseHolds (restrictNat values) row := by
  constructor
  · rintro ⟨literal, member, holds⟩
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ⟨original, present, holds⟩
  · rintro ⟨literal, present, holds⟩
    exact ⟨_, List.mem_map.mpr ⟨literal, present, rfl⟩, holds⟩

private theorem raw_rows_model (rows : List (Clause (Fin locals))) (values : Nat → Bool) :
    Satisfies values (ofClauses (rows.map (List.map (fun literal => (literal.1.val, literal.2))))) ↔
      Satisfies (restrictNat values) (ofClauses rows) := by
  rw [satisfies_ofClauses, satisfies_ofClauses]
  constructor
  · intro model row member
    exact (raw_clause_model row values).mp (model _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  · intro model row member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (raw_clause_model original values).mpr (model original present)

/-- A finite variable representation and its natural-ID literal pairs have
exactly the same existence of a model. -/
theorem raw_rows_satisfiable (rows : List (Clause (Fin locals))) :
    Satisfiable (ofClauses rows) ↔
      Satisfiable (ofClauses (rows.map (List.map (fun literal => (literal.1.val, literal.2))))) := by
  constructor
  · rintro ⟨values, model⟩
    refine ⟨extendNat values, (raw_rows_model rows _).mpr ?_⟩
    simpa only [restrictNat_extendNat] using model
  · rintro ⟨values, model⟩
    exact ⟨restrictNat values, (raw_rows_model rows values).mp model⟩

/-- The finite resident constructor decides precisely the source rows with
physical nonemptiness, including its real reserved directory and scan choice. -/
theorem constructor_satisfiable_iff (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (initial : Dictionary ambient) (coherent : Coherent initial)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient) :
    Satisfiable (constructorFormula heap layout initial coherent references channels within) ↔
      ∃ assignment : Fin ambient → Bool, Satisfies assignment (ofClauses (originalRows references)) ∧
        ∃ channel : Fin channels, assignment ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ = true := by
  unfold constructorFormula
  rw [raw_rows_satisfiable, constructor_clauses_raw]
  exact nonemptyRows_satisfiable initial coherent (originalRows references) channels within

end Controller.Cost.ForestZeroNonemptyImage
