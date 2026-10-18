module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroNonemptyImage

@[expose] public section

/-! The optional nonemptiness row preserves the exact dictionary lift of
the supplied local model, including its enabled-channel witness. -/
namespace Controller.Cost.ForestZeroSameLift
open Controller.CNF Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroNonemptyImage
variable {ambient : Nat}

theorem nonemptyRows_lift_model (initial : Dictionary ambient)
    (coherent : Coherent initial) (rows : List (Clause (Fin ambient)))
    (channels : Nat) (within : channels ≤ ambient) (values : Nat → Bool)
    (model : Satisfies values (ofClauses (nonemptyRows initial rows channels))) :
    Satisfies (ForestZeroModelLift.lift (compileRows initial rows).1 true values)
      (ofClauses rows) ∧
      ∃ channel : Fin channels,
        ForestZeroModelLift.lift (compileRows initial rows).1 true values
          ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ = true := by
  let final := (compileRows initial rows).1
  have valid : Coherent final := (rows_dictionary initial coherent rows).1
  rcases ForestZeroNonempty.search_outcome final valid channels within with
    ⟨unused, _, _⟩ | ⟨covered, _, allUsed⟩
  · have choice : nonemptyRows initial rows channels = (compileRows initial rows).2.1 := by
      have actual := unused
      dsimp only [final] at actual
      simp [nonemptyRows, actual]
    rw [choice] at model
    exact ForestZeroNonempty.unused_preserves_existing_model initial coherent rows
      channels within values model unused
  · have choice : nonemptyRows initial rows channels = (compileRows initial rows).2.1 ++
        [ForestZeroPositive.positiveClause final channels] := by
      have actual := covered
      dsimp only [final] at actual
      simp only [nonemptyRows, actual, ite_true]
      rfl
    rw [choice] at model
    have split : Satisfies values (ofClauses (compileRows initial rows).2.1) ∧
        ClauseHolds values (ForestZeroPositive.positiveClause final channels) := by
      rw [satisfies_ofClauses] at model ⊢
      exact ⟨fun row member => model row (List.mem_append_left _ member),
        model _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
    exact ⟨(ForestZeroModelLift.rows_lift_model initial coherent rows true values).mp split.1,
      (ForestZeroPositive.positiveClause_holds final values true channels within allUsed).mp
        split.2⟩

end Controller.Cost.ForestZeroSameLift
