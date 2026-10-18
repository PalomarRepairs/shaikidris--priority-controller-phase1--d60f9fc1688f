module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroCompile

@[expose] public section

/-! Local dictionary models extend to source coordinates by a configurable
unused-coordinate value. Choosing true transports greatest models, including
coordinates absent from every emitted row. This is a semantic transport; the
physical dictionary, reset and output loops have separate execution contracts.
-/
namespace Controller.Cost.ForestZeroModelLift
open Controller.CNF Controller.Cost.ForestZeroCompile
variable {ambient : ℕ}

def lift (state : Dictionary ambient) (unused : Bool) (values : ℕ → Bool)
    (coordinate : Fin ambient) : Bool :=
  if state.slots[coordinate.val] = 0 then unused else values (state.slots[coordinate.val] - 1)

theorem lift_used (state : Dictionary ambient) (coherent : Coherent state)
    (unused : Bool) (values : ℕ → Bool) (index : ℕ) (coordinate : Fin ambient)
    (present : state.coordinates[index]? = some coordinate) :
    lift state unused values coordinate = values index := by
  have encoded := (coherent coordinate index).mpr present
  simp only [lift, encoded, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel]

theorem lift_unseen (state : Dictionary ambient) (unused : Bool) (values : ℕ → Bool)
    (coordinate : Fin ambient) (unseen : state.slots[coordinate.val] = 0) :
    lift state unused values coordinate = unused := by simp [lift, unseen]

private theorem clause_transport {α β : Type} (left : α → Bool) (right : β → Bool)
    {produced : Clause α} {original : Clause β}
    (same : List.Forall₂ (fun a b => LiteralHolds left a ↔ LiteralHolds right b)
      produced original) : ClauseHolds left produced ↔ ClauseHolds right original := by
  induction same with
  | nil => simp [ClauseHolds]
  | cons first rest ih => simpa only [clauseHolds_cons] using or_congr first ih

private theorem formula_transport {α β : Type} (left : α → Bool) (right : β → Bool)
    {produced : List (Clause α)} {original : List (Clause β)}
    (same : List.Forall₂ (fun a b => ClauseHolds left a ↔ ClauseHolds right b)
      produced original) : Satisfies left (ofClauses produced) ↔ Satisfies right (ofClauses original) := by
  simp only [satisfies_ofClauses]
  induction same with
  | nil => simp
  | cons first rest ih => simpa only [List.forall_mem_cons] using and_congr first ih

/-- Every configurable unused-coordinate extension preserves the actually
compiled rows; the inverse dictionary proves agreement at every occurrence. -/
theorem rows_lift_model (state : Dictionary ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient))) (unused : Bool) (values : ℕ → Bool) :
    Satisfies values (ofClauses (compileRows state rows).2.1) ↔
      Satisfies (lift (compileRows state rows).1 unused values) (ofClauses rows) := by
  have finalCoherent := (rows_dictionary state coherent rows).1
  apply formula_transport
  apply List.Forall₂.imp _ (rows_correspondence state coherent rows)
  intro produced original related
  apply clause_transport
  apply List.Forall₂.imp _ related
  intro output source same
  have value := lift_used _ finalCoherent unused values output.1 source.1 same.1
  simp only [LiteralHolds, value, same.2]

/-- A greatest local model becomes a greatest ambient model by setting every
unused source coordinate true. No enumeration of a support set is assumed. -/
theorem rows_greatest_lift (state : Dictionary ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient))) (values : ℕ → Bool)
    (model : Satisfies values (ofClauses (compileRows state rows).2.1))
    (greatest : ∀ alternative, Satisfies alternative (ofClauses (compileRows state rows).2.1) →
      ∀ index, index < (compileRows state rows).1.coordinates.size →
        alternative index = true → values index = true) :
    Satisfies (lift (compileRows state rows).1 true values) (ofClauses rows) ∧
      ∀ alternative, Satisfies alternative (ofClauses rows) → ∀ coordinate,
        alternative coordinate = true → lift (compileRows state rows).1 true values coordinate = true := by
  refine ⟨(rows_lift_model state coherent rows true values).mp model, ?_⟩
  intro alternative alternativeModel coordinate active
  let final := (compileRows state rows).1
  have finalCoherent := (rows_dictionary state coherent rows).1
  by_cases unseen : final.slots[coordinate.val] = 0
  · exact lift_unseen final true values coordinate unseen
  · have encoded : final.slots[coordinate.val] = (final.slots[coordinate.val] - 1) + 1 := by omega
    have present : final.coordinates[final.slots[coordinate.val] - 1]? = some coordinate :=
      (finalCoherent coordinate _).mp encoded
    have localModel := (rows_forward_model state coherent rows alternative).mpr alternativeModel
    have localActive : localAssignment final alternative (final.slots[coordinate.val] - 1) = true := by
      simp only [localAssignment, present, active]
    have bounded := (Array.getElem?_eq_some_iff.mp present).choose
    have chosen := greatest _ localModel _ bounded localActive
    change lift final true values coordinate = true
    simpa only [lift, ite_eq_right unseen] using chosen

/-- The finite backend need only dominate allocated local IDs. Its arbitrary
extension to natural IDs is irrelevant to the ambient greatest-model result. -/
theorem finite_greatest_lift (state : Dictionary ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient)))
    (values : Fin (compileRows state rows).1.coordinates.size → Bool)
    (model : Satisfies values (finiteRows (compileRows state rows).2.1 (rows_bounds state coherent rows)))
    (greatest : ∀ alternative,
      Satisfies alternative (finiteRows (compileRows state rows).2.1 (rows_bounds state coherent rows)) →
      Controller.Horn.Below alternative values) :
    Satisfies (lift (compileRows state rows).1 true (extendNat values)) (ofClauses rows) ∧
      ∀ alternative, Satisfies alternative (ofClauses rows) →
        Controller.Horn.Below alternative (lift (compileRows state rows).1 true (extendNat values)) := by
  apply rows_greatest_lift state coherent rows (extendNat values)
  · apply (finiteRows_model _ (rows_bounds state coherent rows) (extendNat values)).mp
    simpa only [restrictNat_extendNat] using model
  · intro alternative alternativeModel index bounded active
    have finiteModel := (finiteRows_model _ (rows_bounds state coherent rows) alternative).mpr alternativeModel
    have retained := greatest _ finiteModel ⟨index, bounded⟩ active
    simpa only [extendNat, dite_eq_left bounded] using retained

/-- The actual finite worklist result supplies both the model and bounded
local dominance required for the source greatest-model transport. -/
theorem worklist_greatest_lift (state : Dictionary ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient)))
    (dual : Controller.Horn.DualHorn
      (finiteRows (compileRows state rows).2.1 (rows_bounds state coherent rows)))
    (values : Vector Bool (compileRows state rows).1.coordinates.size)
    (returned : Controller.Horn.Worklist.solveFormula
      (finiteRows (compileRows state rows).2.1 (rows_bounds state coherent rows)) = some values) :
    Satisfies (lift (compileRows state rows).1 true (extendNat (fun i : Fin (compileRows state rows).1.coordinates.size => values[i.val])))
      (ofClauses rows) ∧
      ∀ alternative, Satisfies alternative (ofClauses rows) →
        Controller.Horn.Below alternative
          (lift (compileRows state rows).1 true (extendNat (fun i : Fin (compileRows state rows).1.coordinates.size => values[i.val]))) := by
  obtain ⟨model, greatest⟩ := Controller.Horn.Worklist.solveFormula_some_model _ dual values returned
  exact finite_greatest_lift state coherent rows (fun i => values[i.val]) model greatest

end Controller.Cost.ForestZeroModelLift
