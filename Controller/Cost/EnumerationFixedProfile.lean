module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSlotSource

@[expose] public section

/-! A fixed directory template for runtime unit slots. Each selected slot has
one literal, and the trailing reserved row is empty. Row counts, literal counts
and directory instructions are independent of the prefix flag values. -/
namespace Controller.Cost.EnumerationFixedProfile
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestZeroAssembly Controller.Cost.EnumerationSlotBatch

def selectedRefs (slots : List (Slot ambient)) (trueFlags falseFlags : Slot ambient → Bool) :
    List (List (Reference ambient)) := slots.map (fun slot => [chosen slot trueFlags falseFlags])

def references (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient))
    (trueFlags falseFlags : Slot ambient → Bool) : List (List (Reference ambient)) :=
  baseRefs ++ selectedRefs slots trueFlags falseFlags ++ [[]]

def template (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    List (Clause (Fin ambient)) :=
  originalRows baseRefs ++ slots.map (fun slot => [(slot.inactive.coordinate, slot.inactive.positive)]) ++ [[]]

@[simp] theorem references_length (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (references baseRefs slots trueFlags falseFlags).length = baseRefs.length + slots.length + 1 := by
  simp [references, selectedRefs]
  omega

theorem selectedRefs_flatten (slots : List (Slot ambient)) :
    (selectedRefs slots trueFlags falseFlags).flatten = slots.map (fun slot => chosen slot trueFlags falseFlags) := by
  induction slots with
  | nil => rfl
  | cons slot rest ih => simpa [selectedRefs] using congrArg (List.cons (chosen slot trueFlags falseFlags)) ih

@[simp] theorem references_flatten (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (references baseRefs slots trueFlags falseFlags).flatten =
      baseRefs.flatten ++ slots.map (fun slot => chosen slot trueFlags falseFlags) := by
  simp [references, selectedRefs_flatten]

@[simp] theorem references_literals (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (references baseRefs slots trueFlags falseFlags).flatten.length = baseRefs.flatten.length + slots.length := by
  simp

@[simp] theorem template_length (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (template baseRefs slots).length = baseRefs.length + slots.length + 1 := by
  simp [template, originalRows]
  omega

theorem profile (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    (originalRows (references baseRefs slots trueFlags falseFlags)).map List.length =
      (template baseRefs slots).map List.length := by
  simp [references, selectedRefs, template, originalRows, List.map_map, Function.comp_def]

theorem directory_code_profile (left : List (Clause α)) (right : List (Clause β))
    (same : left.map List.length = right.map List.length) :
    ForestZeroDirectory.code width left = ForestZeroDirectory.code width right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons row rest => simp at same
  | cons row rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      simp only [ForestZeroDirectory.code, ForestZeroQuery.countClause_exact, same.1, ih tail same.2]

theorem directory_code (baseRefs : List (List (Reference ambient))) (slots : List (Slot ambient)) :
    ForestZeroDirectory.code width (originalRows (references baseRefs slots trueFlags falseFlags)) =
      ForestZeroDirectory.code width (template baseRefs slots) :=
  directory_code_profile _ _ (profile baseRefs slots)

end Controller.Cost.EnumerationFixedProfile
