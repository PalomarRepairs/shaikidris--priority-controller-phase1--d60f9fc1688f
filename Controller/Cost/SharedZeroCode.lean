module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Mathlib.Data.List.Forall2
public import Controller.Cost.SharedZeroTemplate
public import Controller.Cost.ForestZeroAdmissibleCaller

@[expose] public section

/-! Source constructor instructions depend on occurrence slots and signs, so root coordinates can vary in one resident query program. -/
namespace Controller.Cost.SharedZeroCode
open Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit

def WireEqual (left right : Reference ambient) : Prop :=
  left.slot = right.slot ∧ left.activity = right.activity ∧ left.positive = right.positive

private theorem wire_refl (reference : Reference ambient) : WireEqual reference reference := ⟨rfl, rfl, rfl⟩

theorem read_congr (left right : Reference ambient) (same : WireEqual left right) :
    readCode width left = readCode width right := by
  simp only [readCode, same.1, same.2.1]

theorem literal_congr (left right : Reference ambient) (same : WireEqual left right) :
    literalCode width base left = literalCode width base right := by
  simp only [literalCode, read_congr left right same, same.2.2]

theorem emit_congr (left right : List (Reference ambient)) (same : List.Forall₂ WireEqual left right) :
    emitCode width base left = emitCode width base right := by
  induction same generalizing base with
  | nil => rfl
  | cons heads tails ih =>
    simp only [emitCode, literal_congr _ _ heads, ih]

private theorem directory_congr (left right : List (List (Reference ambient)))
    (same : List.Forall₂ (List.Forall₂ WireEqual) left right) :
    ForestZeroDirectory.code width (ForestZeroAssembly.originalRows left) =
      ForestZeroDirectory.code width (ForestZeroAssembly.originalRows right) := by
  induction same with
  | nil => rfl
  | cons heads tails ih =>
    simp only [ForestZeroAssembly.originalRows] at ih
    simp only [ForestZeroAssembly.originalRows, List.map_cons, ForestZeroDirectory.code,
      ForestZeroQuery.countClause_exact, List.length_map, heads.length_eq, List.append_assoc, ih]

private theorem flattened (left right : List (List (Reference ambient)))
    (same : List.Forall₂ (List.Forall₂ WireEqual) left right) : List.Forall₂ WireEqual left.flatten right.flatten := by
  induction same with
  | nil => exact .nil
  | cons heads tails ih =>
    simpa only [List.flatten_cons] using List.rel_append heads ih

theorem assembly_congr (left right : List (List (Reference ambient)))
    (same : List.Forall₂ (List.Forall₂ WireEqual) left right) :
    ForestZeroAssembly.assemblyCode width base left = ForestZeroAssembly.assemblyCode width base right := by
  simp only [ForestZeroAssembly.assemblyCode, directory_congr left right same,
    emit_congr left.flatten right.flatten (flattened left right same)]

theorem query_congr (left right : List (List (Reference ambient)))
    (same : List.Forall₂ (List.Forall₂ WireEqual) left right) :
    ForestZeroQueryCaller.queryCode width base protectedEnd left =
      ForestZeroQueryCaller.queryCode width base protectedEnd right := by
  simp only [ForestZeroQueryCaller.queryCode, same.length_eq,
    (flattened left right same).length_eq, assembly_congr left right same]

theorem constructor_congr (left right : List (List (Reference ambient)))
    (same : List.Forall₂ (List.Forall₂ WireEqual) left right) :
    ForestZeroAdmissibleCaller.constructorCode width base protectedEnd recordHeader endHeader returnPC left =
      ForestZeroAdmissibleCaller.constructorCode width base protectedEnd recordHeader endHeader returnPC right := by
  have reserved : List.Forall₂ (List.Forall₂ WireEqual)
      (ForestZeroAdmissibleCaller.reservedReferences left) (ForestZeroAdmissibleCaller.reservedReferences right) := by
    exact List.rel_append same (.cons .nil .nil)
  simp only [ForestZeroAdmissibleCaller.constructorCode,
    query_congr _ _ reserved]

def rootReference (channels nodes slot : Nat) (root : Fin nodes) : Reference (channels + nodes) where
  slot := slot
  raw := root.val
  activity := true
  coordinate := ⟨channels + root.val, by omega⟩
  positive := false

theorem constructor_root_irrel (baseRows : List (List (Reference (channels + nodes))))
    (left right : Fin nodes) :
    ForestZeroAdmissibleCaller.constructorCode width base protectedEnd recordHeader endHeader returnPC
      (baseRows ++ [[rootReference channels nodes slot left]]) =
    ForestZeroAdmissibleCaller.constructorCode width base protectedEnd recordHeader endHeader returnPC
      (baseRows ++ [[rootReference channels nodes slot right]]) := by
  apply constructor_congr
  have stable : List.Forall₂ (List.Forall₂ WireEqual) baseRows baseRows :=
    List.forall₂_same.mpr (fun row member => List.forall₂_same.mpr (fun reference present => wire_refl reference))
  exact List.rel_append stable (.cons (.cons ⟨rfl, rfl, rfl⟩ .nil) .nil)

end Controller.Cost.SharedZeroCode
