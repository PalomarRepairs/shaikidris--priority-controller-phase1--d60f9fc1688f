module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.Wrapper
public import Mathlib.Data.List.Dedup

@[expose] public section

/-! A deterministic finite coding preserves the optional input's ordered clauses. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Native.ObservationProjection
variable {internalCount : Nat}

abbrev WrapperLabel (parameters : Parameters) (internalCount : Nat) :=
  Sum Nat (PrivateActivity (Fin internalCount) (Fin parameters.decoder.roots.length))

local instance (parameters : Parameters) : BEq (WrapperLabel parameters internalCount) :=
  ⟨fun first second => decide (first = second)⟩

local instance (parameters : Parameters) : LawfulBEq (WrapperLabel parameters internalCount) where
  eq_of_beq := by intro first second same; exact of_decide_eq_true same
  rfl := by intro label; exact decide_eq_true rfl

def canonicalWrapperLabels (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    List (WrapperLabel parameters internalCount) :=
  ((optionalInputRows parameters wrapper).flatMap (fun clause => clause.map Prod.fst)).dedup

def canonicalWrapperCount (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) : Nat :=
  (canonicalWrapperLabels parameters wrapper).length + 1

def canonicalLabelIndex (parameters : Parameters) (labels : List (WrapperLabel parameters internalCount))
    (label : WrapperLabel parameters internalCount) : Fin (labels.length + 1) :=
  ⟨labels.idxOf label, Nat.lt_succ_of_le List.idxOf_le_length⟩

def canonicalWrapperRename (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    WrapperLabel parameters internalCount → Fin (canonicalWrapperCount parameters wrapper) :=
  fun label => canonicalLabelIndex parameters (canonicalWrapperLabels parameters wrapper) label

def canonicalWrapperDecode (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (code : Fin (canonicalWrapperCount parameters wrapper)) : WrapperLabel parameters internalCount :=
  ((canonicalWrapperLabels parameters wrapper)[code.val]?).getD (.inl 0)

theorem canonicalWrapperRename_roundtrip (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (label : WrapperLabel parameters internalCount) (present : label ∈ canonicalWrapperLabels parameters wrapper) :
    canonicalWrapperDecode parameters wrapper (canonicalWrapperRename parameters wrapper label) = label := by
  unfold canonicalWrapperDecode canonicalWrapperRename canonicalLabelIndex
  rw [List.getElem?_idxOf present]
  rfl

theorem canonicalWrapperLabels_contains (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length))
    (clause : Clause (WrapperLabel parameters internalCount)) (present : clause ∈ optionalInputRows parameters wrapper)
    (literal : Literal (WrapperLabel parameters internalCount)) (member : literal ∈ clause) :
    literal.1 ∈ canonicalWrapperLabels parameters wrapper := by
  apply List.mem_dedup.mpr
  exact List.mem_flatMap.mpr ⟨clause, present, List.mem_map.mpr ⟨literal, member, rfl⟩⟩

def canonicalOptionalInput (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    FiniteFormula (canonicalWrapperCount parameters wrapper) :=
  let labels := canonicalWrapperLabels parameters wrapper
  optionalFiniteInput parameters wrapper (fun label => canonicalLabelIndex parameters labels label)

theorem relabel_rows_roundtrip {α : Type} {size : Nat} (rows : List (Clause α))
    (encode : α → Fin size) (decode : Fin size → α)
    (inverse : ∀ clause ∈ rows, ∀ literal ∈ clause, decode (encode literal.1) = literal.1) :
    relabel decode (ofClauses (rows.map (Rows.mapClause encode))) = ofClauses rows := by
  have mapped : relabel decode (ofClauses (rows.map (Rows.mapClause encode))) =
      ofClauses ((rows.map (Rows.mapClause encode)).map (Controller.CNF.OrderedFormula.Clause.relabel decode)) := by
    simp [relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel, ofClauses]
  rw [mapped]
  apply congrArg ofClauses
  rw [List.map_map]
  calc
    rows.map (fun clause => Controller.CNF.OrderedFormula.Clause.relabel decode (Rows.mapClause encode clause)) = rows.map id := by
      apply List.map_congr_left
      intro clause present
      unfold Rows.mapClause Controller.CNF.OrderedFormula.Clause.relabel
      rw [List.map_map]
      calc
        clause.map (fun literal => (decode (encode literal.1), literal.2)) = clause.map id := by
          apply List.map_congr_left
          intro literal member
          exact Prod.ext (inverse clause present literal member) rfl
        _ = clause := List.map_id clause
    _ = rows := List.map_id rows

theorem canonicalOptionalInput_roundtrip (parameters : Parameters)
    (wrapper : OptionalWrapper Nat (Fin internalCount) (Fin parameters.decoder.roots.length)) :
    relabel (canonicalWrapperDecode parameters wrapper) (canonicalOptionalInput parameters wrapper) =
      ofClauses (optionalInputRows parameters wrapper) := by
  unfold canonicalOptionalInput optionalFiniteInput
  apply relabel_rows_roundtrip
  intro clause present literal member
  exact canonicalWrapperRename_roundtrip parameters wrapper literal.1
    (canonicalWrapperLabels_contains parameters wrapper clause present literal member)

end Controller.NativeProof.Wrapper
