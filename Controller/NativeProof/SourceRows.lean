module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.LayoutTransport
public import Controller.NativeProof.Rows

@[expose] public section

/-! Actual source producer occurrences have separate original resolution IDs.
The source enumeration includes private fold outputs and retained observation
producers. This binding uses that enumeration directly. -/
namespace Controller.NativeProof.SourceRows
open Controller.CNF Controller.Resolution
open Controller.Native

def before (parameters : Parameters)
    (owner : Fin (SourceController.compile parameters).entries.length) :=
  ((SourceController.compile parameters).entries.take owner.val).flatMap
    fun entry => entry.producer.rows

def after (parameters : Parameters)
    (owner : Fin (SourceController.compile parameters).entries.length) :=
  ((SourceController.compile parameters).entries.drop (owner.val + 1)).flatMap
    fun entry => entry.producer.rows

theorem sourceClauses_split (parameters : Parameters)
    (owner : Fin (SourceController.compile parameters).entries.length) :
    ((SourceController.compile parameters).entries.flatMap fun entry => entry.producer.rows) =
      before parameters owner ++
        (SourceController.compile parameters).entries[owner.val].producer.rows ++
        after parameters owner := by
  have split : (SourceController.compile parameters).entries =
      (SourceController.compile parameters).entries.take owner.val ++
        [(SourceController.compile parameters).entries[owner.val]] ++
        (SourceController.compile parameters).entries.drop (owner.val + 1) := by
    calc
      _ = (SourceController.compile parameters).entries.take (owner.val + 1) ++
          (SourceController.compile parameters).entries.drop (owner.val + 1) :=
        (List.take_append_drop _ _).symm
      _ = _ := by rw [List.take_succ_eq_append_getElem owner.isLt]
  conv_lhs => rw [split]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, before, after]

def producerRow (parameters : Parameters) (rename : Nat → Fin v)
    (owner : Fin (SourceController.compile parameters).entries.length)
    (index : Fin (SourceController.compile parameters).entries[owner.val].producer.rows.length) :
    Rows.Available
      (initialState (relabel rename (SourceController.equationFormula parameters)))
      (Rows.mapClause rename
        (SourceController.compile parameters).entries[owner.val].producer.rows[index.val]) := by
  let position : Fin (SourceController.equationFormula parameters).clauses.size :=
    ⟨(before parameters owner).length + index.val, by
      simp only [SourceController.equationFormula, ofClauses, List.size_toArray]
      rw [sourceClauses_split parameters owner]
      simp only [List.length_append]
      have bound := index.isLt
      omega⟩
  have content : (SourceController.equationFormula parameters).clauses[position.val] =
      (SourceController.compile parameters).entries[owner.val].producer.rows[index.val] := by
    have listBound : (before parameters owner).length + index.val <
        ((SourceController.compile parameters).entries.flatMap fun entry => entry.producer.rows).length := by
      simpa [SourceController.equationFormula, ofClauses, position] using position.isLt
    change ((SourceController.compile parameters).entries.flatMap fun entry => entry.producer.rows)[
      (before parameters owner).length + index.val]'listBound = _
    simp [sourceClauses_split parameters owner, List.getElem_append, index.isLt]
  refine ⟨(before parameters owner).length + index.val + 1, ?_, ?_⟩
  · simpa only [content] using Rows.relabeled_row rename
      (SourceController.equationFormula parameters) position
  · simp only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map]
    exact Nat.succ_le_of_lt position.isLt

theorem producerRow_id (parameters : Parameters) (rename : Nat → Fin v)
    (owner : Fin (SourceController.compile parameters).entries.length)
    (index : Fin (SourceController.compile parameters).entries[owner.val].producer.rows.length) :
    (producerRow parameters rename owner index).id =
      (before parameters owner).length + index.val + 1 := rfl

/-- The full source input retains equation rows before its physical assertions. -/
theorem formula_as_rows (parameters : Parameters) :
    SourceController.formula parameters = ofClauses
      (((SourceController.compile parameters).entries.flatMap fun entry => entry.producer.rows) ++
        (SourceController.assertions parameters).map fun literal => [literal]) := by
  change ({ clauses :=
    ((SourceController.compile parameters).entries.flatMap fun entry => entry.producer.rows).toArray ++
    ((SourceController.assertions parameters).map fun literal => [literal]).toArray } : Formula Nat) = _
  simp [ofClauses, List.append_toArray]

def fullProducerRow (parameters : Parameters) (rename : Nat → Fin v)
    (owner : Fin (SourceController.compile parameters).entries.length)
    (index : Fin (SourceController.compile parameters).entries[owner.val].producer.rows.length) :
    Rows.Available (initialState (relabel rename (SourceController.formula parameters)))
      (Rows.mapClause rename
        (SourceController.compile parameters).entries[owner.val].producer.rows[index.val]) := by
  rw [formula_as_rows, sourceClauses_split parameters owner, List.append_assoc]
  exact Rows.framedRow rename (before parameters owner) _
    (after parameters owner ++ (SourceController.assertions parameters).map fun literal => [literal]) index

end Controller.NativeProof.SourceRows
