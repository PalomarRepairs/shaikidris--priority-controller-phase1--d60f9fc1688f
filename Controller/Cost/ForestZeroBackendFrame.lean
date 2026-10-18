module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.SourceDirectory

@[expose] public section

/-! Protected source cells survive query-local stores, allocation and cleanup.
The frame bounds refer to actual array cells; query headers must lie above the
protected prefix. Backend execution must establish these bounds at each store.
-/
namespace Controller.Cost.ForestZeroBackendFrame
open Controller.Cost

/-- A fixed physical prefix remains present and unchanged. -/
def PrefixFrame (prefixSize : Nat) (before after : Array (Word width)) : Prop :=
  prefixSize ≤ before.size ∧ prefixSize ≤ after.size ∧
    ∀ index, index < prefixSize → after[index]? = before[index]?

theorem refl (heap : Array (Word width)) (bound : prefixSize ≤ heap.size) :
    PrefixFrame prefixSize heap heap := ⟨bound, bound, fun _ _ => rfl⟩

theorem trans (first : PrefixFrame prefixSize before middle)
    (second : PrefixFrame prefixSize middle after) : PrefixFrame prefixSize before after :=
  ⟨first.1, second.2.1, fun index below =>
    (second.2.2 index below).trans (first.2.2 index below)⟩

theorem store (heap : Array (Word width)) (address : Nat) (value : Word width)
    (valid : address < heap.size) (above : prefixSize ≤ address)
    (bound : prefixSize ≤ heap.size) :
    PrefixFrame prefixSize heap (heap.set address value valid) := by
  refine ⟨bound, by simpa using bound, ?_⟩
  intro index below
  exact Array.getElem?_set_ne valid (by omega)

theorem allocate (heap : Array (Word width)) (value : Word width)
    (bound : prefixSize ≤ heap.size) : PrefixFrame prefixSize heap (heap.push value) := by
  refine ⟨bound, by simp; omega, ?_⟩
  intro index below
  rw [Array.getElem?_push]
  simp only [ite_eq_right (show index ≠ heap.size by omega)]

theorem release (heap : Array (Word width)) (above : prefixSize < heap.size) :
    PrefixFrame prefixSize heap heap.pop := by
  refine ⟨by omega, by simp; omega, ?_⟩
  intro index below
  rw [Array.getElem?_pop]
  split <;> simp_all <;> omega

/-- Reusable layouts put every mutable header after the protected source.
This obligation is stronger than a cold layout's header-before-directory bound.
-/
structure ReusableLayout (clauses : List (Controller.CNF.Clause (Fin n)))
    (prefixSize : Nat) extends Controller.Horn.SourceDirectory.Layout clauses where
  headersAbove : ∀ header ∈ [recordHeader, inputHeader, firstHeader,
    directoryHeader, endHeader], prefixSize ≤ header

 theorem directory_above (layout : ReusableLayout clauses prefixSize) :
    prefixSize < layout.directory := by
  have lower := layout.headersAbove layout.recordHeader (by simp)
  have upper := layout.headersBefore layout.recordHeader (by simp)
  omega

 theorem scratch_above (layout : ReusableLayout clauses prefixSize) :
    prefixSize ≤ layout.base := by
  have directory := directory_above layout
  have source := layout.directoryBefore
  have endpoint := layout.sourceBefore
  unfold Controller.Horn.SourceDirectory.sourceOffset at endpoint
  omega

 theorem header_store_frame (layout : ReusableLayout clauses prefixSize)
    (heap : Array (Word width)) (header : Nat) (value : Word width)
    (member : header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader])
    (valid : header < heap.size) :
    PrefixFrame prefixSize heap (heap.set header value valid) := by
  have above := layout.headersAbove header member
  exact store heap header value valid above (by omega)

end Controller.Cost.ForestZeroBackendFrame
