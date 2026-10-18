module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverDispatch

@[expose] public section

/-! Every block's absolute endpoint is bounded by the complete driver extent.
These bounds derive local fetched-instruction capacities from one global bound. -/
namespace Controller.Cost.EnumerationDriverBounds
open Controller.Decoder Controller.Native Controller.Cost.GateProgram
open Controller.Cost.EnumerationDriverCode Controller.Cost.EnumerationDriverLayout

private theorem offset_end (sizes : List Nat) (entry index : Nat) (inside : index < sizes.length) :
    (offsets entry sizes)[index]'(by simpa using inside) + sizes[index] ≤ entry + sizes.sum := by
  induction sizes generalizing entry index with
  | nil => simp at inside
  | cons size rest ih =>
    cases index with
    | zero => simp only [offsets, List.getElem_cons_zero, List.sum_cons]; omega
    | succ index =>
      have next := ih (entry + size) index (by simpa using inside)
      simpa only [offsets, List.getElem_cons_succ, List.sum_cons, Nat.add_assoc] using next

theorem block_end (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (index : Nat) (inside : index < 17) :
    ((entries (labels parameters graph width entry))[index]'(by simpa [entries] using inside)) +
      ((chunks parameters graph width entry rows roots)[index]'(by simpa [chunks] using inside)).length ≤
        entry + (code parameters graph width entry rows roots).length := by
  have valid : index < (chunks parameters graph width entry rows roots).length := by simpa [chunks] using inside
  have validMap : index < ((chunks parameters graph width entry rows roots).map List.length).length := by simpa using valid
  have bound := offset_end ((chunks parameters graph width entry rows roots).map List.length) entry index validMap
  have addressEq := congrArg (fun values : List Nat => values[index]?) (entries_eq parameters graph width entry rows roots)
  rw [List.getElem?_eq_getElem (by simpa [entries] using inside), List.getElem?_eq_getElem (by simpa using validMap)] at addressEq
  have exactAddress := Option.some.inj addressEq
  simpa only [exactAddress, List.getElem_map, code, List.length_flatten] using bound

theorem block_room (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (room : entry + (code parameters graph width entry rows roots).length < 2 ^ width)
    (index : Nat) (inside : index < 17) :
    ((entries (labels parameters graph width entry))[index]'(by simpa [entries] using inside)) +
      ((chunks parameters graph width entry rows roots)[index]'(by simpa [chunks] using inside)).length < 2 ^ width :=
  (block_end parameters graph width entry rows roots index inside).trans_lt room

end Controller.Cost.EnumerationDriverBounds
