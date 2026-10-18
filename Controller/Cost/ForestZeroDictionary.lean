module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroTouch
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-! A shared local-coordinate dictionary occupies disjoint slot and inverse
regions. Its exact inverse invariant derives fresh capacity from the finite
ambient domain. Two physical stores refine a first touch while preserving all
other cells. Initialization and the fetched touched-coordinate reset loop are
separate caller operations. -/
namespace Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroTouch

variable {ambient width : ℕ}

/-- Exact inversion forbids duplicate original coordinates in the local array. -/
theorem coordinates_injective (state : Dictionary ambient) (valid : Coherent state) :
    Function.Injective (fun index : Fin state.coordinates.size => state.coordinates[index.val]) := by
  intro left right same
  have leftPresent : state.coordinates[left.val]? = some state.coordinates[left.val] := by
    simp only [Array.getElem?_eq_getElem left.isLt]
  have rightPresent : state.coordinates[right.val]? = some state.coordinates[right.val] := by
    simp only [Array.getElem?_eq_getElem right.isLt]
  have leftSlot := (valid state.coordinates[left.val] left.val).mpr leftPresent
  have rightSlot := (valid state.coordinates[right.val] right.val).mpr rightPresent
  change state.coordinates[left.val] = state.coordinates[right.val] at same
  rw [same] at leftSlot
  apply Fin.ext
  omega

theorem count_le_ambient (state : Dictionary ambient) (valid : Coherent state) :
    state.coordinates.size ≤ ambient := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective _ (coordinates_injective state valid)

/-- A new coordinate fits the reserved inverse region without a free capacity
premise: its actual first-touch array remains injective in the ambient domain. -/
theorem fresh_capacity (state : Dictionary ambient) (valid : Coherent state)
    (coordinate : Fin ambient) (unseen : state.slots[coordinate.val] = 0) :
    state.coordinates.size < ambient := by
  have bounded := count_le_ambient (touch state coordinate).1
    (touch_coherent state valid coordinate)
  simp only [touch, ite_eq_left unseen, Array.size_push] at bounded
  omega

theorem encoded_bound (state : Dictionary ambient) (valid : Coherent state)
    (coordinate : Fin ambient) : state.slots[coordinate.val] ≤ state.coordinates.size := by
  by_cases unseen : state.slots[coordinate.val] = 0
  · omega
  · have encoded : state.slots[coordinate.val] = (state.slots[coordinate.val] - 1) + 1 := by omega
    have present := (valid coordinate _).mp encoded
    have bounded := (Array.getElem?_eq_some_iff.mp present).1
    omega

structure Layout (ambient heapSize : ℕ) where
  tableBase : ℕ
  inverseBase : ℕ
  tableBound : tableBase + ambient ≤ heapSize
  inverseBound : inverseBase + ambient ≤ heapSize
  disjoint : tableBase + ambient ≤ inverseBase ∨ inverseBase + ambient ≤ tableBase

namespace Layout

theorem table_valid (layout : Layout ambient heapSize) (coordinate : Fin ambient) :
    layout.tableBase + coordinate.val < heapSize := by
  have := layout.tableBound
  have := coordinate.isLt
  omega

theorem inverse_valid (layout : Layout ambient heapSize) (index : ℕ) (bounded : index < ambient) :
    layout.inverseBase + index < heapSize := by
  have := layout.inverseBound
  omega

theorem addresses_ne (layout : Layout ambient heapSize) (coordinate : Fin ambient)
    (index : ℕ) (bounded : index < ambient) :
    layout.tableBase + coordinate.val ≠ layout.inverseBase + index := by
  have := coordinate.isLt
  rcases layout.disjoint with before | after <;> omega

end Layout

/-- The table stores every encoded slot; the used inverse prefix stores the
actual original finite coordinate, retaining its local order. -/
structure Represented (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) : Prop where
  coherent : Coherent state
  slots : ∀ coordinate : Fin ambient,
    heap[layout.tableBase + coordinate.val]? = some (word width state.slots[coordinate.val])
  inverse : ∀ (index : ℕ) (coordinate : Fin ambient),
    state.coordinates[index]? = some coordinate →
    heap[layout.inverseBase + index]? = some (word width coordinate.val)

/-- These are the two actual indexed writes of the fixed first-touch kernel. -/
def freshHeap (heap : Array (Word width)) (tableBase inverseBase : ℕ)
    (state : Dictionary ambient) (coordinate : Fin ambient) : Array (Word width) :=
  (heap.setIfInBounds (tableBase + coordinate.val) (word width (state.coordinates.size + 1))).setIfInBounds
    (inverseBase + state.coordinates.size) (word width coordinate.val)

@[simp] theorem freshHeap_size (heap : Array (Word width)) (tableBase inverseBase : ℕ)
    (state : Dictionary ambient) (coordinate : Fin ambient) :
    (freshHeap heap tableBase inverseBase state coordinate).size = heap.size := by
  simp [freshHeap]

/-- Disjointness preserves the slot write through the inverse write, and every
old inverse cell through the new slot and terminal inverse stores. -/
theorem fresh_represented (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (coordinate : Fin ambient) (unseen : state.slots[coordinate.val] = 0) :
    Represented (freshHeap heap layout.tableBase layout.inverseBase state coordinate)
      { tableBase := layout.tableBase
        inverseBase := layout.inverseBase
        tableBound := by simpa using layout.tableBound
        inverseBound := by simpa using layout.inverseBound
        disjoint := layout.disjoint }
      (touch state coordinate).1 := by
  have capacity := fresh_capacity state represented.coherent coordinate unseen
  have slotValid := layout.table_valid coordinate
  have inverseValid := layout.inverse_valid state.coordinates.size capacity
  constructor
  · exact touch_coherent state represented.coherent coordinate
  · intro other
    change (freshHeap heap layout.tableBase layout.inverseBase state coordinate)[layout.tableBase + other.val]? =
      some (word width (touch state coordinate).1.slots[other.val])
    have separated := layout.addresses_ne other state.coordinates.size capacity
    unfold freshHeap
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm separated)]
    by_cases same : coordinate = other
    · subst other
      simp only [touch, ite_eq_left unseen, Vector.getElem_set_self]
      exact Array.getElem?_setIfInBounds_self_of_lt slotValid
    · have valuesDifferent : coordinate.val ≠ other.val := fun equality => same (Fin.ext equality)
      have addressesDifferent : layout.tableBase + coordinate.val ≠ layout.tableBase + other.val := by omega
      rw [Array.getElem?_setIfInBounds_ne addressesDifferent]
      simpa only [touch, ite_eq_left unseen,
        Vector.getElem_set_ne coordinate.isLt other.isLt valuesDifferent] using represented.slots other
  · intro index other present
    change (freshHeap heap layout.tableBase layout.inverseBase state coordinate)[layout.inverseBase + index]? =
      some (word width other.val)
    simp only [touch, ite_eq_left unseen, Array.getElem?_push] at present
    by_cases last : index = state.coordinates.size
    · subst index
      simp only [ite_eq_left rfl] at present
      have same := Option.some.inj present
      subst other
      unfold freshHeap
      exact Array.getElem?_setIfInBounds_self_of_lt (by simpa using inverseValid)
    · simp only [ite_eq_right last] at present
      have bounded := (Array.getElem?_eq_some_iff.mp present).1
      have ambientBound := count_le_ambient state represented.coherent
      have separated := layout.addresses_ne coordinate index (by omega)
      have inverseDifferent : layout.inverseBase + state.coordinates.size ≠ layout.inverseBase + index := by omega
      unfold freshHeap
      rw [Array.getElem?_setIfInBounds_ne inverseDifferent,
        Array.getElem?_setIfInBounds_ne separated]
      exact represented.inverse index other present

/-- Every cell outside both written addresses is retained; this includes source
and solver frames whose separation the caller derives from its allocation. -/
theorem fresh_outside (heap : Array (Word width)) (tableBase inverseBase : ℕ)
    (state : Dictionary ambient) (coordinate : Fin ambient) (address : ℕ)
    (outsideTable : tableBase + coordinate.val ≠ address)
    (outsideInverse : inverseBase + state.coordinates.size ≠ address) :
    (freshHeap heap tableBase inverseBase state coordinate)[address]? = heap[address]? := by
  rw [freshHeap, Array.getElem?_setIfInBounds_ne outsideInverse,
    Array.getElem?_setIfInBounds_ne outsideTable]

/-- The full fetched first-touch call uses capacity and word fits derived from
its coherent stored dictionary and the actual reserved physical layout. -/
theorem fresh_execution_refines (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (coordinate : Fin ambient)
    (unseen : state.slots[coordinate.val] = 0) (base scratch : ℕ)
    (stack output : List (Word width))
    (heapFits : heap.size < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + 20 < 2 ^ width)
    (block : Controller.Cost.GateProgram.BlockAt program base (code width base)) :
    Execution program
      (atState heap base coordinate.val layout.tableBase state.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState (freshHeap heap layout.tableBase layout.inverseBase state coordinate)
        (base + 20) (touch state coordinate).2.1 layout.tableBase
        (touch state coordinate).1.coordinates.size 1
        (word width layout.inverseBase :: stack) output)
      15 (7 + heap.size + stack.length + output.length) := by
  have capacity := fresh_capacity state represented.coherent coordinate unseen
  have tableValid := layout.table_valid coordinate
  have inverseValid := layout.inverse_valid state.coordinates.size capacity
  have stored : heap[coordinate.val + layout.tableBase]'(by omega) = word width 0 := by
    have slot := represented.slots coordinate
    rw [unseen] at slot
    rw [Array.getElem?_eq_getElem tableValid] at slot
    have equality := Option.some.inj slot
    simpa only [Nat.add_comm] using equality
  have actual := touch_fresh_execution program heap base coordinate.val layout.tableBase
    state.coordinates.size scratch layout.inverseBase stack output
    (by omega) (by omega) (by omega) (by omega) inverseValid stored programFits block
  simpa only [touch, ite_eq_left unseen, Array.size_push, freshHeap,
    Array.setIfInBounds_def, dite_eq_left tableValid,
    dite_eq_left (show layout.inverseBase + state.coordinates.size <
      (heap.set (layout.tableBase + coordinate.val)
        (word width (state.coordinates.size + 1))).size by simpa only [Array.size_set] using inverseValid),
    Nat.add_comm] using actual

/-- A repeated-coordinate call returns the existing decoded local ID and leaves
both stored regions unchanged. No capacity premise or fresh allocation occurs. -/
theorem existing_execution_refines (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (coordinate : Fin ambient)
    (seen : state.slots[coordinate.val] ≠ 0) (base scratch : ℕ)
    (stack output : List (Word width))
    (heapFits : heap.size < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + 20 < 2 ^ width)
    (block : Controller.Cost.GateProgram.BlockAt program base (code width base)) :
    Execution program
      (atState heap base coordinate.val layout.tableBase state.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState heap (base + 20) (touch state coordinate).2.1 layout.tableBase
        (touch state coordinate).1.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      9 (7 + heap.size + stack.length + output.length) := by
  have tableValid := layout.table_valid coordinate
  have bounded := encoded_bound state represented.coherent coordinate
  have countBound := count_le_ambient state represented.coherent
  have stored : heap[coordinate.val + layout.tableBase]'(by omega) =
      word width state.slots[coordinate.val] := by
    have slot := represented.slots coordinate
    rw [Array.getElem?_eq_getElem tableValid] at slot
    have equality := Option.some.inj slot
    simpa only [Nat.add_comm] using equality
  have actual := touch_existing_execution program heap base coordinate.val layout.tableBase
    state.coordinates.size scratch state.slots[coordinate.val] layout.inverseBase stack output
    (by omega) (by omega) (by omega) (by omega) stored programFits block
  simpa only [touch, ite_eq_right seen] using actual

end Controller.Cost.ForestZeroDictionary
