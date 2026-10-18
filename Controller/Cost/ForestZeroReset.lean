module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroDictionary

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A uniform reset loop reads retained original coordinates from the reserved
inverse region and clears their shared slot cells. The loop count is the actual
local count; no ambient scan, per-root allocation or generated clear code is
used. The fixed code preserves both region bases and the caller's frames. -/
namespace Controller.Cost.ForestZeroReset
open Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroTouch

/-- Registers are remaining count, table base, inverse base and scratch. -/
def code (width base : ℕ) : Controller.Cost.GateProgram.Code width :=
  [.branchZero 0 (word width (base + 12)),
   .constant 3 (word width (2 ^ width - 1)), .add 0 0 3,
   .add 3 2 0, .load 3 3, .add 3 1 3,
   .push 0, .constant 0 (word width 0), .store 3 0, .pop 0,
   .constant 3 (word width 0), .branchZero 3 (word width base)]

@[simp] theorem code_length : (code width base).length = 12 := rfl

/-- The physical array recurrence performs an actual inverse-cell lookup and
one slot update at each retained index, descending from the supplied count. -/
def resetHeap (width tableBase inverseBase : ℕ) : Array (Word width) → ℕ → Array (Word width)
  | heap, 0 => heap
  | heap, count + 1 =>
      let coordinate := (heap[inverseBase + count]?.getD (word width 0)).val
      resetHeap width tableBase inverseBase
        (heap.setIfInBounds (tableBase + coordinate) (word width 0)) count

@[simp] theorem resetHeap_size (heap : Array (Word width)) (tableBase inverseBase count : ℕ) :
    (resetHeap width tableBase inverseBase heap count).size = heap.size := by
  induction count generalizing heap with
  | zero => rfl
  | succ count ih =>
      simpa only [resetHeap, Array.size_setIfInBounds] using
        (ih (heap.setIfInBounds
          (tableBase + (heap[inverseBase + count]?.getD (word width 0)).val) (word width 0)))

/-- Inverse storage is independent of the partially cleared slot table. -/
def InverseStored (heap : Array (Word width)) (inverseBase : ℕ)
    (coordinates : Array (Fin ambient)) : Prop :=
  ∀ (index : ℕ) (coordinate : Fin ambient), coordinates[index]? = some coordinate →
    heap[inverseBase + index]? = some (word width coordinate.val)

theorem represented_inverse (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state) :
    InverseStored heap layout.inverseBase state.coordinates := represented.inverse

/-- A table clear preserves every retained inverse coordinate because the two
reserved intervals are disjoint, including shared/repeated source occurrences. -/
theorem clear_inverse (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (coordinates : Array (Fin ambient)) (countBound : coordinates.size ≤ ambient)
    (stored : InverseStored heap layout.inverseBase coordinates) (coordinate : Fin ambient) :
    InverseStored (heap.setIfInBounds (layout.tableBase + coordinate.val) (word width 0))
      layout.inverseBase coordinates := by
  intro index other present
  have bounded := (Array.getElem?_eq_some_iff.mp present).1
  have separated := layout.addresses_ne coordinate index (by omega)
  rw [Array.getElem?_setIfInBounds_ne separated]
  exact stored index other present

/-- The inverse lookup used by the real reset recurrence returns the original
coordinate, with no supplied address-to-coordinate oracle. -/
theorem inverse_read (heap : Array (Word width)) (inverseBase : ℕ)
    (coordinates : Array (Fin ambient)) (stored : InverseStored heap inverseBase coordinates)
    (index : Fin coordinates.size) (ambientFits : ambient ≤ 2 ^ width) :
    (heap[inverseBase + index.val]?.getD (word width 0)).val = coordinates[index.val].val := by
  have present : coordinates[index.val]? = some coordinates[index.val] := by
    simp only [Array.getElem?_eq_getElem index.isLt]
  rw [stored index.val coordinates[index.val] present]
  simp only [Option.getD_some]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le coordinates[index.val].isLt ambientFits)

/-- All cells outside the entire table interval survive one actual clear. -/
theorem clear_outside (heap : Array (Word width)) (tableBase : ℕ)
    (coordinate : Fin ambient) (address : ℕ)
    (outside : address < tableBase ∨ tableBase + ambient ≤ address) :
    (heap.setIfInBounds (tableBase + coordinate.val) (word width 0))[address]? = heap[address]? := by
  have bounded := coordinate.isLt
  have different : tableBase + coordinate.val ≠ address := by rcases outside with before | after <;> omega
  exact Array.getElem?_setIfInBounds_ne different

/-- Clearing a slot cannot turn any already-zero cell nonzero, even when that
cell is selected again by a repeated stored coordinate. -/
theorem reset_zero_retained (heap : Array (Word width)) (tableBase inverseBase count address : ℕ)
    (zero : heap[address]? = some (word width 0)) :
    (resetHeap width tableBase inverseBase heap count)[address]? = some (word width 0) := by
  induction count generalizing heap with
  | zero => exact zero
  | succ count ih =>
      apply ih
      have valid := (Array.getElem?_eq_some_iff.mp zero).1
      rw [Array.getElem?_setIfInBounds]
      by_cases same : tableBase + (heap[inverseBase + count]?.getD (word width 0)).val = address
      · rw [ite_eq_left same, same, ite_eq_left valid]
      · rw [ite_eq_right same]; exact zero

/-- Every retained coordinate in the processed prefix is cleared by the actual
inverse lookup recurrence. Layout separation supplies inverse stability at each
step; the table itself may already contain zeros from earlier clear steps. -/
theorem reset_clears (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (coordinates : Array (Fin ambient)) (countBound : coordinates.size ≤ ambient)
    (stored : InverseStored heap layout.inverseBase coordinates)
    (ambientFits : ambient ≤ 2 ^ width) (count : ℕ) (remaining : count ≤ coordinates.size)
    (index : ℕ) (coordinate : Fin ambient) (present : coordinates[index]? = some coordinate)
    (processed : index < count) :
    (resetHeap width layout.tableBase layout.inverseBase heap count)[layout.tableBase + coordinate.val]? =
      some (word width 0) := by
  induction count generalizing heap index coordinate with
  | zero => omega
  | succ count ih =>
      let current : Fin coordinates.size := ⟨count, by omega⟩
      let original := coordinates[count]'current.isLt
      have actual := inverse_read heap layout.inverseBase coordinates stored current ambientFits
      change (heap[layout.inverseBase + count]?.getD (word width 0)).val = original.val at actual
      rw [resetHeap, actual]
      let cleared := heap.setIfInBounds (layout.tableBase + original.val) (word width 0)
      have nextStored := clear_inverse heap layout coordinates countBound stored original
      let nextLayout : Layout ambient cleared.size :=
        { tableBase := layout.tableBase
          inverseBase := layout.inverseBase
          tableBound := by simpa [cleared] using layout.tableBound
          inverseBound := by simpa [cleared] using layout.inverseBound
          disjoint := layout.disjoint }
      by_cases last : index = count
      · subst index
        have currentPresent : coordinates[count]? = some original := by
          exact Array.getElem?_eq_getElem current.isLt
        have equal : original = coordinate := Option.some.inj (currentPresent.symm.trans present)
        subst coordinate
        apply reset_zero_retained
        exact Array.getElem?_setIfInBounds_self_of_lt (layout.table_valid original)
      · exact ih cleared nextLayout nextStored (by omega) index coordinate present (by omega)

/-- Coherence turns the touched-prefix reset into an all-zero shared slot table:
unseen slots stay zero; every positive slot decodes to a cleared retained entry. -/
theorem reset_slots_zero (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (ambientFits : ambient ≤ 2 ^ width) (coordinate : Fin ambient) :
    (resetHeap width layout.tableBase layout.inverseBase heap state.coordinates.size)[layout.tableBase + coordinate.val]? =
      some (word width 0) := by
  by_cases unseen : state.slots[coordinate.val] = 0
  · apply reset_zero_retained
    simpa only [unseen] using represented.slots coordinate
  · have encoded : state.slots[coordinate.val] = (state.slots[coordinate.val] - 1) + 1 := by omega
    have present := (represented.coherent coordinate _).mp encoded
    have bounded := (Array.getElem?_eq_some_iff.mp present).1
    exact reset_clears heap layout state.coordinates
      (count_le_ambient state represented.coherent) represented.inverse ambientFits
      state.coordinates.size (Nat.le_refl _) _ coordinate present bounded


private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) (fits : cursor < 2 ^ width) :
    (atState heap cursor x0 x1 x2 x3 stack output).advance =
      atState heap (cursor + 1) x0 x1 x2 x3 stack output := by
  simp [atState, State.advance, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put0_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 0 (word width value) =
      atState heap cursor value x1 x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put3_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 3 (word width value) =
      atState heap cursor x0 x1 x2 value stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

/-- One nonempty reset iteration consists of twelve actual fetched instructions:
a stored inverse read, one shared-table clear, and a return to the loop head. -/
theorem iteration_execution (program : Program width 4) (heap : Array (Word width))
    (base tableBase inverseBase count coordinate scratch : ℕ) (stack output : List (Word width))
    (countFits : count + 1 < 2 ^ width)
    (inverseFits : inverseBase + count < 2 ^ width)
    (inverseValid : inverseBase + count < heap.size)
    (coordinateFits : coordinate < 2 ^ width)
    (slotFits : tableBase + coordinate < 2 ^ width)
    (slotValid : tableBase + coordinate < heap.size)
    (stored : heap[inverseBase + count]'inverseValid = word width coordinate)
    (programFits : base + 12 < 2 ^ width)
    (block : Controller.Cost.GateProgram.BlockAt program base (code width base)) :
    Execution program
      (atState heap base (count + 1) tableBase inverseBase scratch stack output)
      (atState (heap.setIfInBounds (tableBase + coordinate) (word width 0))
        base count tableBase inverseBase 0 stack output)
      12 (6 + heap.size + stack.length + output.length) := by
  let cleared := heap.setIfInBounds (tableBase + coordinate) (word width 0)
  let s0 := atState heap base (count + 1) tableBase inverseBase scratch stack output
  let s1 := atState heap (base + 1) (count + 1) tableBase inverseBase scratch stack output
  let s2 := atState heap (base + 2) (count + 1) tableBase inverseBase (2 ^ width - 1) stack output
  let s3 := atState heap (base + 3) count tableBase inverseBase (2 ^ width - 1) stack output
  let s4 := atState heap (base + 4) count tableBase inverseBase (inverseBase + count) stack output
  let s5 := atState heap (base + 5) count tableBase inverseBase coordinate stack output
  let s6 := atState heap (base + 6) count tableBase inverseBase (tableBase + coordinate) stack output
  let s7 := atState heap (base + 7) count tableBase inverseBase (tableBase + coordinate)
    (word width count :: stack) output
  let s8 := atState heap (base + 8) 0 tableBase inverseBase (tableBase + coordinate)
    (word width count :: stack) output
  let s9 := atState cleared (base + 9) 0 tableBase inverseBase (tableBase + coordinate)
    (word width count :: stack) output
  let s10 := atState cleared (base + 10) count tableBase inverseBase (tableBase + coordinate) stack output
  let s11 := atState cleared (base + 11) count tableBase inverseBase 0 stack output
  let s12 := atState cleared base count tableBase inverseBase 0 stack output
  have countWord : (word width count).val = count := Nat.mod_eq_of_lt (by omega)
  have positiveWord : (word width (count + 1)).val = count + 1 := Nat.mod_eq_of_lt countFits
  have inverseWord : (word width inverseBase).val = inverseBase := Nat.mod_eq_of_lt (by omega)
  have coordinateWord : (word width coordinate).val = coordinate := Nat.mod_eq_of_lt coordinateFits
  have tableWord : (word width tableBase).val = tableBase := Nat.mod_eq_of_lt (by omega)
  have inverseAddressWord : (word width (inverseBase + count)).val = inverseBase + count := Nat.mod_eq_of_lt inverseFits
  have slotWord : (word width (tableBase + coordinate)).val = tableBase + coordinate := Nat.mod_eq_of_lt slotFits
  have maximumFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have maximumWord : (word width (2 ^ width - 1)).val = 2 ^ width - 1 := Nat.mod_eq_of_lt maximumFits
  have decoded : word width ((count + 1) + (2 ^ width - 1)) = word width count := by
    have same : (count + 1) + (2 ^ width - 1) = count + 2 ^ width := by have := Nat.two_pow_pos width; omega
    apply Fin.ext
    simp only [word, same, Nat.add_mod_right]
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.branchZero 0 (word width (base + 12))) rfl (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    change some (if (word width (count + 1)).val = 0 then
      { s0.advance with pc := word width (base + 12) } else s0.advance) = some s1
    rw [positiveWord, ite_eq_right (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.constant 3 (word width (2 ^ width - 1))) rfl (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    change some (s1.advance.put 3 (word width (2 ^ width - 1))) = some s2
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.add 0 0 3) rfl (by omega)
      (by simpa [code] using block 2 (by simp [code]))]
    change some (s2.advance.put 0 (word width ((word width (count + 1)).val +
      (word width (2 ^ width - 1)).val))) = some s3
    rw [positiveWord, maximumWord, decoded, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.add 3 2 0) rfl (by omega)
      (by simpa [code] using block 3 (by simp [code]))]
    change some (s3.advance.put 3 (word width ((word width inverseBase).val + (word width count).val))) = some s4
    rw [inverseWord, countWord, advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.load 3 3) rfl (by omega)
      (by simpa [code] using block 4 (by simp [code]))]
    change (if valid : (word width (inverseBase + count)).val < heap.size then
      some (s4.advance.put 3 heap[(word width (inverseBase + count)).val]) else none) = some s5
    rw [inverseAddressWord, dite_eq_left inverseValid, stored,
      advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.add 3 1 3) rfl (by omega)
      (by simpa [code] using block 5 (by simp [code]))]
    change some (s5.advance.put 3 (word width ((word width tableBase).val + (word width coordinate).val))) = some s6
    rw [tableWord, coordinateWord, advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.push 0) rfl (by omega)
      (by simpa [code] using block 6 (by simp [code]))]
    change some { s6.advance with stack := word width count :: stack } = some s7
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (base + 7) (.constant 0 (word width 0)) rfl (by omega)
      (by simpa [code] using block 7 (by simp [code]))]
    change some (s7.advance.put 0 (word width 0)) = some s8
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (base + 8) (.store 3 0) rfl (by omega)
      (by simpa [code] using block 8 (by simp [code]))]
    change (if valid : (word width (tableBase + coordinate)).val < heap.size then
      some { s8.advance with heap := (heap.set (word width (tableBase + coordinate)).val (word width 0)) }
      else none) = some s9
    rw [slotWord, dite_eq_left slotValid, advance_at _ _ _ _ _ _ _ _ (by omega)]
    simp only [s9, cleared, Array.setIfInBounds_def, dite_eq_left slotValid] <;> rfl
  have t9 : programStep program s9 = some s10 := by
    rw [fetched program s9 (base + 9) (.pop 0) rfl (by omega)
      (by simpa [code] using block 9 (by simp [code]))]
    change some { s9.advance.put 0 (word width count) with stack := stack } = some s10
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at] <;> rfl
  have t10 : programStep program s10 = some s11 := by
    rw [fetched program s10 (base + 10) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [code] using block 10 (by simp [code]))]
    change some (s10.advance.put 3 (word width 0)) = some s11
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t11 : programStep program s11 = some s12 := by
    rw [fetched program s11 (base + 11) (.branchZero 3 (word width base)) rfl (by omega)
      (by simpa [code] using block 11 (by simp [code]))]
    change some (if (word width 0).val = 0 then { s11.advance with pc := word width base }
      else s11.advance) = some s12
    simp only [word, Nat.zero_mod, ite_true]
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
  have first := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3)))
  have second := Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl s6)))
  have third := Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9)))
  have fourth := Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.refl s12)))
  have joined := ((first.append second).append third).append fourth
  have smaller : 5 + heap.size + stack.length + output.length ≤
      6 + heap.size + stack.length + output.length := by omega
  convert joined using 1 <;>
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12,
      atState_liveWords, cleared, Array.size_setIfInBounds, List.length_cons,
      Nat.max_self, Nat.zero_add] <;> omega

/-- The complete reusable reset executes its fixed program over actual retained
inverse cells. Its cost is exactly twelve instructions per touched coordinate
and one final exit test; the source and inverse intervals are never allocated or
scanned afresh. -/
theorem reset_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (coordinates : Array (Fin ambient))
    (countBound : coordinates.size ≤ ambient)
    (stored : InverseStored heap layout.inverseBase coordinates)
    (base scratch count : ℕ) (stack output : List (Word width))
    (remaining : count ≤ coordinates.size)
    (heapFits : heap.size < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + 12 < 2 ^ width)
    (block : Controller.Cost.GateProgram.BlockAt program base (code width base)) :
    Execution program
      (atState heap base count layout.tableBase layout.inverseBase scratch stack output)
      (atState (resetHeap width layout.tableBase layout.inverseBase heap count)
        (base + 12) 0 layout.tableBase layout.inverseBase
        (if count = 0 then scratch else 0) stack output)
      (12 * count + 1)
      ((if count = 0 then 5 else 6) + heap.size + stack.length + output.length) := by
  induction count generalizing heap scratch with
  | zero =>
      let initial := atState heap base 0 layout.tableBase layout.inverseBase scratch stack output
      let final := atState heap (base + 12) 0 layout.tableBase layout.inverseBase scratch stack output
      have transition : programStep program initial = some final := by
        rw [fetched program initial base (.branchZero 0 (word width (base + 12))) rfl (by omega)
          (by simpa [code] using block 0 (by simp [code]))]
        change some (if (word width 0).val = 0 then
          { initial.advance with pc := word width (base + 12) } else initial.advance) = some final
        simp only [word, Nat.zero_mod, ite_true]
        rw [advance_at _ _ _ _ _ _ _ _ (by omega)] <;> rfl
      have actual := Execution.cons transition (Execution.refl final)
      simpa [resetHeap, initial, final, atState_liveWords] using actual
  | succ count ih =>
      let current : Fin coordinates.size := ⟨count, by omega⟩
      let coordinate := coordinates[count]'current.isLt
      have actualRead := inverse_read heap layout.inverseBase coordinates stored current (by omega)
      change (heap[layout.inverseBase + count]?.getD (word width 0)).val = coordinate.val at actualRead
      have inverseValid := layout.inverse_valid count (by omega)
      have tableValid := layout.table_valid coordinate
      have present : coordinates[count]? = some coordinate := Array.getElem?_eq_getElem current.isLt
      have getter : heap[layout.inverseBase + count]'inverseValid = word width coordinate.val := by
        have entry := stored count coordinate present
        rw [Array.getElem?_eq_getElem inverseValid] at entry
        exact Option.some.inj entry
      let cleared := heap.setIfInBounds (layout.tableBase + coordinate.val) (word width 0)
      let nextLayout : Layout ambient cleared.size :=
        { tableBase := layout.tableBase
          inverseBase := layout.inverseBase
          tableBound := by simpa [cleared] using layout.tableBound
          inverseBound := by simpa [cleared] using layout.inverseBound
          disjoint := layout.disjoint }
      have nextStored := clear_inverse heap layout coordinates countBound stored coordinate
      have first := iteration_execution program heap base layout.tableBase layout.inverseBase
        count coordinate.val scratch stack output (by omega) (by omega) inverseValid (by
          have := coordinate.isLt; omega) (by omega) tableValid getter programFits block
      have rest := ih cleared nextLayout nextStored 0 (by omega)
        (by simpa [cleared] using heapFits)
      have joined := first.append rest
      have smaller : 5 + heap.size + stack.length + output.length ≤
          6 + heap.size + stack.length + output.length := by omega
      convert joined using 1
      · simp [resetHeap, actualRead, cleared, nextLayout]
      · omega
      · by_cases empty : count = 0 <;>
          simp [empty, nextLayout, cleared, Nat.max_eq_left smaller]

end Controller.Cost.ForestZeroReset
