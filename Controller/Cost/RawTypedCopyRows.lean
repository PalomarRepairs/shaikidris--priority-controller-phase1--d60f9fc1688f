module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RawTypedCopyPrefix

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.RawTypedCopy
open Controller.Cost
variable {width : Nat}
open Controller.Cost

/-- Original guard words are copied without rank conversion. Each source
occurrence is loaded once and allocated once, including duplicates. -/
def unchangedOccurrenceCopyCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 3 (word width done), .load 5 2, .allocate 5,
    .constant 5 (word width 1), .add 2 2 5, .add 3 3 7,
    .branchZero 6 (word width entry)]

theorem copyRegisters_initial_stream (state : State width 8) (cursor count : Nat)
    (cursorHeld : state.reg 2 = word width cursor) (countHeld : state.reg 3 = word width count)
    (zeroHeld : state.reg 6 = word width 0) (maskHeld : state.reg 7 = word width (2 ^ width - 1)) :
    state.reg = copyRegisters (state.reg 0) (state.reg 1) (word width cursor)
      (word width count) (state.reg 4) (state.reg 5) (word width 0) (word width (2 ^ width - 1)) := by
  funext register
  fin_cases register <;> simp [copyRegisters, cursorHeld, countHeld, zeroHeld, maskHeld]

def UnchangedStreamStored (heap : Array (Word width)) (cursor : Nat)
    (values : List (Word width)) : Prop :=
  ∀ index : Fin values.length, heap[cursor + index.val]? = some values[index.val]

theorem unchanged_occurrence_execution (resident : Program width 8)
    (entry done cursor count : Nat) (value : Word width) (state : State width 8)
    (physical : ∀ phase : Fin 7, resident[entry + phase.val]? =
      (unchangedOccurrenceCopyCode width entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 7 < 2 ^ width) (room : state.heap.size + 1 < 2 ^ width)
    (positive : 0 < count) (countFits : count < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (cursorHeld : state.reg 2 = word width cursor) (countHeld : state.reg 3 = word width count)
    (zeroHeld : state.reg 6 = word width 0) (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (sourceCell : state.heap[cursor]? = some value) :
    ∃ final peak, Execution resident state final 7 peak ∧ peak ≤ state.liveWords + 1 ∧
      final.heap = state.heap.push value ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 2 = word width (cursor + 1) ∧ final.reg 3 = word width (count - 1) ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 3 → register ≠ 5 →
        final.reg register = state.reg register) := by
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  let s1 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (cursor)) (word width (count)) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (cursor)) (word width (count)) (state.reg 4) (value) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (cursor)) (word width (count)) (state.reg 4) (value) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap.push value, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (cursor)) (word width (count)) (state.reg 4) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap.push value, pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (cursor + 1)) (word width (count)) (state.reg 4) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap.push value, pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (cursor + 1)) (word width (count - 1)) (state.reg 4) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap.push value, pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (cursor + 1)) (word width (count - 1)) (state.reg 4) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap.push value, pc := word width (entry) }
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 3 (word width done)) position (by omega)
      (by simpa [unchangedOccurrenceCopyCode] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 3 done count running positive countFits countHeld
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial_stream state cursor count cursorHeld countHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.load 5 2) (by rfl) (by omega)
      (by simpa [unchangedOccurrenceCopyCode] using physical ⟨1, by decide⟩)]
    have result := copy_load_step s1 5 2 cursor value running (by omega) (by rfl) sourceCell
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (cursor)) (word width (count)) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (value)) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.allocate 5) (by rfl) (by omega)
      (by simpa [unchangedOccurrenceCopyCode] using physical ⟨2, by decide⟩)]
    have result := copy_allocate_step s2 5 value running (by change state.heap.size < _; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 1 := by
    simp only [s3, State.liveWords, Array.size_push] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.constant 5 (word width 1)) (by rfl) (by omega)
      (by simpa [unchangedOccurrenceCopyCode] using physical ⟨3, by decide⟩)]
    have result := copy_constant_step s3 5 (word width 1) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (cursor)) (word width (count)) (state.reg 4) (value) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 1 := by
    simp only [s4, State.liveWords, Array.size_push] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [unchangedOccurrenceCopyCode] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 2 2 5 (cursor) (1) running (by omega) (by omega) (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (word width (cursor)) (word width (count)) (state.reg 4) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (cursor + 1))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 1 := by
    simp only [s5, State.liveWords, Array.size_push] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 3 3 7) (by rfl) (by omega)
      (by simpa [unchangedOccurrenceCopyCode] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 3 3 7 (count) (2 ^ width - 1) running (by omega) (by omega) (by rfl) (by rfl)
    rw [marker_word_decrement count positive countFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (cursor + 1)) (word width (count)) (state.reg 4) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (count - 1))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 1 := by
    simp only [s6, State.liveWords, Array.size_push] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.branchZero 6 (word width entry)) (by rfl) (by omega)
      (by simpa [unchangedOccurrenceCopyCode] using physical ⟨6, by decide⟩)]
    have result := copy_branch_zero s6 6 entry running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live7 : s7.liveWords = state.liveWords + 1 := by
    simp only [s7, State.liveWords, Array.size_push] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.refl s7)))))))
  refine ⟨s7, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (s7.liveWords))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, rfl, rfl, ?_⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, max_le_iff]
    omega
  · intro register notCursor notCount notTemporary
    fin_cases register <;> simp_all [s7, copyRegisters]

/-- One physical unchanged guard stream, with exact original order and repeats. -/
theorem unchanged_stream_execution (resident : Program width 8) (entry done : Nat)
    (physical : ∀ phase : Fin 7, resident[entry + phase.val]? =
      (unchangedOccurrenceCopyCode width entry done)[phase.val]?)
    (codeFits : entry + 7 < 2 ^ width) :
    ∀ (values : List (Word width)) (cursor : Nat) (state : State width 8),
      state.pc = word width entry → state.halted = false →
      state.heap.size + values.length < 2 ^ width → cursor + values.length < 2 ^ width →
      values.length < 2 ^ width → state.reg 2 = word width cursor →
      state.reg 3 = word width values.length → state.reg 6 = word width 0 →
      state.reg 7 = word width (2 ^ width - 1) → UnchangedStreamStored state.heap cursor values →
      ∃ final peak, Execution resident state final (7 * values.length + 1) peak ∧
        peak ≤ state.liveWords + values.length ∧ final.heap = state.heap ++ values.toArray ∧
        final.stack = state.stack ∧ final.output = state.output ∧
        final.pc = word width done ∧ final.halted = false ∧
        final.reg 2 = word width (cursor + values.length) ∧ final.reg 3 = word width 0 ∧
        (∀ register : Fin 8, register ≠ 2 → register ≠ 3 → register ≠ 5 →
          final.reg register = state.reg register) := by
  intro values
  induction values with
  | nil =>
    intro cursor state position running room cursorFits countFits cursorHeld countHeld zeroHeld maskHeld stored
    let final : State width 8 := { state.advance with pc := word width done }
    have transition : programStep resident state = some final := by
      rw [fetched resident state entry (.branchZero 3 (word width done)) position (by omega)
        (by simpa [unchangedOccurrenceCopyCode] using physical ⟨0, by decide⟩)]
      exact copy_branch_zero state 3 done running countHeld
    have trace := Execution.cons transition (Execution.refl final)
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, max state.liveWords final.liveWords, ?_, ?_, ?_, rfl, rfl, rfl,
      running, ?_, countHeld, ?_⟩
    · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using trace
    · simp only [live, max_self, List.length_nil, Nat.add_zero, Nat.le_refl]
    · change state.heap = state.heap ++ ([] : List (Word width)).toArray
      rw [copy_nil_array, Array.append_empty]
    · change state.reg 2 = word width cursor
      exact cursorHeld
    · intro register notCursor notCount notTemporary
      rfl
  | cons value rest ih =>
    intro cursor state position running room cursorFits countFits cursorHeld countHeld zeroHeld maskHeld stored
    have sourceCell : state.heap[cursor]? = some value := by
      simpa only [List.getElem_cons_zero, Nat.add_zero] using stored ⟨0, by simp⟩
    obtain ⟨middle, firstPeak, firstTrace, firstSpace, middleHeap, middleStack,
      middleOutput, middlePC, middleRunning, middleCursor, middleCount, frame⟩ :=
      unchanged_occurrence_execution resident entry done cursor (value :: rest).length value state
        physical position running codeFits (by simp only [List.length_cons] at room; omega)
        (by simp) countFits (by simp only [List.length_cons] at cursorFits; omega)
        cursorHeld countHeld zeroHeld maskHeld sourceCell
    have middleSize : middle.heap.size = state.heap.size + 1 := by rw [middleHeap, Array.size_push]
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]; omega
    have preserve : ∀ (address : Nat) (wordValue : Word width),
        state.heap[address]? = some wordValue → middle.heap[address]? = some wordValue := by
      intro address wordValue cell
      rw [middleHeap]
      exact copy_push_cell state.heap value wordValue address cell
    have restStored : UnchangedStreamStored middle.heap (cursor + 1) rest := by
      intro index
      have oldCell := stored ⟨index.val + 1, by have := index.isLt; simp only [List.length_cons]; omega⟩
      simp only [List.getElem_cons_succ] at oldCell
      have kept := preserve _ _ oldCell
      simpa only [Nat.add_assoc, Nat.add_comm 1 index.val] using kept
    obtain ⟨final, restPeak, restTrace, restSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalCursor, finalCount, finalFrame⟩ :=
      ih (cursor + 1) middle middlePC middleRunning
        (by simp only [List.length_cons] at room; rw [middleSize]; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at countFits; omega)
        middleCursor (by simpa only [List.length_cons, Nat.add_sub_cancel] using middleCount)
        ((frame 6 (by decide) (by decide) (by decide)).trans zeroHeld)
        ((frame 7 (by decide) (by decide) (by decide)).trans maskHeld) restStored
    refine ⟨final, max firstPeak restPeak, ?_, ?_, ?_, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, ?_, finalCount, ?_⟩
    · have trace := firstTrace.append restTrace
      convert trace using 1 <;> simp only [List.length_cons] <;> omega
    · rw [max_le_iff]
      constructor <;> simp only [List.length_cons] <;> omega
    · rw [finalHeap, middleHeap]
      have conversion := List.toArray_cons value rest
      rw [conversion]
      change (state.heap ++ #[value]) ++ rest.toArray = _
      exact Array.append_assoc
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using finalCursor
    · intro register notCursor notCount notTemporary
      exact (finalFrame register notCursor notCount notTemporary).trans
        (frame register notCursor notCount notTemporary)

/-- A selected row's original pointer and arity are fetched through Q. Offset0
selects child occurrences; offset1 selects guards. Counts and pointers come from
actual original packet cells, not an abstract incidence query. -/
def typedSliceSetupCode (width nodes base done stream offset : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done),
    .constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)),
    .load 2 2, .load 5 1, .add 5 5 5, .add 3 2 5,
    .constant 2 (word width (9 + 2 * nodes + offset)), .add 2 2 3, .load 2 2,
    .constant 5 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)),
    .load 5 5, .add 2 2 5,
    .constant 5 (word width (9 + 4 * nodes + offset)), .add 3 3 5, .load 3 3,
    .branchZero 6 (word width stream)]

def typedRowsBackedgeCode (width entry : Nat) : Program width 8 :=
  #[.constant 5 (word width 1), .add 1 1 5, .add 0 0 7,
    .branchZero 6 (word width entry)]

def typedChildrenCopyCode (width nodes base entry done : Nat) : Program width 8 :=
  typedSliceSetupCode width nodes base done (entry + 16) 0 ++
  mappedOccurrenceCopyCode width (entry + 16) (entry + 25) ++
  typedRowsBackedgeCode width entry

def typedGuardsCopyCode (width nodes base entry done : Nat) : Program width 8 :=
  typedSliceSetupCode width nodes base done (entry + 16) 1 ++
  unchangedOccurrenceCopyCode width (entry + 16) (entry + 23) ++
  typedRowsBackedgeCode width entry

-- Complete selected-child row cost16 setup +9k+1 stream +4 backedge =21+9k;
-- selected-guard row cost16 +7k+1 +4 =21+7k. Final outer test adds1.
-- Outer Q cursor/count remain in r1/r0 while inner count/source use r3/r2;
-- mapped/unchanged stream frames retain outer registers, rank4, zero6, mask7.
-- No charged stack fields or untracked temporary allocation are introduced.

theorem slice_setup_execution (resident : Program width 8)
    (nodes base entry done stream offset H old cursor count relative length : Nat)
    (state : State width 8)
    (physical : ∀ phase : Fin 16, resident[entry + phase.val]? =
      (typedSliceSetupCode width nodes base done stream offset)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 16 < 2 ^ width) (heapRoom : state.heap.size < 2 ^ width)
    (positive : 0 < count) (countFits : count < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (sourceRoom : H + relative + length < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (zeroHeld : state.reg 6 = word width 0) (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (directoryCell : state.heap[H + 9 + 2 * nodes + 2 * old + offset]? = some (word width relative))
    (countCell : state.heap[H + 9 + 4 * nodes + 2 * old + offset]? = some (word width length)) :
    ∃ final, Execution resident state final 16 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width stream ∧ final.halted = false ∧
      final.reg 2 = word width (H + relative) ∧ final.reg 3 = word width length ∧
      final.reg 0 = state.reg 0 ∧ final.reg 1 = state.reg 1 ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let activeSlot := Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base
  let directory := H + 9 + 2 * nodes + 2 * old + offset
  let arity := H + 9 + 4 * nodes + 2 * old + offset
  obtain ⟨directoryBound, directoryValue⟩ := Array.getElem?_eq_some_iff.mp directoryCell
  obtain ⟨arityBound, arityValue⟩ := Array.getElem?_eq_some_iff.mp countCell
  obtain ⟨activeBound, activeValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  have arityFits : arity < 2 ^ width := by dsimp only [arity]; omega
  have directoryFits : directory < 2 ^ width := by dsimp only [directory]; omega
  have activeFits : activeSlot < 2 ^ width := by dsimp only [activeSlot]; omega
  let s1 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (activeSlot)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (word width (old)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (H + 2 * old)) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (9 + 2 * nodes + offset)) (word width (H + 2 * old)) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (directory)) (word width (H + 2 * old)) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (relative)) (word width (H + 2 * old)) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (relative)) (word width (H + 2 * old)) (state.reg 4) (word width (activeSlot)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (relative)) (word width (H + 2 * old)) (state.reg 4) (word width (H)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + relative)) (word width (H + 2 * old)) (state.reg 4) (word width (H)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + relative)) (word width (H + 2 * old)) (state.reg 4) (word width (9 + 4 * nodes + offset)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + relative)) (word width (arity)) (state.reg 4) (word width (9 + 4 * nodes + offset)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 14) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + relative)) (word width (length)) (state.reg 4) (word width (9 + 4 * nodes + offset)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (entry + 15) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + relative)) (word width (length)) (state.reg 4) (word width (9 + 4 * nodes + offset)) (word width (0)) (word width (2 ^ width - 1))
      pc := word width (stream) }
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 0 (word width done)) position (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 0 done count running positive countFits countHeld
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial_directory state count cursor countHeld cursorHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords := rfl
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (activeSlot))) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (activeSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (activeSlot))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 2 2 (activeSlot) (word width (H)) running activeFits (by rfl) (by change state.heap[activeSlot]? = some (word width (H)); simpa only [directory, arity] using rawCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (activeSlot)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 5 1) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨3, by decide⟩)]
    have result := copy_load_step s3 5 1 (cursor) (word width (old)) running (by omega) (by rfl) (by change state.heap[cursor]? = some (word width (old)); simpa only [directory, arity] using queueCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (old))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords := rfl
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 5 5 5) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 5 5 5 (old) (old) running (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (old) + (old) = (2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (word width (old)) (word width (0)) (word width (2 ^ width - 1)) (word width (2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords := rfl
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 3 2 5) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 3 2 5 (H) (2 * old) running (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (H) + (2 * old) = (H + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords := rfl
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 2 (word width (9 + 2 * nodes + offset))) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 2 (word width (9 + 2 * nodes + offset)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H)) (word width (H + 2 * old)) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1)) (word width (9 + 2 * nodes + offset))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords := rfl
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 2 2 3 (9 + 2 * nodes + offset) (H + 2 * old) running (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (9 + 2 * nodes + offset) + (H + 2 * old) = (directory) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (9 + 2 * nodes + offset)) (word width (H + 2 * old)) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1)) (word width (directory))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords := rfl
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 2 2 (directory) (word width (relative)) running directoryFits (by rfl) (by change state.heap[directory]? = some (word width (relative)); simpa only [directory, arity] using directoryCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (directory)) (word width (H + 2 * old)) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1)) (word width (relative))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords := rfl
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.constant 5 (word width (activeSlot))) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨9, by decide⟩)]
    have result := copy_constant_step s9 5 (word width (activeSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (relative)) (word width (H + 2 * old)) (state.reg 4) (word width (2 * old)) (word width (0)) (word width (2 ^ width - 1)) (word width (activeSlot))) register
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords := rfl
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨10, by decide⟩)]
    have result := copy_load_step s10 5 5 (activeSlot) (word width (H)) running activeFits (by rfl) (by change state.heap[activeSlot]? = some (word width (H)); simpa only [directory, arity] using rawCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (relative)) (word width (H + 2 * old)) (state.reg 4) (word width (activeSlot)) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords := rfl
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨11, by decide⟩)]
    have result := copy_add_step s11 2 2 5 (relative) (H) running (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (relative) + (H) = (H + relative) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (relative)) (word width (H + 2 * old)) (state.reg 4) (word width (H)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + relative))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords := rfl
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.constant 5 (word width (9 + 4 * nodes + offset))) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨12, by decide⟩)]
    have result := copy_constant_step s12 5 (word width (9 + 4 * nodes + offset)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + relative)) (word width (H + 2 * old)) (state.reg 4) (word width (H)) (word width (0)) (word width (2 ^ width - 1)) (word width (9 + 4 * nodes + offset))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords := rfl
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.add 3 3 5) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨13, by decide⟩)]
    have result := copy_add_step s13 3 3 5 (H + 2 * old) (9 + 4 * nodes + offset) running (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by dsimp only [arity, directory] at arityFits directoryFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (H + 2 * old) + (9 + 4 * nodes + offset) = (arity) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + relative)) (word width (H + 2 * old)) (state.reg 4) (word width (9 + 4 * nodes + offset)) (word width (0)) (word width (2 ^ width - 1)) (word width (arity))) register
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords := rfl
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.load 3 3) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨14, by decide⟩)]
    have result := copy_load_step s14 3 3 (arity) (word width (length)) running arityFits (by rfl) (by change state.heap[arity]? = some (word width (length)); simpa only [directory, arity] using countCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + relative)) (word width (arity)) (state.reg 4) (word width (9 + 4 * nodes + offset)) (word width (0)) (word width (2 ^ width - 1)) (word width (length))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords := rfl
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.branchZero 6 (word width stream)) (by rfl) (by omega)
      (by simpa [typedSliceSetupCode, activeSlot] using physical ⟨15, by decide⟩)]
    have result := copy_branch_zero s15 6 stream running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live16 : s16.liveWords = state.liveWords := rfl
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.refl s16))))))))))))))))
  refine ⟨s16, ?_, rfl, rfl, rfl, rfl, running, rfl, rfl, countHeld.symm,
    cursorHeld.symm, rfl, zeroHeld.symm, maskHeld.symm⟩
  simpa only [Nat.reduceAdd, live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, max_self] using trace

theorem typed_rows_backedge_execution (resident : Program width 8)
    (entry next count cursor : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 4, resident[entry + phase.val]? =
      (typedRowsBackedgeCode width next)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 4 < 2 ^ width) (positive : 0 < count)
    (countFits : count < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countHeld : state.reg 0 = word width count)
    (cursorHeld : state.reg 1 = word width cursor)
    (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final, Execution resident state final 4 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width next ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 5 →
        final.reg register = state.reg register) := by
  let s1 := state.advance.put 5 (word width 1)
  let s2 := s1.advance.put 1 (word width (cursor + 1))
  let s3 := s2.advance.put 0 (word width (count - 1))
  let final : State width 8 := { s3.advance with pc := word width next }
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state entry (.constant 5 (word width 1)) position (by omega)
      (by simpa [typedRowsBackedgeCode] using physical ⟨0, by decide⟩)]
    exact copy_constant_step state 5 _ running
  have pc1 : s1.pc = word width (entry + 1) := referenceAdvancePC state entry position (by omega)
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.add 1 1 5) pc1 (by omega)
      (by simpa [typedRowsBackedgeCode] using physical ⟨1, by decide⟩)]
    exact copy_add_step s1 1 1 5 cursor 1 running (by omega) (by omega)
      (by simpa [s1, State.advance, State.put] using cursorHeld) (by rfl)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = word width (entry + 2)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.add 0 0 7) pc2 (by omega)
      (by simpa [typedRowsBackedgeCode] using physical ⟨2, by decide⟩)]
    have result := copy_add_step s2 0 0 7 count (2 ^ width - 1) running countFits
      (by have := Nat.two_pow_pos width; omega)
      (by simpa [s2, s1, State.advance, State.put] using countHeld)
      (by simpa [s2, s1, State.advance, State.put] using maskHeld)
    rw [marker_word_decrement count positive countFits] at result
    exact result
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = word width (entry + 3)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have t3 : programStep resident s3 = some final := by
    rw [fetched resident s3 (entry + 3) (.branchZero 6 (word width next)) pc3 (by omega)
      (by simpa [typedRowsBackedgeCode] using physical ⟨3, by decide⟩)]
    exact copy_branch_zero s3 6 next running
      (by simpa [s3, s2, s1, State.advance, State.put] using zeroHeld)
  have live1 : s1.liveWords = state.liveWords := rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have liveFinal : final.liveWords = state.liveWords := rfl
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.refl final))))
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, rfl, rfl, ?_⟩
  · simpa only [Nat.reduceAdd, live1, live2, live3, liveFinal, max_self] using trace
  · intro register notCount notCursor notTemp
    simp only [final, s3, s2, s1, State.advance, State.put,
      ite_eq_right notCount, ite_eq_right notCursor, ite_eq_right notTemp]

theorem child_row_execution (resident : Program width 8)
    (nodes base entry done rankBase H old relative count cursor : Nat)
    (occurrences : List (MappedOccurrence width)) (state : State width 8)
    (setupPhysical : ∀ phase : Fin 16, resident[entry + phase.val]? =
      (typedSliceSetupCode width nodes base done (entry + 16) 0)[phase.val]?)
    (streamPhysical : ∀ phase : Fin 9, resident[entry + 16 + phase.val]? =
      (mappedOccurrenceCopyCode width (entry + 16) (entry + 25))[phase.val]?)
    (backPhysical : ∀ phase : Fin 4, resident[entry + 25 + phase.val]? =
      (typedRowsBackedgeCode width entry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 29 < 2 ^ width)
    (positive : 0 < count) (countFits : count < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width)
    (room : state.heap.size + occurrences.length < 2 ^ width)
    (sourceFits : H + relative + occurrences.length < 2 ^ width)
    (lengthFits : occurrences.length < 2 ^ width)
    (countHeld : state.reg 0 = word width count)
    (cursorHeld : state.reg 1 = word width cursor)
    (rankHeld : state.reg 4 = word width rankBase)
    (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (directoryCell : state.heap[H + 9 + 2 * nodes + 2 * old]? = some (word width relative))
    (arityCell : state.heap[H + 9 + 4 * nodes + 2 * old]? = some (word width occurrences.length))
    (stored : MappedStreamStored state.heap (H + relative) rankBase occurrences) :
    ∃ final peak, Execution resident state final (21 + 9 * occurrences.length) peak ∧
      peak ≤ state.liveWords + occurrences.length ∧
      final.heap = state.heap ++ (occurrences.map MappedOccurrence.mapped).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  obtain ⟨selected, selection, selectedHeap, selectedStack, selectedOutput,
    selectedPC, selectedRunning, sourceHeld, lengthHeld, selectedCount,
    selectedCursor, selectedRank, selectedZero, selectedMask⟩ :=
    slice_setup_execution resident nodes base entry done (entry + 16) 0 H old cursor count
      relative occurrences.length state setupPhysical position running (by omega) (by omega)
      positive countFits cursorFits sourceFits countHeld cursorHeld zeroHeld maskHeld
      rawCell queueCell (by simpa only [Nat.add_zero] using directoryCell)
      (by simpa only [Nat.add_zero] using arityCell)
  have selectedLive : selected.liveWords = state.liveWords := by
    simp only [State.liveWords, selectedHeap, selectedStack, selectedOutput]
  obtain ⟨copied, copyPeak, copying, copySpace, copyHeap, copyStack, copyOutput,
    copyPC, copyRunning, copyCursor, copyCount, copyRegistersHeld⟩ :=
    mapped_stream_execution resident (entry + 16) (entry + 25) rankBase streamPhysical
      (by omega) occurrences (H + relative) selected selectedPC selectedRunning
      (by rw [selectedHeap]; exact room) sourceFits lengthFits sourceHeld lengthHeld
      (selectedRank.trans rankHeld) (selectedZero.trans zeroHeld) (selectedMask.trans maskHeld)
      (by rw [selectedHeap]; exact stored)
  have copiedLive : copied.liveWords = state.liveWords + occurrences.length := by
    simp only [State.liveWords, copyHeap, copyStack, copyOutput, Array.size_append,
      List.size_toArray, List.length_map, selectedHeap, selectedStack, selectedOutput]
    omega
  have copiedCount : copied.reg 0 = word width count :=
    (copyRegistersHeld 0 (by decide) (by decide) (by decide)).trans (selectedCount.trans countHeld)
  have copiedCursor : copied.reg 1 = word width cursor :=
    (copyRegistersHeld 1 (by decide) (by decide) (by decide)).trans (selectedCursor.trans cursorHeld)
  have copiedZero : copied.reg 6 = word width 0 :=
    (copyRegistersHeld 6 (by decide) (by decide) (by decide)).trans (selectedZero.trans zeroHeld)
  have copiedMask : copied.reg 7 = word width (2 ^ width - 1) :=
    (copyRegistersHeld 7 (by decide) (by decide) (by decide)).trans (selectedMask.trans maskHeld)
  obtain ⟨final, returning, finalHeap, finalStack, finalOutput, finalPC,
    finalRunning, finalCount, finalCursor, finalRegisters⟩ :=
    typed_rows_backedge_execution resident (entry + 25) entry count cursor copied backPhysical
      copyPC copyRunning (by omega) positive countFits cursorFits copiedCount copiedCursor
      copiedZero copiedMask
  refine ⟨final, max (max state.liveWords copyPeak) copied.liveWords, ?_, ?_, ?_,
    finalStack.trans (copyStack.trans selectedStack),
    finalOutput.trans (copyOutput.trans selectedOutput), finalPC, finalRunning,
    finalCount, finalCursor, ?_, ?_, ?_⟩
  · have trace := (selection.append copying).append returning
    convert trace using 1 <;> omega
  · rw [max_le_iff, max_le_iff]
    constructor
    · constructor
      · omega
      · rw [selectedLive] at copySpace
        exact copySpace
    · rw [copiedLive]
  · rw [finalHeap, copyHeap, selectedHeap]
  · exact (finalRegisters 4 (by decide) (by decide) (by decide)).trans
      ((copyRegistersHeld 4 (by decide) (by decide) (by decide)).trans selectedRank)
  · exact (finalRegisters 6 (by decide) (by decide) (by decide)).trans
      ((copyRegistersHeld 6 (by decide) (by decide) (by decide)).trans selectedZero)
  · exact (finalRegisters 7 (by decide) (by decide) (by decide)).trans
      ((copyRegistersHeld 7 (by decide) (by decide) (by decide)).trans selectedMask)

structure ChildSourceRow (width : Nat) where
  old : Nat
  relative : Nat
  occurrences : List (MappedOccurrence width)

def copiedChildWords : List (ChildSourceRow width) → List (Word width)
  | [] => []
  | row :: rest => row.occurrences.map MappedOccurrence.mapped ++ copiedChildWords rest

def childOccurrenceCount : List (ChildSourceRow width) → Nat
  | [] => 0
  | row :: rest => row.occurrences.length + childOccurrenceCount rest

theorem copied_child_words_length (rows : List (ChildSourceRow width)) :
    (copiedChildWords rows).length = childOccurrenceCount rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [copiedChildWords, childOccurrenceCount, List.length_append,
      List.length_map, ih]

def ChildRowsStored (heap : Array (Word width)) (nodes H cursor rankBase : Nat)
    (rows : List (ChildSourceRow width)) : Prop :=
  ∀ index : Fin rows.length,
    let row := rows[index.val]
    heap[cursor + index.val]? = some (word width row.old) ∧
    heap[H + 9 + 2 * nodes + 2 * row.old]? = some (word width row.relative) ∧
    heap[H + 9 + 4 * nodes + 2 * row.old]? = some (word width row.occurrences.length) ∧
    MappedStreamStored heap (H + row.relative) rankBase row.occurrences

/-- Complete original-Q child copying charges every original stored occurrence.
Ranked outputs retain each occurrence's position and multiplicity. -/
theorem child_rows_execution (resident : Program width 8)
    (nodes base entry done rankBase H : Nat)
    (setupPhysical : ∀ phase : Fin 16, resident[entry + phase.val]? =
      (typedSliceSetupCode width nodes base done (entry + 16) 0)[phase.val]?)
    (streamPhysical : ∀ phase : Fin 9, resident[entry + 16 + phase.val]? =
      (mappedOccurrenceCopyCode width (entry + 16) (entry + 25))[phase.val]?)
    (backPhysical : ∀ phase : Fin 4, resident[entry + 25 + phase.val]? =
      (typedRowsBackedgeCode width entry)[phase.val]?)
    (codeFits : entry + 29 < 2 ^ width) :
    ∀ (rows : List (ChildSourceRow width)) (cursor : Nat) (state : State width 8),
      state.pc = word width entry → state.halted = false →
      state.heap.size + childOccurrenceCount rows < 2 ^ width →
      cursor + rows.length < 2 ^ width → rows.length < 2 ^ width →
      (∀ row ∈ rows, H + row.relative + row.occurrences.length < 2 ^ width) →
      state.reg 0 = word width rows.length → state.reg 1 = word width cursor →
      state.reg 4 = word width rankBase → state.reg 6 = word width 0 →
      state.reg 7 = word width (2 ^ width - 1) →
      state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H) →
      ChildRowsStored state.heap nodes H cursor rankBase rows →
      ∃ final peak, Execution resident state final
          (21 * rows.length + 9 * childOccurrenceCount rows + 1) peak ∧
        peak ≤ state.liveWords + childOccurrenceCount rows ∧
        final.heap = state.heap ++ (copiedChildWords rows).toArray ∧
        final.stack = state.stack ∧ final.output = state.output ∧
        final.pc = word width done ∧ final.halted = false ∧
        final.reg 0 = word width 0 ∧ final.reg 1 = word width (cursor + rows.length) ∧
        final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  intro rows
  induction rows with
  | nil =>
    intro cursor state position running room cursorFits countFits sourceFits countHeld
      cursorHeld rankHeld zeroHeld maskHeld rawCell stored
    let final : State width 8 := { state.advance with pc := word width done }
    have transition : programStep resident state = some final := by
      rw [fetched resident state entry (.branchZero 0 (word width done)) position (by omega)
        (by simpa [typedSliceSetupCode] using setupPhysical ⟨0, by decide⟩)]
      exact copy_branch_zero state 0 done running countHeld
    have trace := Execution.cons transition (Execution.refl final)
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, max state.liveWords final.liveWords, ?_, ?_, ?_, rfl, rfl,
      rfl, running, countHeld, ?_, rfl, rfl, rfl⟩
    · simpa only [List.length_nil, childOccurrenceCount, Nat.mul_zero, Nat.zero_add] using trace
    · simp only [childOccurrenceCount, Nat.add_zero, live, max_self, Nat.le_refl]
    · change state.heap = state.heap ++ (copiedChildWords []).toArray
      rw [copiedChildWords, copy_nil_array, Array.append_empty]
    · change state.reg 1 = word width (cursor + ([] : List (ChildSourceRow width)).length)
      simpa only [List.length_nil, Nat.add_zero] using cursorHeld
  | cons row rest ih =>
    intro cursor state position running room cursorFits countFits sourceFits countHeld
      cursorHeld rankHeld zeroHeld maskHeld rawCell stored
    obtain ⟨queueFirst, directoryFirst, arityFirst, streamFirst⟩ := stored ⟨0, by simp⟩
    simp only [List.getElem_cons_zero, Nat.add_zero] at queueFirst directoryFirst arityFirst streamFirst
    obtain ⟨middle, firstPeak, firstTrace, firstSpace, middleHeap, middleStack,
      middleOutput, middlePC, middleRunning, middleCount, middleCursor,
      middleRank, middleZero, middleMask⟩ :=
      child_row_execution resident nodes base entry done rankBase H row.old row.relative
        (row :: rest).length cursor row.occurrences state setupPhysical streamPhysical backPhysical
        position running codeFits (by simp) countFits
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [childOccurrenceCount] at room; omega)
        (sourceFits row (by simp))
        (by simp only [childOccurrenceCount] at room; omega)
        countHeld cursorHeld rankHeld zeroHeld maskHeld rawCell queueFirst directoryFirst arityFirst streamFirst
    have middleSize : middle.heap.size = state.heap.size + row.occurrences.length := by
      simp only [middleHeap, Array.size_append, List.size_toArray, List.length_map]
    have middleLive : middle.liveWords = state.liveWords + row.occurrences.length := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]
      omega
    have preserve : ∀ (address : Nat) (value : Word width), state.heap[address]? = some value →
        middle.heap[address]? = some value := by
      intro address value cell
      obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
      rw [middleHeap, Array.getElem?_append_left valid]
      exact cell
    have restStored : ChildRowsStored middle.heap nodes H (cursor + 1) rankBase rest := by
      intro index
      obtain ⟨q, d, a, original⟩ := stored ⟨index.val + 1, by simp only [List.length_cons]; omega⟩
      simp only [List.getElem_cons_succ] at q d a original
      refine ⟨?_, preserve _ _ d, preserve _ _ a, ?_⟩
      · simpa only [Nat.add_assoc, Nat.add_comm 1 index.val] using preserve _ _ q
      · intro occurrence
        obtain ⟨source, rank, fits⟩ := original occurrence
        exact ⟨preserve _ _ source, preserve _ _ rank, fits⟩
    obtain ⟨final, restPeak, restTrace, restSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalCount, finalCursor, finalRank, finalZero, finalMask⟩ :=
      ih (cursor + 1) middle middlePC middleRunning
        (by simp only [childOccurrenceCount] at room; rw [middleSize]; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at countFits; omega)
        (fun selected member => sourceFits selected (List.mem_cons_of_mem row member))
        (by simpa only [List.length_cons, Nat.add_sub_cancel] using middleCount)
        middleCursor (middleRank.trans rankHeld) (middleZero.trans zeroHeld)
        (middleMask.trans maskHeld) (preserve _ _ rawCell) restStored
    refine ⟨final, max firstPeak restPeak, ?_, ?_, ?_, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalCount, ?_,
      finalRank.trans middleRank, finalZero.trans middleZero, finalMask.trans middleMask⟩
    · have trace := firstTrace.append restTrace
      convert trace using 1 <;> simp only [List.length_cons, childOccurrenceCount] <;> omega
    · rw [max_le_iff]
      constructor <;> simp only [childOccurrenceCount] <;> omega
    · rw [finalHeap, middleHeap]
      have conversion : (copiedChildWords (row :: rest)).toArray =
          (row.occurrences.map MappedOccurrence.mapped).toArray ++ (copiedChildWords rest).toArray := by
        change ((row.occurrences.map MappedOccurrence.mapped) ++ copiedChildWords rest).toArray = _
        exact (List.append_toArray _ _).symm
      rw [conversion]
      exact Array.append_assoc
    · simp only [List.length_cons] at ⊢
      simpa only [Nat.add_assoc, Nat.add_comm 1 rest.length] using finalCursor


theorem guard_row_execution (resident : Program width 8)
    (nodes base entry done rankBase H old relative count cursor : Nat)
    (values : List (Word width)) (state : State width 8)
    (setupPhysical : ∀ phase : Fin 16, resident[entry + phase.val]? =
      (typedSliceSetupCode width nodes base done (entry + 16) 1)[phase.val]?)
    (streamPhysical : ∀ phase : Fin 7, resident[entry + 16 + phase.val]? =
      (unchangedOccurrenceCopyCode width (entry + 16) (entry + 23))[phase.val]?)
    (backPhysical : ∀ phase : Fin 4, resident[entry + 23 + phase.val]? =
      (typedRowsBackedgeCode width entry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 27 < 2 ^ width)
    (positive : 0 < count) (countFits : count < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width)
    (room : state.heap.size + values.length < 2 ^ width)
    (sourceFits : H + relative + values.length < 2 ^ width)
    (lengthFits : values.length < 2 ^ width)
    (countHeld : state.reg 0 = word width count)
    (cursorHeld : state.reg 1 = word width cursor)
    (rankHeld : state.reg 4 = word width rankBase)
    (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (directoryCell : state.heap[H + 9 + 2 * nodes + 2 * old + 1]? = some (word width relative))
    (arityCell : state.heap[H + 9 + 4 * nodes + 2 * old + 1]? = some (word width values.length))
    (stored : UnchangedStreamStored state.heap (H + relative) values) :
    ∃ final peak, Execution resident state final (21 + 7 * values.length) peak ∧
      peak ≤ state.liveWords + values.length ∧
      final.heap = state.heap ++ values.toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  obtain ⟨selected, selection, selectedHeap, selectedStack, selectedOutput,
    selectedPC, selectedRunning, sourceHeld, lengthHeld, selectedCount,
    selectedCursor, selectedRank, selectedZero, selectedMask⟩ :=
    slice_setup_execution resident nodes base entry done (entry + 16) 1 H old cursor count
      relative values.length state setupPhysical position running (by omega) (by omega)
      positive countFits cursorFits sourceFits countHeld cursorHeld zeroHeld maskHeld
      rawCell queueCell (by simpa only [Nat.add_zero] using directoryCell)
      (by simpa only [Nat.add_zero] using arityCell)
  have selectedLive : selected.liveWords = state.liveWords := by
    simp only [State.liveWords, selectedHeap, selectedStack, selectedOutput]
  obtain ⟨copied, copyPeak, copying, copySpace, copyHeap, copyStack, copyOutput,
    copyPC, copyRunning, copyCursor, copyCount, copyRegistersHeld⟩ :=
    unchanged_stream_execution resident (entry + 16) (entry + 23) streamPhysical
      (by omega) values (H + relative) selected selectedPC selectedRunning
      (by rw [selectedHeap]; exact room) sourceFits lengthFits sourceHeld lengthHeld
      (selectedZero.trans zeroHeld) (selectedMask.trans maskHeld)
      (by rw [selectedHeap]; exact stored)
  have copiedLive : copied.liveWords = state.liveWords + values.length := by
    simp only [State.liveWords, copyHeap, copyStack, copyOutput, Array.size_append,
      List.size_toArray, selectedHeap, selectedStack, selectedOutput]
    omega
  have copiedCount : copied.reg 0 = word width count :=
    (copyRegistersHeld 0 (by decide) (by decide) (by decide)).trans (selectedCount.trans countHeld)
  have copiedCursor : copied.reg 1 = word width cursor :=
    (copyRegistersHeld 1 (by decide) (by decide) (by decide)).trans (selectedCursor.trans cursorHeld)
  have copiedZero : copied.reg 6 = word width 0 :=
    (copyRegistersHeld 6 (by decide) (by decide) (by decide)).trans (selectedZero.trans zeroHeld)
  have copiedMask : copied.reg 7 = word width (2 ^ width - 1) :=
    (copyRegistersHeld 7 (by decide) (by decide) (by decide)).trans (selectedMask.trans maskHeld)
  obtain ⟨final, returning, finalHeap, finalStack, finalOutput, finalPC,
    finalRunning, finalCount, finalCursor, finalRegisters⟩ :=
    typed_rows_backedge_execution resident (entry + 23) entry count cursor copied backPhysical
      copyPC copyRunning (by omega) positive countFits cursorFits copiedCount copiedCursor
      copiedZero copiedMask
  refine ⟨final, max (max state.liveWords copyPeak) copied.liveWords, ?_, ?_, ?_,
    finalStack.trans (copyStack.trans selectedStack),
    finalOutput.trans (copyOutput.trans selectedOutput), finalPC, finalRunning,
    finalCount, finalCursor, ?_, ?_, ?_⟩
  · have trace := (selection.append copying).append returning
    convert trace using 1 <;> omega
  · rw [max_le_iff, max_le_iff]
    constructor
    · constructor
      · omega
      · rw [selectedLive] at copySpace
        exact copySpace
    · rw [copiedLive]
  · rw [finalHeap, copyHeap, selectedHeap]
  · exact (finalRegisters 4 (by decide) (by decide) (by decide)).trans
      ((copyRegistersHeld 4 (by decide) (by decide) (by decide)).trans selectedRank)
  · exact (finalRegisters 6 (by decide) (by decide) (by decide)).trans
      ((copyRegistersHeld 6 (by decide) (by decide) (by decide)).trans selectedZero)
  · exact (finalRegisters 7 (by decide) (by decide) (by decide)).trans
      ((copyRegistersHeld 7 (by decide) (by decide) (by decide)).trans selectedMask)


structure GuardSourceRow (width : Nat) where
  old : Nat
  relative : Nat
  values : List (Word width)

def copiedGuardWords : List (GuardSourceRow width) → List (Word width)
  | [] => []
  | row :: rest => row.values ++ copiedGuardWords rest

def guardOccurrenceCount : List (GuardSourceRow width) → Nat
  | [] => 0
  | row :: rest => row.values.length + guardOccurrenceCount rest

theorem copied_guard_words_length (rows : List (GuardSourceRow width)) :
    (copiedGuardWords rows).length = guardOccurrenceCount rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [copiedGuardWords, guardOccurrenceCount, List.length_append,
      ih]

def GuardRowsStored (heap : Array (Word width)) (nodes H cursor rankBase : Nat)
    (rows : List (GuardSourceRow width)) : Prop :=
  ∀ index : Fin rows.length,
    let row := rows[index.val]
    heap[cursor + index.val]? = some (word width row.old) ∧
    heap[H + 9 + 2 * nodes + 2 * row.old + 1]? = some (word width row.relative) ∧
    heap[H + 9 + 4 * nodes + 2 * row.old + 1]? = some (word width row.values.length) ∧
    UnchangedStreamStored heap (H + row.relative) row.values

/-- Complete original-Q guard copying retains every original channel word,
including repeated occurrences in their listed positions. -/
theorem guard_rows_execution (resident : Program width 8)
    (nodes base entry done rankBase H : Nat)
    (setupPhysical : ∀ phase : Fin 16, resident[entry + phase.val]? =
      (typedSliceSetupCode width nodes base done (entry + 16) 1)[phase.val]?)
    (streamPhysical : ∀ phase : Fin 7, resident[entry + 16 + phase.val]? =
      (unchangedOccurrenceCopyCode width (entry + 16) (entry + 23))[phase.val]?)
    (backPhysical : ∀ phase : Fin 4, resident[entry + 23 + phase.val]? =
      (typedRowsBackedgeCode width entry)[phase.val]?)
    (codeFits : entry + 27 < 2 ^ width) :
    ∀ (rows : List (GuardSourceRow width)) (cursor : Nat) (state : State width 8),
      state.pc = word width entry → state.halted = false →
      state.heap.size + guardOccurrenceCount rows < 2 ^ width →
      cursor + rows.length < 2 ^ width → rows.length < 2 ^ width →
      (∀ row ∈ rows, H + row.relative + row.values.length < 2 ^ width) →
      state.reg 0 = word width rows.length → state.reg 1 = word width cursor →
      state.reg 4 = word width rankBase → state.reg 6 = word width 0 →
      state.reg 7 = word width (2 ^ width - 1) →
      state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H) →
      GuardRowsStored state.heap nodes H cursor rankBase rows →
      ∃ final peak, Execution resident state final
          (21 * rows.length + 7 * guardOccurrenceCount rows + 1) peak ∧
        peak ≤ state.liveWords + guardOccurrenceCount rows ∧
        final.heap = state.heap ++ (copiedGuardWords rows).toArray ∧
        final.stack = state.stack ∧ final.output = state.output ∧
        final.pc = word width done ∧ final.halted = false ∧
        final.reg 0 = word width 0 ∧ final.reg 1 = word width (cursor + rows.length) ∧
        final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  intro rows
  induction rows with
  | nil =>
    intro cursor state position running room cursorFits countFits sourceFits countHeld
      cursorHeld rankHeld zeroHeld maskHeld rawCell stored
    let final : State width 8 := { state.advance with pc := word width done }
    have transition : programStep resident state = some final := by
      rw [fetched resident state entry (.branchZero 0 (word width done)) position (by omega)
        (by simpa [typedSliceSetupCode] using setupPhysical ⟨0, by decide⟩)]
      exact copy_branch_zero state 0 done running countHeld
    have trace := Execution.cons transition (Execution.refl final)
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, max state.liveWords final.liveWords, ?_, ?_, ?_, rfl, rfl,
      rfl, running, countHeld, ?_, rfl, rfl, rfl⟩
    · simpa only [List.length_nil, guardOccurrenceCount, Nat.mul_zero, Nat.zero_add] using trace
    · simp only [guardOccurrenceCount, Nat.add_zero, live, max_self, Nat.le_refl]
    · change state.heap = state.heap ++ (copiedGuardWords []).toArray
      rw [copiedGuardWords, copy_nil_array, Array.append_empty]
    · change state.reg 1 = word width (cursor + ([] : List (GuardSourceRow width)).length)
      simpa only [List.length_nil, Nat.add_zero] using cursorHeld
  | cons row rest ih =>
    intro cursor state position running room cursorFits countFits sourceFits countHeld
      cursorHeld rankHeld zeroHeld maskHeld rawCell stored
    obtain ⟨queueFirst, directoryFirst, arityFirst, streamFirst⟩ := stored ⟨0, by simp⟩
    simp only [List.getElem_cons_zero, Nat.add_zero] at queueFirst directoryFirst arityFirst streamFirst
    obtain ⟨middle, firstPeak, firstTrace, firstSpace, middleHeap, middleStack,
      middleOutput, middlePC, middleRunning, middleCount, middleCursor,
      middleRank, middleZero, middleMask⟩ :=
      guard_row_execution resident nodes base entry done rankBase H row.old row.relative
        (row :: rest).length cursor row.values state setupPhysical streamPhysical backPhysical
        position running codeFits (by simp) countFits
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [guardOccurrenceCount] at room; omega)
        (sourceFits row (by simp))
        (by simp only [guardOccurrenceCount] at room; omega)
        countHeld cursorHeld rankHeld zeroHeld maskHeld rawCell queueFirst directoryFirst arityFirst streamFirst
    have middleSize : middle.heap.size = state.heap.size + row.values.length := by
      simp only [middleHeap, Array.size_append, List.size_toArray]
    have middleLive : middle.liveWords = state.liveWords + row.values.length := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]
      omega
    have preserve : ∀ (address : Nat) (value : Word width), state.heap[address]? = some value →
        middle.heap[address]? = some value := by
      intro address value cell
      obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
      rw [middleHeap, Array.getElem?_append_left valid]
      exact cell
    have restStored : GuardRowsStored middle.heap nodes H (cursor + 1) rankBase rest := by
      intro index
      obtain ⟨q, d, a, original⟩ := stored ⟨index.val + 1, by simp only [List.length_cons]; omega⟩
      simp only [List.getElem_cons_succ] at q d a original
      refine ⟨?_, preserve _ _ d, preserve _ _ a, ?_⟩
      · simpa only [Nat.add_assoc, Nat.add_comm 1 index.val] using preserve _ _ q
      · intro occurrence
        exact preserve _ _ (original occurrence)
    obtain ⟨final, restPeak, restTrace, restSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalCount, finalCursor, finalRank, finalZero, finalMask⟩ :=
      ih (cursor + 1) middle middlePC middleRunning
        (by simp only [guardOccurrenceCount] at room; rw [middleSize]; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at countFits; omega)
        (fun selected member => sourceFits selected (List.mem_cons_of_mem row member))
        (by simpa only [List.length_cons, Nat.add_sub_cancel] using middleCount)
        middleCursor (middleRank.trans rankHeld) (middleZero.trans zeroHeld)
        (middleMask.trans maskHeld) (preserve _ _ rawCell) restStored
    refine ⟨final, max firstPeak restPeak, ?_, ?_, ?_, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalCount, ?_,
      finalRank.trans middleRank, finalZero.trans middleZero, finalMask.trans middleMask⟩
    · have trace := firstTrace.append restTrace
      convert trace using 1 <;> simp only [List.length_cons, guardOccurrenceCount] <;> omega
    · rw [max_le_iff]
      constructor <;> simp only [guardOccurrenceCount] <;> omega
    · rw [finalHeap, middleHeap]
      have conversion : (copiedGuardWords (row :: rest)).toArray =
          (row.values).toArray ++ (copiedGuardWords rest).toArray := by
        change ((row.values) ++ copiedGuardWords rest).toArray = _
        exact (List.append_toArray _ _).symm
      rw [conversion]
      exact Array.append_assoc
    · simp only [List.length_cons] at ⊢
      simpa only [Nat.add_assoc, Nat.add_comm 1 rest.length] using finalCursor

/-- Root cursor and count are loaded from the retained original raw header.
The allocation-dependent raw origin is read from the actual saved slot. -/
def typedRootSetupCode (width nodes base rootEntry : Nat) : Program width 8 :=
  #[.constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)),
    .load 2 2, .copy 3 2,
    .constant 5 (word width 7), .add 5 2 5, .load 5 5, .add 2 2 5,
    .constant 5 (word width 2), .add 3 3 5, .load 3 3,
    .branchZero 6 (word width rootEntry)]

theorem copy_copy_step (state : State width 8) (dst src : Fin 8)
    (value : Word width) (running : state.halted = false) (held : state.reg src = value) :
    step (.copy dst src) state = some (state.advance.put dst value) := by
  simp only [step, running, Bool.false_eq_true, ite_false, held]

theorem copyRegisters_initial_zero (state : State width 8)
    (held : state.reg 6 = word width 0) :
    state.reg = copyRegisters (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3)
      (state.reg 4) (state.reg 5) (word width 0) (state.reg 7) := by
  funext register
  fin_cases register <;> simp [copyRegisters, held]

theorem root_setup_execution (resident : Program width 8)
    (nodes base entry rootEntry H relative count : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 11, resident[entry + phase.val]? =
      (typedRootSetupCode width nodes base rootEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 11 < 2 ^ width) (heapRoom : state.heap.size < 2 ^ width)
    (sourceFits : H + relative + count < 2 ^ width)
    (zeroHeld : state.reg 6 = word width 0)
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (offsetCell : state.heap[H + 7]? = some (word width relative))
    (countCell : state.heap[H + 2]? = some (word width count)) :
    ∃ final, Execution resident state final 11 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width rootEntry ∧ final.halted = false ∧
      final.reg 2 = word width (H + relative) ∧ final.reg 3 = word width count ∧
      final.reg 0 = state.reg 0 ∧ final.reg 1 = state.reg 1 ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let activeSlot := Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base
  obtain ⟨activeBound, activeValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  obtain ⟨offsetBound, offsetValue⟩ := Array.getElem?_eq_some_iff.mp offsetCell
  obtain ⟨countBound, countValue⟩ := Array.getElem?_eq_some_iff.mp countCell
  have activeFits : activeSlot < 2 ^ width := by dsimp only [activeSlot]; omega
  let s1 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (activeSlot)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (state.reg 7), pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (state.reg 7), pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (H)) (state.reg 4) (state.reg 5) (word width 0) (state.reg 7), pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (H)) (state.reg 4) (word width (7)) (word width 0) (state.reg 7), pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (H)) (state.reg 4) (word width (H + 7)) (word width 0) (state.reg 7), pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (H)) (state.reg 4) (word width (relative)) (word width 0) (state.reg 7), pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H + relative)) (word width (H)) (state.reg 4) (word width (relative)) (word width 0) (state.reg 7), pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H + relative)) (word width (H)) (state.reg 4) (word width (2)) (word width 0) (state.reg 7), pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H + relative)) (word width (H + 2)) (state.reg 4) (word width (2)) (word width 0) (state.reg 7), pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H + relative)) (word width (count)) (state.reg 4) (word width (2)) (word width 0) (state.reg 7), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H + relative)) (word width (count)) (state.reg 4) (word width (2)) (word width 0) (state.reg 7), pc := word width (rootEntry) }
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 2 (word width (activeSlot))) position (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨0, by decide⟩)]
    have result := copy_constant_step state 2 (word width (activeSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      change (if register = 2 then word width activeSlot else state.reg register) = _
      rw [copyRegisters_initial_zero state zeroHeld]
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (state.reg 7) (word width (activeSlot))) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords := rfl
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨1, by decide⟩)]
    have result := copy_load_step s1 2 2 (activeSlot) (word width (H)) running activeFits (by rfl) (by change state.heap[activeSlot]? = _; exact rawCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (word width (activeSlot)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (state.reg 7) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.copy 3 2) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨2, by decide⟩)]
    have result := copy_copy_step s2 3 2 (word width (H)) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (H)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (state.reg 7) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.constant 5 (word width (7))) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨3, by decide⟩)]
    have result := copy_constant_step s3 5 (word width (7)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (H)) (state.reg 4) (state.reg 5) (word width 0) (state.reg 7) (word width (7))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords := rfl
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 5 2 5) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 5 2 5 (H) (7) running (by omega) (by omega) (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (H)) (state.reg 4) (word width (7)) (word width 0) (state.reg 7) (word width (H + 7))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords := rfl
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨5, by decide⟩)]
    have result := copy_load_step s5 5 5 (H + 7) (word width (relative)) running (by omega) (by rfl) (by change state.heap[H + 7]? = _; exact offsetCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (H)) (state.reg 4) (word width (H + 7)) (word width 0) (state.reg 7) (word width (relative))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords := rfl
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨6, by decide⟩)]
    have result := copy_add_step s6 2 2 5 (H) (relative) running (by omega) (by omega) (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (word width (H)) (word width (H)) (state.reg 4) (word width (relative)) (word width 0) (state.reg 7) (word width (H + relative))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords := rfl
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.constant 5 (word width (2))) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨7, by decide⟩)]
    have result := copy_constant_step s7 5 (word width (2)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H + relative)) (word width (H)) (state.reg 4) (word width (relative)) (word width 0) (state.reg 7) (word width (2))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords := rfl
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.add 3 3 5) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨8, by decide⟩)]
    have result := copy_add_step s8 3 3 5 (H) (2) running (by omega) (by omega) (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (H + relative)) (word width (H)) (state.reg 4) (word width (2)) (word width 0) (state.reg 7) (word width (H + 2))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords := rfl
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.load 3 3) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨9, by decide⟩)]
    have result := copy_load_step s9 3 3 (H + 2) (word width (count)) running (by omega) (by rfl) (by change state.heap[H + 2]? = _; exact countCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (H + relative)) (word width (H + 2)) (state.reg 4) (word width (2)) (word width 0) (state.reg 7) (word width (count))) register
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords := rfl
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.branchZero 6 (word width rootEntry)) (by rfl) (by omega)
      (by simpa [typedRootSetupCode, activeSlot] using physical ⟨10, by decide⟩)]
    have result := copy_branch_zero s10 6 rootEntry running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live11 : s11.liveWords = state.liveWords := rfl
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.refl s11)))))))))))
  refine ⟨s11, ?_, rfl, rfl, rfl, rfl, running, rfl, rfl, rfl, rfl, rfl, zeroHeld.symm, rfl⟩
  simpa only [Nat.reduceAdd, live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, max_self] using trace

open Controller.Decoder Controller.Cost.ForestIndexedOperands

/-- Constructor-preserving original source rows. All Nat reference lists retain
positions and repeated occurrences; validation precedes their word encoding. -/
def originalRow : RawGate → Row
  | .zero => ⟨0, 0, [], []⟩
  | .input channel => ⟨1, channel, [], []⟩
  | .disj children => ⟨2, 0, children, []⟩
  | .guard child labels => ⟨3, child, [child], labels⟩
  | .liveAnd left right => ⟨4, left, [left, right], []⟩

def originalRows (raw : RawDAG) : List Row := raw.nodes.toList.map originalRow

theorem original_row_matches (gate : RawGate) (valid : gate.WellFormed channels nodes) :
    (originalRow gate).Matches (gate.toGate valid) := by
  cases gate <;> simp [originalRow, Row.Matches, RawGate.toGate, Gate.children,
    Gate.guardLabels, List.map_map, Function.comp_def]

theorem original_row_head (gate : RawGate) (valid : gate.WellFormed channels nodes) :
    (originalRow gate).head = UniformDAGSource.typedHead (gate.toGate valid) := by
  cases gate <;> rfl

/-- The counted original header extends the five global counts by four derived
relative offsets. It supplies no externally cached directory metadata. -/
def originalHeader (channels : Nat) (raw : RawDAG) : List Nat :=
  let rows := originalRows raw
  let childStart := 9 + 6 * rows.length
  let guardStart := childStart + (rowChildren rows).length
  let rootStart := guardStart + (rowGuards rows).length
  [rows.length, channels, raw.roots.length, (rowChildren rows).length,
    (rowGuards rows).length, childStart, guardStart, rootStart, rootStart + raw.roots.length]

def originalHeaderHeap (width channels : Nat) (raw : RawDAG) : Array (Word width) :=
  ((originalHeader channels raw).map (word width)).toArray

/-- Exact original source image used by the physical loader. Reference-word
identity applies to validated Nat fields within the justified word capacity. -/
def originalPacket (width channels : Nat) (raw : RawDAG) : Array (Word width) :=
  cacheHeap width (originalHeaderHeap width channels raw) (originalRows raw) raw.roots

theorem original_rows_length (raw : RawDAG) :
    (originalRows raw).length = raw.nodes.size := by
  simp only [originalRows, List.length_map, Array.length_toList]

theorem original_header_size (channels : Nat) (raw : RawDAG) :
    (originalHeaderHeap width channels raw).size = 9 := by
  simp only [originalHeaderHeap, List.size_toArray, List.length_map, originalHeader,
    List.length_cons, List.length_nil]

theorem original_packet_size (channels : Nat) (raw : RawDAG) :
    (originalPacket width channels raw).size = 9 + 6 * raw.nodes.size +
      (rowChildren (originalRows raw)).length + (rowGuards (originalRows raw)).length + raw.roots.length := by
  rw [originalPacket, cacheHeap_size, original_header_size, original_rows_length]

theorem row_stream_cell (field : Row → List Nat) (rows : List Row)
    (index : Nat) (valid : index < rows.length) (position : Nat)
    (inside : position < (field rows[index]).length) :
    (rows.flatMap field)[((rows.take index).flatMap field).length + position]? =
      some ((field rows[index])[position]) := by
  induction rows generalizing index with
  | nil => simp at valid
  | cons row rest ih =>
    cases index with
    | zero =>
      simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
        List.getElem_cons_zero, List.flatMap_cons]
      have rowInside : position < (field row).length := by
        simpa only [List.getElem_cons_zero] using inside
      rw [List.getElem?_append_left rowInside, List.getElem?_eq_getElem rowInside]
    | succ index =>
      have next : index < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using valid
      have nextInside : position < (field rest[index]).length := by
        simpa only [List.getElem_cons_succ] using inside
      have tail := ih index next nextInside
      simp only [List.take_succ_cons, List.flatMap_cons, List.length_append,
        List.getElem_cons_succ]
      rw [Nat.add_assoc, List.getElem?_append_right (by omega :
        (field row).length ≤ (field row).length +
          (((rest.take index).flatMap field).length + position)), Nat.add_sub_cancel_left]
      exact tail

def OriginalImageStored (heap : Array (Word width)) (H channels : Nat) (raw : RawDAG) : Prop :=
  ∀ index : Fin (originalPacket width channels raw).size,
    heap[H + index.val]? = some (originalPacket width channels raw)[index.val]

theorem original_image_cell (heap : Array (Word width)) (H channels : Nat) (raw : RawDAG)
    (image : OriginalImageStored heap H channels raw) (index : Nat) (value : Word width)
    (cell : (originalPacket width channels raw)[index]? = some value) :
    heap[H + index]? = some value := by
  obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
  have saved := image ⟨index, valid⟩
  rw [actual] at saved
  exact saved

def originalRootStart (raw : RawDAG) : Nat :=
  9 + 6 * (originalRows raw).length + (rowChildren (originalRows raw)).length +
    (rowGuards (originalRows raw)).length

theorem original_root_header_cells (heap : Array (Word width)) (H channels : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap H channels raw) :
    heap[H + 7]? = some (word width (originalRootStart raw)) ∧
    heap[H + 2]? = some (word width raw.roots.length) := by
  constructor
  · apply original_image_cell heap H channels raw image
    rw [originalPacket, cacheHeap,
      ForestCursorMaterialize.allocatedHeap_prefix width _ _ 7
        (by rw [original_header_size]; decide)]
    simp [originalHeaderHeap, originalHeader, originalRootStart, Nat.add_assoc]
  · apply original_image_cell heap H channels raw image
    rw [originalPacket, cacheHeap,
      ForestCursorMaterialize.allocatedHeap_prefix width _ _ 2
        (by rw [original_header_size]; decide)]
    simp [originalHeaderHeap, originalHeader]

theorem original_root_cell (heap : Array (Word width)) (H channels : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap H channels raw)
    (index : Nat) (valid : index < raw.roots.length) :
    heap[H + (originalRootStart raw + index)]? = some (word width raw.roots[index]) := by
  have cell := cache_root_word (width := width) (originalHeaderHeap width channels raw)
    (originalRows raw) raw.roots index valid
  have bound : originalRootStart raw + index < (originalPacket width channels raw).size := by
    rw [originalPacket, cacheHeap_size, original_header_size]
    unfold originalRootStart
    omega
  have selected : (originalPacket width channels raw)[originalRootStart raw + index] =
      word width raw.roots[index] := by
    simpa only [originalPacket, original_header_size, originalRootStart, Nat.add_assoc] using cell
  exact original_image_cell heap H channels raw image _ _
    (by rw [Array.getElem?_eq_getElem bound, selected])

theorem produced_rank_cell (graph : UnorderedDAG channels)
    (numbering : graph.Numbering) (heap : Array (Word width)) (rankBase : Nat)
    (cells : ∀ index : Fin numbering.order.length,
      heap[rankBase + numbering.order[index.val].val]? = some (word width index.val))
    (old : Fin graph.nodeCount) :
    heap[rankBase + old.val]? = some (word width (numbering.newIndex old).val) := by
  have selected := cells (numbering.newIndex old)
  have original : numbering.order[(numbering.newIndex old).val] = old := by
    change numbering.oldIndex (numbering.newIndex old) = old
    exact numbering.oldIndex_newIndex old
  simpa only [original] using selected

def numberedRootOccurrences (graph : UnorderedDAG channels) (numbering : graph.Numbering) :
    List (MappedOccurrence width) :=
  graph.roots.map (fun old => ⟨old.val, word width (numbering.newIndex old).val⟩)

theorem original_numbered_roots_stored (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (heap : Array (Word width))
    (H rankBase : Nat) (image : OriginalImageStored heap H channels raw)
    (nodesFit : raw.nodes.size < 2 ^ width)
    (ranks : ∀ index : Fin numbering.order.length,
      heap[rankBase + numbering.order[index.val].val]? = some (word width index.val)) :
    MappedStreamStored heap (H + originalRootStart raw) rankBase
      (numberedRootOccurrences (raw.toUnordered valid) numbering) := by
  let graph := raw.toUnordered valid
  have rootLengths : graph.roots.length = raw.roots.length := by
    simp only [graph, RawDAG.toUnordered, List.length_map, List.length_attach]
  intro index
  have sourceBound : index.val < raw.roots.length := by
    have bound := index.isLt
    simp only [numberedRootOccurrences, List.length_map] at bound
    rw [rootLengths] at bound
    exact bound
  have graphBound : index.val < graph.roots.length := by rw [rootLengths]; exact sourceBound
  have rawRoot : raw.roots[index.val] = (graph.roots[index.val]).val := by
    have roots := RawDAG.toUnordered_roots raw valid
    have selected := congrArg (fun values : List Nat => values[index.val]?) roots
    simp only [List.getElem?_map] at selected
    change Option.map Fin.val graph.roots[index.val]? = raw.roots[index.val]? at selected
    rw [List.getElem?_eq_getElem graphBound,
      List.getElem?_eq_getElem sourceBound] at selected
    have same : some ((graph.roots[index.val]).val) = some raw.roots[index.val] := by
      simpa only [Option.map_some] using selected
    exact (Option.some.inj same).symm
  simp only [numberedRootOccurrences, List.getElem_map]
  change heap[(H + originalRootStart raw) + index.val]? =
      some (word width (graph.roots[index.val]).val) ∧
    heap[rankBase + (graph.roots[index.val]).val]? =
      some (word width (numbering.newIndex (graph.roots[index.val])).val) ∧
    (graph.roots[index.val]).val < 2 ^ width
  refine ⟨?_, produced_rank_cell graph numbering heap rankBase ranks (graph.roots[index.val]), ?_⟩
  · have source := original_root_cell heap H channels raw image index.val sourceBound
    rw [rawRoot] at source
    simpa only [Nat.add_assoc] using source
  · have bounded := (graph.roots[index.val]).isLt
    change (graph.roots[index.val]).val < raw.nodes.size at bounded
    omega

/-- The declared original roots are fetched in their original order and rank
remapped by the actual produced table. Duplicate root occurrences are emitted
as duplicate packet words. Header setup and every stream iteration are fetched. -/
theorem original_roots_execution (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (resident : Program width 8) (nodes base entry done H rankBase : Nat)
    (nodesEq : nodes = raw.nodes.size) (state : State width 8)
    (setupAt : ∀ phase : Fin 11, resident[entry + phase.val]? =
      (typedRootSetupCode width nodes base (entry + 11))[phase.val]?)
    (streamAt : ∀ phase : Fin 9, resident[entry + 11 + phase.val]? =
      (mappedOccurrenceCopyCode width (entry + 11) done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 20 < 2 ^ width)
    (room : state.heap.size + raw.roots.length < 2 ^ width)
    (sourceFits : H + originalRootStart raw + raw.roots.length < 2 ^ width)
    (nodesFit : nodes < 2 ^ width)
    (rankHeld : state.reg 4 = word width rankBase)
    (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (image : OriginalImageStored state.heap H channels raw)
    (ranks : ∀ index : Fin numbering.order.length,
      state.heap[rankBase + numbering.order[index.val].val]? = some (word width index.val)) :
    ∃ final peak, Execution resident state final (9 * raw.roots.length + 12) peak ∧
      peak ≤ state.liveWords + raw.roots.length ∧
      final.heap = state.heap ++
        (((numbering.toDAG.roots.map Fin.val).map (word width)).toArray) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 3 = word width 0 ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 3 → register ≠ 5 →
        final.reg register = state.reg register) := by
  obtain ⟨offsetCell, countCell⟩ := original_root_header_cells state.heap H channels raw image
  obtain ⟨selected, selection, selectedHeap, selectedStack, selectedOutput,
    selectedPC, selectedRunning, selectedCursor, selectedCount, selectedZeroCount,
    selectedQueueCursor, selectedRank, selectedZero, selectedMask⟩ :=
    root_setup_execution resident nodes base entry (entry + 11) H (originalRootStart raw)
      raw.roots.length state setupAt position running (by omega) (by omega)
      sourceFits zeroHeld rawCell offsetCell countCell
  have selectedLive : selected.liveWords = state.liveWords := by
    simp only [State.liveWords, selectedHeap, selectedStack, selectedOutput]
  let occurrences : List (MappedOccurrence width) :=
    numberedRootOccurrences (width := width) (raw.toUnordered valid) numbering
  have count : occurrences.length = raw.roots.length := by
    simp only [occurrences, numberedRootOccurrences, RawDAG.toUnordered,
      List.length_map, List.length_attach]
  have stored : MappedStreamStored selected.heap (H + originalRootStart raw) rankBase occurrences := by
    rw [selectedHeap]
    exact original_numbered_roots_stored raw valid numbering state.heap H rankBase image
      (by rw [← nodesEq]; exact nodesFit) ranks
  obtain ⟨final, peak, copying, space, heap, stack, output, pc, halted,
    cursor, remaining, held⟩ := mapped_stream_execution resident (entry + 11) done rankBase
      streamAt (by omega) occurrences (H + originalRootStart raw) selected selectedPC selectedRunning
      (by rw [selectedHeap, count]; exact room) (by rw [count]; exact sourceFits)
      (by rw [count]; omega) selectedCursor (by rw [count]; exact selectedCount)
      (selectedRank.trans rankHeld) (selectedZero.trans zeroHeld) (selectedMask.trans maskHeld) stored
  refine ⟨final, max state.liveWords peak, ?_, ?_, ?_, stack.trans selectedStack,
    output.trans selectedOutput, pc, halted, remaining, ?_⟩
  · have trace := selection.append copying
    convert trace using 1 <;> rw [count] <;> omega
  · rw [max_le_iff]
    constructor
    · omega
    · rw [selectedLive, count] at space
      exact space
  · rw [heap, selectedHeap]
    have words : occurrences.map MappedOccurrence.mapped =
        (numbering.toDAG.roots.map Fin.val).map (word width) := by
      simp only [occurrences, numberedRootOccurrences, UnorderedDAG.Numbering.toDAG,
        List.map_map, Function.comp_def]
    rw [words]
  · intro register notCursor notCount notTemporary
    have retained : selected.reg register = state.reg register := by
      fin_cases register <;> simp_all
    exact (held register notCursor notCount notTemporary).trans retained

theorem original_header_cells (heap : Array (Word width)) (H channels : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap H channels raw)
    (index : Nat) (valid : index < (originalRows raw).length) :
    heap[H + 9 + 2 * index]? =
        some (word width ((originalRows raw)[index]).tag) ∧
    heap[H + 9 + 2 * index + 1]? =
        some (word width ((originalRows raw)[index]).head) := by
  have first := cache_header_word (width := width) (originalHeaderHeap width channels raw)
    (originalRows raw) raw.roots (2 * index)
    (by rw [rowHeaders_length]; omega)
  have second := cache_header_word (width := width) (originalHeaderHeap width channels raw)
    (originalRows raw) raw.roots (2 * index + 1)
    (by rw [rowHeaders_length]; omega)
  rw [header_tag_value (originalRows raw) index valid] at first
  rw [header_head_value (originalRows raw) index valid] at second
  have bound0 : 9 + 2 * index < (originalPacket width channels raw).size := by
    rw [originalPacket, cacheHeap_size, original_header_size]
    omega
  have bound1 : 9 + 2 * index + 1 < (originalPacket width channels raw).size := by
    rw [originalPacket, cacheHeap_size, original_header_size]
    omega
  constructor
  · have cell : (originalPacket width channels raw)[9 + 2 * index]? =
        some (word width ((originalRows raw)[index]).tag) := by
      rw [Array.getElem?_eq_getElem bound0]
      exact congrArg some (by simpa only [originalPacket, original_header_size] using first)
    simpa only [Nat.add_assoc] using original_image_cell heap H channels raw image _ _ cell
  · have cell : (originalPacket width channels raw)[9 + 2 * index + 1]? =
        some (word width ((originalRows raw)[index]).head) := by
      rw [Array.getElem?_eq_getElem bound1]
      exact congrArg some (by simpa only [originalPacket, original_header_size, Nat.add_assoc] using second)
    simpa only [Nat.add_assoc] using original_image_cell heap H channels raw image _ _ cell


theorem original_arity_cells (heap : Array (Word width)) (H channels : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap H channels raw)
    (index : Nat) (valid : index < (originalRows raw).length) :
    heap[H + 9 + 4 * raw.nodes.size + 2 * index]? =
        some (word width ((originalRows raw)[index]).children.length) ∧
    heap[H + 9 + 4 * raw.nodes.size + 2 * index + 1]? =
        some (word width ((originalRows raw)[index]).guards.length) := by
  let rows := originalRows raw
  have rowValid : index < rows.length := valid
  have rowBound : index < raw.nodes.size := by simpa only [original_rows_length] using valid
  have room := original_packet_size (width := width) channels raw
  let beforeWords := rowHeaders rows ++
    rowBases rows (9 + 6 * rows.length)
      (9 + 6 * rows.length + (rowChildren rows).length)
  let afterWords := rowChildren rows ++ rowGuards rows ++ raw.roots
  have beforeLength : beforeWords.length = 4 * rows.length := by
    simp only [beforeWords, List.length_append, rowHeaders_length, rowBases_length]
    omega
  have packet : serializedRows 9 rows raw.roots =
      beforeWords ++ rowArities rows ++ afterWords := by
    simp only [serializedRows, beforeWords, afterWords, List.append_assoc]
  have first := allocated_segment_word (width := width)
    (originalHeaderHeap width channels raw) beforeWords (rowArities rows) afterWords
    (2 * index) (by rw [rowArities_length]; omega)
  have second := allocated_segment_word (width := width)
    (originalHeaderHeap width channels raw) beforeWords (rowArities rows) afterWords
    (2 * index + 1) (by rw [rowArities_length]; omega)
  obtain ⟨child, guard⟩ := row_arity_values rows index valid
  rw [child, countSource_value] at first
  rw [guard, countSource_value] at second
  have selected0 : (originalPacket width channels raw)[9 + 4 * raw.nodes.size + 2 * index]'(by omega) =
      word width (rows[index]).children.length := by
    simpa only [originalPacket, cacheHeap, original_header_size, packet,
      beforeLength, original_rows_length, rows, Nat.zero_add, Nat.add_assoc] using first
  have selected1 : (originalPacket width channels raw)[9 + 4 * raw.nodes.size + 2 * index + 1]'(by omega) =
      word width (rows[index]).guards.length := by
    simpa only [originalPacket, cacheHeap, original_header_size, packet,
      beforeLength, original_rows_length, rows, Nat.zero_add, Nat.add_assoc] using second
  constructor
  · have cell : (originalPacket width channels raw)[9 + 4 * raw.nodes.size + 2 * index]? =
        some (word width (rows[index]).children.length) := by
      rw [Array.getElem?_eq_getElem (by omega), selected0]
    simpa only [Nat.add_assoc] using original_image_cell heap H channels raw image _ _ cell
  · have cell : (originalPacket width channels raw)[9 + 4 * raw.nodes.size + 2 * index + 1]? =
        some (word width (rows[index]).guards.length) := by
      rw [Array.getElem?_eq_getElem (by omega), selected1]
    simpa only [Nat.add_assoc] using original_image_cell heap H channels raw image _ _ cell


theorem original_tag_lt (gate : RawGate) : (originalRow gate).tag < 5 := by
  cases gate <;> simp [originalRow]

def numberedHeaderRow (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (index : Fin numbering.order.length) : HeaderSourceRow width :=
  let old := numbering.oldIndex index
  let gate := raw.nodes[old.val]
  let source := originalRow gate
  { old := old.val
    tag := ⟨source.tag, original_tag_lt gate⟩
    head := source.head
    mapped := word width (UniformDAGSource.typedHead (numbering.toDAG.node index)) }

def numberedHeaderRows (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) : List (HeaderSourceRow width) :=
  (List.finRange numbering.order.length).map (numberedHeaderRow raw valid numbering)



def numberedRows (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) : List Row :=
  (List.finRange numbering.toDAG.nodeCount).map fun index =>
    originalRow (RawGate.ofGate (numbering.toDAG.node index))


theorem erased_typed_row_matches (gate : Gate channels available) :
    (originalRow (RawGate.ofGate gate)).Matches gate := by
  cases gate <;> simp [originalRow, RawGate.ofGate, Row.Matches,
    Gate.children, Gate.guardLabels]

theorem erased_typed_row_head (gate : Gate channels available) :
    (originalRow (RawGate.ofGate gate)).head = UniformDAGSource.typedHead gate := by
  cases gate <;> rfl

theorem numbered_rows_length (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    (numberedRows raw valid numbering).length = numbering.toDAG.nodeCount := by
  simp only [numberedRows, List.length_map, List.length_finRange]

theorem numbered_rows_match (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    RowsMatch numbering.toDAG (numberedRows raw valid numbering) := by
  refine ⟨numbered_rows_length raw valid numbering, ?_⟩
  intro index
  have chosenEq : (List.finRange numbering.toDAG.nodeCount)[index.val]'(by
      simpa only [List.length_finRange] using index.isLt) = index := by
    simp only [List.finRange, List.getElem_ofFn]
  simp only [numberedRows, List.getElem_map]
  rw [chosenEq]
  exact erased_typed_row_matches (numbering.toDAG.node index)

theorem numbered_rows_heads (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    UniformDAGSource.HeadsMatch numbering.toDAG (numberedRows raw valid numbering)
      (numbered_rows_match raw valid numbering) := by
  constructor
  intro index
  have chosenEq : (List.finRange numbering.toDAG.nodeCount)[index.val]'(by
      simpa only [List.length_finRange] using index.isLt) = index := by
    simp only [List.finRange, List.getElem_ofFn]
  simp only [numberedRows, List.getElem_map]
  rw [chosenEq]
  exact erased_typed_row_head (numbering.toDAG.node index)


def numberedChildRow (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (index : Fin numbering.order.length) : ChildSourceRow width :=
  let old := numbering.oldIndex index
  { old := old.val
    relative := 9 + 6 * raw.nodes.size +
      (rowChildren ((originalRows raw).take old.val)).length
    occurrences := ((raw.toUnordered valid).node old).children.map fun child =>
      ⟨child.val, word width (numbering.newIndex child).val⟩ }

def numberedChildRows (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) : List (ChildSourceRow width) :=
  (List.finRange numbering.order.length).map (numberedChildRow (width := width) raw valid numbering)

def numberedGuardRow (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (index : Fin numbering.order.length) : GuardSourceRow width :=
  let old := numbering.oldIndex index
  { old := old.val
    relative := 9 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
      (rowGuards ((originalRows raw).take old.val)).length
    values := (((raw.toUnordered valid).node old).guardLabels.map Fin.val).map (word width) }

def numberedGuardRows (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) : List (GuardSourceRow width) :=
  (List.finRange numbering.order.length).map (numberedGuardRow (width := width) raw valid numbering)



@[irreducible] def orderedTypedCopyCode (width nodes children base entry done : Nat) : Program width 8 :=
  typedGlobalCopyCode width nodes base (entry + 31) ++
  typedHeaderCopyCode width nodes base (entry + 31) (entry + 62) ++
  typedDirectorySetupCode width nodes children base (entry + 73) ++
  typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105) ++
  typedCopyRestartCode width nodes base (entry + 108) ++
  typedArityCopyCode width nodes base (entry + 108) (entry + 125) ++
  typedCopyRestartCode width nodes base (entry + 128) ++
  typedChildrenCopyCode width nodes base (entry + 128) (entry + 157) ++
  typedCopyRestartCode width nodes base (entry + 160) ++
  typedGuardsCopyCode width nodes base (entry + 160) (entry + 187) ++
  typedRootSetupCode width nodes base (entry + 198) ++
  mappedOccurrenceCopyCode width (entry + 198) done


theorem orderedTypedCopyCode_size (width nodes children base entry done : Nat) :
    (orderedTypedCopyCode width nodes children base entry done).size = 207 := by
  unfold orderedTypedCopyCode
  simp only [Array.size_append]
  simp only [typedGlobalCopyCode, typedHeaderCopyCode, typedDirectorySetupCode,
    typedDirectoryCopyCode, typedCopyRestartCode, typedArityCopyCode,
    typedChildrenCopyCode, typedGuardsCopyCode, typedSliceSetupCode,
    typedRowsBackedgeCode, mappedOccurrenceCopyCode, unchangedOccurrenceCopyCode,
    typedRootSetupCode, Array.size_append]
  rfl


theorem original_head_fit (gate : RawGate) (valid : gate.WellFormed channels nodes)
    (channelsFit : channels < 2 ^ width) (nodesFit : nodes < 2 ^ width) :
    (originalRow gate).head < 2 ^ width := by
  cases gate with
  | zero => simpa only [originalRow] using Nat.two_pow_pos width
  | input channel =>
    have bound := valid.2 channel (by simp only [RawGate.channels, List.mem_singleton])
    change channel < 2 ^ width
    omega
  | disj children => simpa only [originalRow] using Nat.two_pow_pos width
  | guard child labels =>
    have bound := valid.1 child (by simp only [RawGate.children, List.mem_singleton])
    change child < 2 ^ width
    omega
  | liveAnd left right =>
    have bound := valid.1 left (by simp only [RawGate.children, List.mem_cons, List.mem_singleton, true_or])
    change left < 2 ^ width
    omega

theorem original_selected_row (raw : RawDAG) (valid : raw.WellFormed channels)
    (old : Fin (raw.toUnordered valid).nodeCount) :
    (originalRows raw)[old.val]'(by rw [original_rows_length]; exact old.isLt) =
      originalRow (RawGate.ofGate ((raw.toUnordered valid).node old)) := by
  rw [RawDAG.toUnordered_node raw valid old]
  simp only [originalRows, List.getElem_map, Array.getElem_toList]


theorem mapped_head_rank (gate : Gate channels available)
    (mapper : (child : Fin available) → child ∈ gate.children → Fin target)
    (ranked : 3 ≤ (originalRow (RawGate.ofGate gate)).tag) :
    ∃ (child : Fin available) (membership : child ∈ gate.children),
      (originalRow (RawGate.ofGate gate)).head = child.val ∧
      UniformDAGSource.typedHead (gate.mapChildren mapper) = (mapper child membership).val := by
  cases gate with
  | zero => simp only [RawGate.ofGate, originalRow] at ranked; omega
  | input channel => simp only [RawGate.ofGate, originalRow] at ranked; omega
  | disj children => simp only [RawGate.ofGate, originalRow] at ranked; omega
  | guard child labels =>
    refine ⟨child, by simp only [Gate.children, List.mem_singleton], rfl, ?_⟩
    rfl
  | liveAnd left right =>
    refine ⟨left, by simp only [Gate.children, List.mem_cons, List.mem_singleton, true_or], rfl, ?_⟩
    rfl

theorem original_numbered_headers_stored (raw : RawDAG)
    (valid : raw.WellFormed channels) (numbering : (raw.toUnordered valid).Numbering)
    (heap : Array (Word width)) (H cursor rankBase : Nat)
    (image : OriginalImageStored heap H channels raw)
    (channelsFit : channels < 2 ^ width) (nodesFit : raw.nodes.size < 2 ^ width)
    (queue : ∀ index : Fin numbering.order.length,
      heap[cursor + index.val]? = some (word width numbering.order[index.val].val))
    (ranks : ∀ index : Fin numbering.order.length,
      heap[rankBase + numbering.order[index.val].val]? = some (word width index.val)) :
    HeaderRowsStored heap H cursor rankBase (numberedHeaderRows raw valid numbering) := by
  intro position
  have positionBound : position.val < numbering.order.length := by
    simpa only [numberedHeaderRows, List.length_map, List.length_finRange] using position.isLt
  let index : Fin numbering.order.length := ⟨position.val, positionBound⟩
  let old := numbering.oldIndex index
  let gate := (raw.toUnordered valid).node old
  have originalEq : originalRow raw.nodes[old.val] = originalRow (RawGate.ofGate gate) := by
    rw [RawDAG.toUnordered_node raw valid old]
  have originalRowEq : (originalRows raw)[old.val]'(by rw [original_rows_length]; exact old.isLt) =
      originalRow (RawGate.ofGate gate) := original_selected_row raw valid old
  have source := original_header_cells heap H channels raw image old.val
    (by rw [original_rows_length]; exact old.isLt)
  rw [originalRowEq] at source
  have rowAt : (numberedHeaderRows raw valid numbering)[position.val] =
      numberedHeaderRow raw valid numbering index := by
    simp only [numberedHeaderRows, List.getElem_map, List.getElem_finRange]
    rfl
  have held := queue index
  change heap[cursor + index.val]? = some (word width old.val) at held
  simp only [rowAt]
  change heap[cursor + index.val]? = some (word width old.val) ∧
    heap[H + 9 + 2 * old.val]? = some (word width (originalRow raw.nodes[old.val]).tag) ∧
    heap[H + 9 + 2 * old.val + 1]? = some (word width (originalRow raw.nodes[old.val]).head) ∧
    (3 ≤ (originalRow raw.nodes[old.val]).tag → heap[rankBase + (originalRow raw.nodes[old.val]).head]? =
      some (word width (UniformDAGSource.typedHead (numbering.toDAG.node index)))) ∧
    (originalRow raw.nodes[old.val]).head < 2 ^ width
  rw [originalEq]
  refine ⟨held, source.1, source.2, ?_, ?_⟩
  · intro ranked
    obtain ⟨child, membership, headEq, mappedEq⟩ :=
      mapped_head_rank gate (numbering.child index) ranked
    rw [headEq]
    have actual := produced_rank_cell (raw.toUnordered valid) numbering heap rankBase ranks child
    have mappedValue : UniformDAGSource.typedHead (numbering.toDAG.node index) =
        (numbering.newIndex child).val := mappedEq
    rw [mappedValue]
    exact actual
  · rw [← originalEq]
    exact original_head_fit raw.nodes[old.val] (valid.1 old) channelsFit nodesFit

def numberedDirectoryRow (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (index : Fin numbering.order.length) : DirectorySourceRow :=
  let old := numbering.oldIndex index
  let gate := (raw.toUnordered valid).node old
  ⟨old.val, gate.children.length, gate.guardLabels.length⟩

def numberedDirectoryRows (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) : List DirectorySourceRow :=
  (List.finRange numbering.order.length).map (numberedDirectoryRow raw valid numbering)

theorem erased_typed_row_counts (gate : Gate channels available) :
    (originalRow (RawGate.ofGate gate)).children.length = gate.children.length ∧
    (originalRow (RawGate.ofGate gate)).guards.length = gate.guardLabels.length := by
  cases gate <;> simp [originalRow, RawGate.ofGate, Gate.children, Gate.guardLabels]

theorem original_numbered_directory_stored (raw : RawDAG)
    (valid : raw.WellFormed channels) (numbering : (raw.toUnordered valid).Numbering)
    (heap : Array (Word width)) (H cursor : Nat)
    (image : OriginalImageStored heap H channels raw)
    (queue : ∀ index : Fin numbering.order.length,
      heap[cursor + index.val]? = some (word width (numbering.order[index.val].val))) :
    DirectoryRowsStored heap raw.nodes.size H cursor
      (numberedDirectoryRows raw valid numbering) := by
  intro position
  have positionBound : position.val < numbering.order.length := by
    simpa only [numberedDirectoryRows, List.length_map, List.length_finRange] using position.isLt
  let index : Fin numbering.order.length := ⟨position.val, positionBound⟩
  let old := numbering.oldIndex index
  let gate := (raw.toUnordered valid).node old
  have source := original_arity_cells heap H channels raw image old.val
    (by rw [original_rows_length]; exact old.isLt)
  rw [original_selected_row raw valid old] at source
  obtain ⟨childCount, guardCount⟩ := erased_typed_row_counts gate
  rw [childCount, guardCount] at source
  have rowAt : (numberedDirectoryRows raw valid numbering)[position.val] =
      numberedDirectoryRow raw valid numbering index := by
    simp only [numberedDirectoryRows, List.getElem_map, List.getElem_finRange]
    rfl
  have held := queue index
  change heap[cursor + index.val]? = some (word width old.val) at held
  simp only [rowAt]
  change heap[cursor + index.val]? = some (word width old.val) ∧
    heap[H + 9 + 4 * raw.nodes.size + 2 * old.val]? = some (word width gate.children.length) ∧
    heap[H + 9 + 4 * raw.nodes.size + 2 * old.val + 1]? = some (word width gate.guardLabels.length)
  exact ⟨held, source.1, source.2⟩

theorem original_child_cell (heap : Array (Word width)) (H channels : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap H channels raw)
    (index : Nat) (valid : index < (originalRows raw).length) (position : Nat)
    (inside : position < ((originalRows raw)[index]).children.length) :
    heap[H + (9 + 6 * raw.nodes.size +
      (rowChildren ((originalRows raw).take index)).length + position)]? =
        some (word width (((originalRows raw)[index]).children[position])) := by
  let rows := originalRows raw
  let beforeWords := rowHeaders rows ++
    rowBases rows (9 + 6 * rows.length)
      (9 + 6 * rows.length + (rowChildren rows).length) ++ rowArities rows
  let afterWords := rowGuards rows ++ raw.roots
  have beforeLength : beforeWords.length = 6 * raw.nodes.size := by
    simp only [beforeWords, List.length_append, rowHeaders_length, rowBases_length, rowArities_length]
    rw [show rows.length = raw.nodes.size from original_rows_length raw]
    omega
  have packet : serializedRows 9 rows raw.roots = beforeWords ++ rowChildren rows ++ afterWords := by
    simp only [serializedRows, beforeWords, afterWords, List.append_assoc]
  have selected := row_stream_cell Row.children rows index valid position inside
  obtain ⟨segmentBound, segmentValue⟩ := List.getElem?_eq_some_iff.mp selected
  have physical := allocated_segment_word (width := width)
    (originalHeaderHeap width channels raw) beforeWords (rowChildren rows) afterWords
    ((rowChildren (rows.take index)).length + position) segmentBound
  have physicalValue := physical.trans (congrArg (word width) segmentValue)
  have packetBound : 9 + 6 * raw.nodes.size +
      (rowChildren (rows.take index)).length + position < (originalPacket width channels raw).size := by
    rw [original_packet_size]
    change _ < 9 + 6 * raw.nodes.size + (rowChildren rows).length + (rowGuards rows).length + raw.roots.length
    change (rowChildren (rows.take index)).length + position < (rowChildren rows).length at segmentBound
    omega
  have cell : (originalPacket width channels raw)[9 + 6 * raw.nodes.size +
      (rowChildren (rows.take index)).length + position]? =
        some (word width ((rows[index]).children[position])) := by
    rw [Array.getElem?_eq_getElem packetBound]
    apply congrArg some
    simpa only [originalPacket, cacheHeap, original_header_size, ← packet,
      beforeLength, Nat.add_assoc] using physicalValue
  exact original_image_cell heap H channels raw image _ _ cell

theorem original_guard_cell (heap : Array (Word width)) (H channels : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap H channels raw)
    (index : Nat) (valid : index < (originalRows raw).length) (position : Nat)
    (inside : position < ((originalRows raw)[index]).guards.length) :
    heap[H + (9 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
      (rowGuards ((originalRows raw).take index)).length + position)]? =
        some (word width (((originalRows raw)[index]).guards[position])) := by
  let rows := originalRows raw
  let beforeWords := rowHeaders rows ++
    rowBases rows (9 + 6 * rows.length)
      (9 + 6 * rows.length + (rowChildren rows).length) ++ rowArities rows ++ rowChildren rows
  let afterWords := raw.roots
  have beforeLength : beforeWords.length = 6 * raw.nodes.size + (rowChildren rows).length := by
    simp only [beforeWords, List.length_append, rowHeaders_length, rowBases_length, rowArities_length]
    rw [show rows.length = raw.nodes.size from original_rows_length raw]
    omega
  have packet : serializedRows 9 rows raw.roots = beforeWords ++ rowGuards rows ++ afterWords := by
    simp only [serializedRows, beforeWords, afterWords, List.append_assoc]
  have selected := row_stream_cell Row.guards rows index valid position inside
  obtain ⟨segmentBound, segmentValue⟩ := List.getElem?_eq_some_iff.mp selected
  have physical := allocated_segment_word (width := width)
    (originalHeaderHeap width channels raw) beforeWords (rowGuards rows) afterWords
    ((rowGuards (rows.take index)).length + position) segmentBound
  have physicalValue := physical.trans (congrArg (word width) segmentValue)
  have packetBound : 9 + 6 * raw.nodes.size + (rowChildren rows).length +
      (rowGuards (rows.take index)).length + position < (originalPacket width channels raw).size := by
    rw [original_packet_size]
    change _ < 9 + 6 * raw.nodes.size + (rowChildren rows).length + (rowGuards rows).length + raw.roots.length
    change (rowGuards (rows.take index)).length + position < (rowGuards rows).length at segmentBound
    omega
  have cell : (originalPacket width channels raw)[9 + 6 * raw.nodes.size + (rowChildren rows).length +
      (rowGuards (rows.take index)).length + position]? =
        some (word width ((rows[index]).guards[position])) := by
    rw [Array.getElem?_eq_getElem packetBound]
    apply congrArg some
    simpa only [originalPacket, cacheHeap, original_header_size, ← packet,
      beforeLength, Nat.add_assoc] using physicalValue
  exact original_image_cell heap H channels raw image _ _ cell

theorem original_image_frame (heap final : Array (Word width))
    (H channels : Nat) (raw : RawDAG)
    (image : OriginalImageStored heap H channels raw)
    (preserve : ∀ (address : Nat) (value : Word width),
      heap[address]? = some value → final[address]? = some value) :
    OriginalImageStored final H channels raw := by
  intro index
  exact preserve _ _ (image index)

theorem appended_cell_frame (heap : Array (Word width)) (words : Array (Word width))
    (address : Nat) (value : Word width) (cell : heap[address]? = some value) :
    (heap ++ words)[address]? = some value := by
  obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
  rw [Array.getElem?_append_left valid]
  exact cell

theorem original_image_append (heap : Array (Word width)) (words : Array (Word width))
    (H channels : Nat) (raw : RawDAG) (image : OriginalImageStored heap H channels raw) :
    OriginalImageStored (heap ++ words) H channels raw :=
  original_image_frame heap (heap ++ words) H channels raw image
    (appended_cell_frame heap words)

theorem original_image_store_below (heap : Array (Word width))
    (slot : Nat) (stored : Word width) (H channels : Nat) (raw : RawDAG)
    (image : OriginalImageStored heap H channels raw) (below : slot < H) :
    OriginalImageStored (heap.setIfInBounds slot stored) H channels raw := by
  intro index
  exact directory_set_cell heap slot (H + index.val) stored _ (by omega) (image index)

theorem original_numbered_child_stream_stored (raw : RawDAG)
    (valid : raw.WellFormed channels) (numbering : (raw.toUnordered valid).Numbering)
    (heap : Array (Word width)) (H rankBase : Nat)
    (image : OriginalImageStored heap H channels raw)
    (nodesFit : raw.nodes.size < 2 ^ width)
    (ranks : ∀ index : Fin numbering.order.length,
      heap[rankBase + numbering.order[index.val].val]? = some (word width index.val))
    (index : Fin numbering.order.length) :
    MappedStreamStored heap (H + (numberedChildRow (width := width) raw valid numbering index).relative) rankBase
      (numberedChildRow (width := width) raw valid numbering index).occurrences := by
  let old := numbering.oldIndex index
  let gate := (raw.toUnordered valid).node old
  have oldBound : old.val < (originalRows raw).length := by
    rw [original_rows_length]
    exact old.isLt
  have rowEq := original_selected_row raw valid old
  have childrenEq : ((originalRows raw)[old.val]'(by rw [original_rows_length]; exact old.isLt)).children =
      gate.children.map Fin.val := by
    rw [rowEq]
    exact (erased_typed_row_matches gate).2.2.1
  intro position
  have childBound : position.val < gate.children.length := by
    simpa only [numberedChildRow, List.length_map] using position.isLt
  let child : Fin (raw.toUnordered valid).nodeCount := gate.children[position.val]
  have inside : position.val < ((originalRows raw)[old.val]).children.length := by
    rw [childrenEq, List.length_map]
    exact childBound
  have source := original_child_cell heap H channels raw image old.val
    (by rw [original_rows_length]; exact old.isLt) position.val inside
  have valueEq : ((originalRows raw)[old.val]).children[position.val] = child.val := by
    have optional := congrArg (fun values : List Nat => values[position.val]?) childrenEq
    rw [List.getElem?_eq_getElem inside, List.getElem?_map,
      List.getElem?_eq_getElem childBound, Option.map_some] at optional
    exact Option.some.inj optional
  rw [valueEq] at source
  have actualRank := produced_rank_cell (raw.toUnordered valid) numbering heap rankBase ranks child
  simp only [numberedChildRow, List.get_eq_getElem, List.getElem_map]
  change heap[(H + (9 + 6 * raw.nodes.size +
      (rowChildren ((originalRows raw).take old.val)).length)) + position.val]? =
        some (word width child.val) ∧
    heap[rankBase + child.val]? = some (word width (numbering.newIndex child).val) ∧
    child.val < 2 ^ width
  refine ⟨?_, actualRank, ?_⟩
  · simpa only [Nat.add_assoc] using source
  · have childFits := child.isLt
    change child.val < raw.nodes.size at childFits
    omega

theorem original_numbered_guard_stream_stored (raw : RawDAG)
    (valid : raw.WellFormed channels) (numbering : (raw.toUnordered valid).Numbering)
    (heap : Array (Word width)) (H : Nat)
    (image : OriginalImageStored heap H channels raw)
    (index : Fin numbering.order.length) :
    UnchangedStreamStored heap (H + (numberedGuardRow (width := width) raw valid numbering index).relative)
      (numberedGuardRow (width := width) raw valid numbering index).values := by
  let old := numbering.oldIndex index
  let gate := (raw.toUnordered valid).node old
  have oldBound : old.val < (originalRows raw).length := by
    rw [original_rows_length]
    exact old.isLt
  have rowEq := original_selected_row raw valid old
  have guardsEq : ((originalRows raw)[old.val]).guards = gate.guardLabels.map Fin.val := by
    rw [rowEq]
    exact (erased_typed_row_matches gate).2.2.2
  intro position
  have guardBound : position.val < gate.guardLabels.length := by
    simpa only [numberedGuardRow, List.length_map] using position.isLt
  have inside : position.val < ((originalRows raw)[old.val]).guards.length := by
    rw [guardsEq, List.length_map]
    exact guardBound
  have source := original_guard_cell heap H channels raw image old.val oldBound position.val inside
  have valueEq : ((originalRows raw)[old.val]).guards[position.val] = gate.guardLabels[position.val].val := by
    have optional := congrArg (fun values : List Nat => values[position.val]?) guardsEq
    rw [List.getElem?_eq_getElem inside, List.getElem?_map,
      List.getElem?_eq_getElem guardBound, Option.map_some] at optional
    exact Option.some.inj optional
  rw [valueEq] at source
  simp only [numberedGuardRow, List.get_eq_getElem, List.getElem_map]
  change heap[(H + (9 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
      (rowGuards ((originalRows raw).take old.val)).length)) + position.val]? =
    some (word width gate.guardLabels[position.val].val)
  simpa only [Nat.add_assoc] using source

theorem original_base_cells (heap : Array (Word width)) (H channels : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap H channels raw)
    (index : Nat) (valid : index < (originalRows raw).length) :
    heap[H + 9 + 2 * raw.nodes.size + 2 * index]? =
      some (word width (9 + 6 * raw.nodes.size + (rowChildren ((originalRows raw).take index)).length)) ∧
    heap[H + 9 + 2 * raw.nodes.size + 2 * index + 1]? =
      some (word width (9 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
        (rowGuards ((originalRows raw).take index)).length)) := by
  obtain ⟨child, guard⟩ := cache_base_words (width := width) (originalHeaderHeap width channels raw)
    (originalRows raw) raw.roots index valid
  have indexBound : index < raw.nodes.size := by simpa only [original_rows_length] using valid
  have size := original_packet_size (width := width) channels raw
  constructor
  · have cell : (originalPacket width channels raw)[9 + 2 * raw.nodes.size + 2 * index]? =
        some (word width (9 + 6 * raw.nodes.size + (rowChildren ((originalRows raw).take index)).length)) := by
      rw [Array.getElem?_eq_getElem (by omega)]
      apply congrArg some
      simpa only [originalPacket, original_header_size, original_rows_length] using child
    simpa only [Nat.add_assoc] using original_image_cell heap H channels raw image _ _ cell
  · have cell : (originalPacket width channels raw)[9 + 2 * raw.nodes.size + 2 * index + 1]? =
        some (word width (9 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards ((originalRows raw).take index)).length)) := by
      rw [Array.getElem?_eq_getElem (by omega)]
      apply congrArg some
      simpa only [originalPacket, original_header_size, original_rows_length, Nat.add_assoc] using guard
    simpa only [Nat.add_assoc] using original_image_cell heap H channels raw image _ _ cell

theorem original_numbered_children_stored (raw : RawDAG)
    (valid : raw.WellFormed channels) (numbering : (raw.toUnordered valid).Numbering)
    (heap : Array (Word width)) (H cursor rankBase : Nat)
    (image : OriginalImageStored heap H channels raw) (nodesFit : raw.nodes.size < 2 ^ width)
    (queue : ∀ index : Fin numbering.order.length,
      heap[cursor + index.val]? = some (word width (numbering.order[index.val].val)))
    (ranks : ∀ index : Fin numbering.order.length,
      heap[rankBase + numbering.order[index.val].val]? = some (word width index.val)) :
    ChildRowsStored heap raw.nodes.size H cursor rankBase (numberedChildRows (width := width) raw valid numbering) := by
  intro position
  have positionBound : position.val < numbering.order.length := by
    simpa only [numberedChildRows, List.length_map, List.length_finRange] using position.isLt
  let index : Fin numbering.order.length := ⟨position.val, positionBound⟩
  let old := numbering.oldIndex index
  let gate := (raw.toUnordered valid).node old
  have rowAt : (numberedChildRows (width := width) raw valid numbering)[position.val] =
      numberedChildRow (width := width) raw valid numbering index := by
    simp only [numberedChildRows, List.getElem_map, List.getElem_finRange]
    rfl
  have counts := original_numbered_directory_stored raw valid numbering heap H cursor image queue
    ⟨index.val, by simp only [numberedDirectoryRows, List.length_map, List.length_finRange]; exact index.isLt⟩
  have directoryRowAt : (numberedDirectoryRows raw valid numbering)[index.val]'(by
      simp only [numberedDirectoryRows, List.length_map, List.length_finRange]; exact index.isLt) =
      numberedDirectoryRow raw valid numbering index := by
    simp only [numberedDirectoryRows, List.getElem_map, List.getElem_finRange]
    rfl
  simp only [directoryRowAt] at counts
  change heap[cursor + index.val]? = some (word width old.val) ∧
    heap[H + 9 + 4 * raw.nodes.size + 2 * old.val]? = some (word width gate.children.length) ∧
    heap[H + 9 + 4 * raw.nodes.size + 2 * old.val + 1]? = some (word width gate.guardLabels.length) at counts
  have bases := original_base_cells heap H channels raw image old.val
    (by rw [original_rows_length]; exact old.isLt)
  simp only [rowAt]
  refine ⟨counts.1, bases.1, ?_, ?_⟩
  · simpa only [numberedChildRow, List.length_map] using counts.2.1
  · exact original_numbered_child_stream_stored raw valid numbering heap H rankBase image nodesFit ranks index

theorem original_numbered_guards_stored (raw : RawDAG)
    (valid : raw.WellFormed channels) (numbering : (raw.toUnordered valid).Numbering)
    (heap : Array (Word width)) (H cursor rankBase : Nat)
    (image : OriginalImageStored heap H channels raw)
    (queue : ∀ index : Fin numbering.order.length,
      heap[cursor + index.val]? = some (word width (numbering.order[index.val].val))) :
    GuardRowsStored heap raw.nodes.size H cursor rankBase (numberedGuardRows (width := width) raw valid numbering) := by
  intro position
  have positionBound : position.val < numbering.order.length := by
    simpa only [numberedGuardRows, List.length_map, List.length_finRange] using position.isLt
  let index : Fin numbering.order.length := ⟨position.val, positionBound⟩
  let old := numbering.oldIndex index
  let gate := (raw.toUnordered valid).node old
  have rowAt : (numberedGuardRows (width := width) raw valid numbering)[position.val] =
      numberedGuardRow (width := width) raw valid numbering index := by
    simp only [numberedGuardRows, List.getElem_map, List.getElem_finRange]
    rfl
  have counts := original_numbered_directory_stored raw valid numbering heap H cursor image queue
    ⟨index.val, by simp only [numberedDirectoryRows, List.length_map, List.length_finRange]; exact index.isLt⟩
  have directoryRowAt : (numberedDirectoryRows raw valid numbering)[index.val]'(by
      simp only [numberedDirectoryRows, List.length_map, List.length_finRange]; exact index.isLt) =
      numberedDirectoryRow raw valid numbering index := by
    simp only [numberedDirectoryRows, List.getElem_map, List.getElem_finRange]
    rfl
  simp only [directoryRowAt] at counts
  change heap[cursor + index.val]? = some (word width old.val) ∧
    heap[H + 9 + 4 * raw.nodes.size + 2 * old.val]? = some (word width gate.children.length) ∧
    heap[H + 9 + 4 * raw.nodes.size + 2 * old.val + 1]? = some (word width gate.guardLabels.length) at counts
  have bases := original_base_cells heap H channels raw image old.val
    (by rw [original_rows_length]; exact old.isLt)
  simp only [rowAt]
  refine ⟨counts.1, bases.2, ?_, ?_⟩
  · simpa only [numberedGuardRow, List.length_map] using counts.2.2
  · exact original_numbered_guard_stream_stored raw valid numbering heap H image index

def CopiedPacketCells (heap : Array (Word width)) (origin : Nat) (words : List (Word width)) : Prop :=
  ∀ index : Fin words.length, heap[origin + index.val]? = some words[index.val]

theorem copied_packet_frame (heap final : Array (Word width)) (origin : Nat)
    (words : List (Word width)) (stored : CopiedPacketCells heap origin words)
    (preserve : ∀ (address : Nat) (value : Word width), origin ≤ address →
      heap[address]? = some value → final[address]? = some value) :
    CopiedPacketCells final origin words := by
  intro index
  exact preserve _ _ (by omega) (stored index)

theorem copied_packet_append (heap : Array (Word width)) (origin : Nat)
    (beforeWords afterWords : List (Word width))
    (size : heap.size = origin + beforeWords.length)
    (stored : CopiedPacketCells heap origin beforeWords) :
    CopiedPacketCells (heap ++ afterWords.toArray) origin (beforeWords ++ afterWords) := by
  intro index
  by_cases earlier : index.val < beforeWords.length
  · have bounded : origin + index.val < heap.size := by omega
    have cell := stored ⟨index.val, earlier⟩
    rw [Array.getElem?_append_left bounded]
    simpa only [List.getElem_append_left earlier] using cell
  · have later : beforeWords.length ≤ index.val := by omega
    have bound := index.isLt
    simp only [List.length_append] at bound
    have afterBound : index.val - beforeWords.length < afterWords.length := by omega
    have addressAfter : heap.size ≤ origin + index.val := by omega
    have offset : origin + index.val - heap.size = index.val - beforeWords.length := by omega
    rw [Array.getElem?_append_right addressAfter, offset, List.getElem?_toArray,
      List.getElem?_eq_getElem afterBound, List.getElem_append_right later]

theorem copied_packet_concat (heap : Array (Word width)) (origin : Nat)
    (beforeWords afterWords : List (Word width))
    (beforeStored : CopiedPacketCells heap origin beforeWords)
    (afterStored : CopiedPacketCells heap (origin + beforeWords.length) afterWords) :
    CopiedPacketCells heap origin (beforeWords ++ afterWords) := by
  intro index
  by_cases earlier : index.val < beforeWords.length
  · simpa only [List.getElem_append_left earlier] using beforeStored ⟨index.val, earlier⟩
  · have later : beforeWords.length ≤ index.val := by omega
    have bound := index.isLt
    simp only [List.length_append] at bound
    have inside : index.val - beforeWords.length < afterWords.length := by omega
    have cell := afterStored ⟨index.val - beforeWords.length, inside⟩
    have address : (origin + beforeWords.length) + (index.val - beforeWords.length) =
        origin + index.val := by omega
    rw [address] at cell
    simpa only [List.getElem_append_right later] using cell

theorem copied_packet_directory (heap : Array (Word width)) (origin : Nat)
    (beforeWords : List (Word width)) (headSlot tailSlot childCursor guardCursor : Nat)
    (rows : List DirectorySourceRow) (size : heap.size = origin + beforeWords.length)
    (headBelow : headSlot < origin) (tailBelow : tailSlot < origin)
    (stored : CopiedPacketCells heap origin beforeWords) :
    CopiedPacketCells (directoryFoldHeap heap headSlot tailSlot childCursor guardCursor rows) origin
      (beforeWords ++ directoryCursorWords childCursor guardCursor rows) := by
  apply copied_packet_concat
  · apply copied_packet_frame heap _ origin beforeWords stored
    intro address value afterOrigin cell
    exact directory_fold_preserves heap headSlot tailSlot childCursor guardCursor rows address value
      (by omega) (by omega) cell
  · intro index
    have cell := directory_fold_packet heap headSlot tailSlot childCursor guardCursor rows
      (by omega) (by omega) index
    rw [size] at cell
    exact cell

/-- Every row and occurrence supplied to the fetched copy passes is obtained
from the original stored packet and the queue and rank cells produced by the
dependency runtime. No separate incidence table is required. -/
theorem source_copy_inputs (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (heap : Array (Word width)) (H cursor rankBase : Nat)
    (image : OriginalImageStored heap H channels raw)
    (channelsFit : channels < 2 ^ width) (nodesFit : raw.nodes.size < 2 ^ width)
    (queue : ∀ index : Fin numbering.order.length,
      heap[cursor + index.val]? = some (word width (numbering.order[index.val].val)))
    (ranks : ∀ index : Fin numbering.order.length,
      heap[rankBase + numbering.order[index.val].val]? = some (word width index.val)) :
    HeaderRowsStored heap H cursor rankBase (numberedHeaderRows raw valid numbering) ∧
    DirectoryRowsStored heap raw.nodes.size H cursor (numberedDirectoryRows raw valid numbering) ∧
    ChildRowsStored heap raw.nodes.size H cursor rankBase (numberedChildRows (width := width) raw valid numbering) ∧
    GuardRowsStored heap raw.nodes.size H cursor rankBase (numberedGuardRows (width := width) raw valid numbering) ∧
    MappedStreamStored heap (H + originalRootStart raw) rankBase
      (numberedRootOccurrences (raw.toUnordered valid) numbering) := by
  exact ⟨original_numbered_headers_stored raw valid numbering heap H cursor rankBase image channelsFit nodesFit queue ranks,
    original_numbered_directory_stored raw valid numbering heap H cursor image queue,
    original_numbered_children_stored raw valid numbering heap H cursor rankBase image nodesFit queue ranks,
    original_numbered_guards_stored raw valid numbering heap H cursor rankBase image queue,
    original_numbered_roots_stored raw valid numbering heap H rankBase image nodesFit ranks⟩


theorem original_global_cells (raw : RawDAG) (heap : Array (Word width))
    (H channels : Nat) (image : OriginalImageStored heap H channels raw) :
    RawGlobalCells heap H raw.nodes.size channels raw.roots.length
      (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length := by
  have first : heap[H]? = some (word width raw.nodes.size) := by
    have cell : (originalPacket width channels raw)[0]? = some (word width raw.nodes.size) := by
      rw [originalPacket, cacheHeap,
        ForestCursorMaterialize.allocatedHeap_prefix width _ _ 0
          (by rw [original_header_size]; decide)]
      simp only [originalHeaderHeap, originalHeader, List.getElem?_toArray,
        List.getElem?_map, List.getElem?_cons_zero, Option.map_some, original_rows_length]
    simpa only [Nat.add_zero] using original_image_cell heap H channels raw image _ _ cell
  have second : heap[H + 1]? = some (word width channels) := by
    apply original_image_cell heap H channels raw image
    rw [originalPacket, cacheHeap,
      ForestCursorMaterialize.allocatedHeap_prefix width _ _ 1
        (by rw [original_header_size]; decide)]
    simp only [originalHeaderHeap, originalHeader, List.getElem?_toArray,
      List.getElem?_map, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some]
  have third : heap[H + 2]? = some (word width raw.roots.length) := by
    apply original_image_cell heap H channels raw image
    rw [originalPacket, cacheHeap,
      ForestCursorMaterialize.allocatedHeap_prefix width _ _ 2
        (by rw [original_header_size]; decide)]
    simp only [originalHeaderHeap, originalHeader, List.getElem?_toArray,
      List.getElem?_map, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some]
  have fourth : heap[H + 3]? = some (word width (rowChildren (originalRows raw)).length) := by
    apply original_image_cell heap H channels raw image
    rw [originalPacket, cacheHeap,
      ForestCursorMaterialize.allocatedHeap_prefix width _ _ 3
        (by rw [original_header_size]; decide)]
    simp only [originalHeaderHeap, originalHeader, List.getElem?_toArray,
      List.getElem?_map, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some]
  have fifth : heap[H + 4]? = some (word width (rowGuards (originalRows raw)).length) := by
    apply original_image_cell heap H channels raw image
    rw [originalPacket, cacheHeap,
      ForestCursorMaterialize.allocatedHeap_prefix width _ _ 4
        (by rw [original_header_size]; decide)]
    simp only [originalHeaderHeap, originalHeader, List.getElem?_toArray,
      List.getElem?_map, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some]
  exact ⟨first, second, third, fourth, fifth⟩

structure RetainedCopyFacts (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (heap : Array (Word width)) (H base rankBase : Nat) : Prop where
  image : OriginalImageStored heap H channels raw
  rawBase : heap[Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base]? = some (word width H)
  queue : ∀ index : Fin numbering.order.length,
    heap[Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + index.val]? =
      some (word width (numbering.order[index.val].val))
  ranks : ∀ index : Fin numbering.order.length,
    heap[rankBase + numbering.order[index.val].val]? = some (word width index.val)


theorem retained_copy_append (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (heap : Array (Word width))
    (H base rankBase : Nat) (words : Array (Word width))
    (facts : RetainedCopyFacts raw valid numbering heap H base rankBase) :
    RetainedCopyFacts raw valid numbering (heap ++ words) H base rankBase := by
  refine ⟨original_image_append heap words H channels raw facts.image,
    appended_cell_frame heap words _ _ facts.rawBase, ?_, ?_⟩
  · intro index
    exact appended_cell_frame heap words _ _ (facts.queue index)
  · intro index
    exact appended_cell_frame heap words _ _ (facts.ranks index)

theorem retained_copy_store (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (heap : Array (Word width))
    (H base rankBase slot : Nat) (value : Word width)
    (facts : RetainedCopyFacts raw valid numbering heap H base rankBase)
    (sourceBelow : slot < H)
    (queueBelow : slot < Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)
    (rankBelow : slot < rankBase)
    (rawDifferent : slot ≠ Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base) :
    RetainedCopyFacts raw valid numbering (heap.setIfInBounds slot value) H base rankBase := by
  refine ⟨original_image_store_below heap slot value H channels raw facts.image sourceBelow,
    directory_set_cell heap slot _ value _ rawDifferent facts.rawBase, ?_, ?_⟩
  · intro index
    exact directory_set_cell heap slot _ value _ (by omega) (facts.queue index)
  · intro index
    exact directory_set_cell heap slot _ value _ (by omega) (facts.ranks index)

theorem retained_copy_directory (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (heap : Array (Word width))
    (H base rankBase headSlot tailSlot childCursor guardCursor : Nat)
    (rows : List DirectorySourceRow)
    (facts : RetainedCopyFacts raw valid numbering heap H base rankBase)
    (headSource : headSlot < H) (tailSource : tailSlot < H)
    (headQueue : headSlot < Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)
    (tailQueue : tailSlot < Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)
    (headRank : headSlot < rankBase) (tailRank : tailSlot < rankBase)
    (headRaw : headSlot < Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base)
    (tailRaw : tailSlot < Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base) :
    RetainedCopyFacts raw valid numbering
      (directoryFoldHeap heap headSlot tailSlot childCursor guardCursor rows) H base rankBase := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro index
    exact directory_fold_preserves heap headSlot tailSlot childCursor guardCursor rows
      (H + index.val) _ (by omega) (by omega) (facts.image index)
  · exact directory_fold_preserves heap headSlot tailSlot childCursor guardCursor rows
      _ _ headRaw tailRaw facts.rawBase
  · intro index
    exact directory_fold_preserves heap headSlot tailSlot childCursor guardCursor rows
      _ _ (by omega) (by omega) (facts.queue index)
  · intro index
    exact directory_fold_preserves heap headSlot tailSlot childCursor guardCursor rows
      _ _ (by omega) (by omega) (facts.ranks index)

theorem directory_next_slot_preserved (heap : Array (Word width))
    (headSlot tailSlot nextSlot childCursor guardCursor origin : Nat)
    (rows : List DirectorySourceRow)
    (headBelow : headSlot < nextSlot) (tailBelow : tailSlot < nextSlot)
    (stored : heap[nextSlot]? = some (word width origin)) :
    (directoryFoldHeap heap headSlot tailSlot childCursor guardCursor rows)[nextSlot]? =
      some (word width origin) :=
  directory_fold_preserves heap headSlot tailSlot childCursor guardCursor rows
    nextSlot (word width origin) headBelow tailBelow stored

theorem retained_copy_setup_stores (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (heap : Array (Word width))
    (H base rankBase headSlot tailSlot childCursor guardCursor : Nat)
    (facts : RetainedCopyFacts raw valid numbering heap H base rankBase)
    (headSource : headSlot < H) (tailSource : tailSlot < H)
    (headQueue : headSlot < Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)
    (tailQueue : tailSlot < Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)
    (headRank : headSlot < rankBase) (tailRank : tailSlot < rankBase)
    (headRaw : headSlot ≠ Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base)
    (tailRaw : tailSlot ≠ Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base) :
    RetainedCopyFacts raw valid numbering
      ((heap.setIfInBounds headSlot (word width childCursor)).setIfInBounds tailSlot
        (word width guardCursor)) H base rankBase := by
  exact retained_copy_store raw valid numbering _ H base rankBase tailSlot (word width guardCursor)
    (retained_copy_store raw valid numbering heap H base rankBase headSlot (word width childCursor)
      facts headSource headQueue headRank headRaw)
    tailSource tailQueue tailRank tailRaw

theorem ordered_copy_tick_sum (nodes children guards roots : Nat) :
    31 + (28 * nodes + 1) + 11 + (32 * nodes + 1) + 3 + (17 * nodes + 1) + 3 +
      (21 * nodes + 9 * children + 1) + 3 + (21 * nodes + 7 * guards + 1) +
      (9 * roots + 12) = 119 * nodes + 9 * children + 7 * guards + 9 * roots + 68 := by
  omega

theorem ordered_copy_allocation_sum (nodes children guards roots : Nat) :
    5 + 2 * nodes + 2 * nodes + 2 * nodes + children + guards + roots =
      5 + 6 * nodes + children + guards + roots := by
  omega

theorem retained_copy_global (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (heap : Array (Word width))
    (H base rankBase : Nat) (globalWords : Array (Word width))
    (facts : RetainedCopyFacts raw valid numbering heap H base rankBase)
    (sourceBelow : Controller.Horn.WorklistBucketReady.nextSlot (n := raw.nodes.size) base < H)
    (rankAfter : H ≤ rankBase) :
    RetainedCopyFacts raw valid numbering
      (heap.setIfInBounds (Controller.Horn.WorklistBucketReady.nextSlot (n := raw.nodes.size) base)
        (word width heap.size) ++ globalWords) H base rankBase := by
  apply retained_copy_append
  apply retained_copy_store raw valid numbering heap H base rankBase _ (word width heap.size) facts
  · exact sourceBelow
  · simp only [Controller.Horn.WorklistBucketReady.nextSlot,
      Controller.Horn.WorklistMark.queueStart]
    omega
  · omega
  · simp only [Controller.Horn.WorklistBucketReady.nextSlot,
      Controller.Horn.WorklistFIFO.activeSlot]
    omega

theorem global_origin_cell (heap : Array (Word width)) (slot : Nat)
    (globalWords : Array (Word width)) (valid : slot < heap.size) :
    (heap.setIfInBounds slot (word width heap.size) ++ globalWords)[slot]? =
      some (word width heap.size) := by
  apply appended_cell_frame
  simp only [Array.getElem?_setIfInBounds, valid, ite_true]

structure OrderedCopyInvariant (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (initial state : State width 8)
    (H base rankBase origin : Nat) (copied : List (Word width)) : Prop where
  retained : RetainedCopyFacts raw valid numbering state.heap H base rankBase
  packet : CopiedPacketCells state.heap origin copied
  allocation : state.heap.size = origin + copied.length
  originCell : state.heap[Controller.Horn.WorklistBucketReady.nextSlot (n := raw.nodes.size) base]? =
    some (word width origin)
  stack : state.stack = initial.stack
  output : state.output = initial.output
  rankRegister : state.reg 4 = word width rankBase
  zeroRegister : state.reg 6 = word width 0
  maskRegister : state.reg 7 = word width (2 ^ width - 1)
  running : state.halted = false

theorem ordered_copy_live (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (initial state : State width 8)
    (H base rankBase origin : Nat) (copied : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin copied)
    (originSize : origin = initial.heap.size) :
    state.liveWords = initial.liveWords + copied.length := by
  simp only [State.liveWords, invariant.allocation, invariant.stack, invariant.output, originSize]
  omega

def numberedGlobalWords (raw : RawDAG) (channels : Nat) : List (Word width) :=
  [word width channels, word width raw.nodes.size,
    word width (rowChildren (originalRows raw)).length,
    word width (rowGuards (originalRows raw)).length, word width raw.roots.length]

def numberedPacketWords (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) : List (Word width) :=
  numberedGlobalWords (width := width) raw channels ++
  copiedHeaderWords (numberedHeaderRows raw valid numbering) ++
  directoryCursorWords (width := width) (5 + 6 * raw.nodes.size)
    (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length)
    (numberedDirectoryRows raw valid numbering) ++
  copiedArityWords (width := width) (numberedDirectoryRows raw valid numbering) ++
  copiedChildWords (numberedChildRows (width := width) raw valid numbering) ++
  copiedGuardWords (numberedGuardRows (width := width) raw valid numbering) ++
  (numbering.toDAG.roots.map Fin.val).map (word width)

theorem original_packet_stored_end (heap : Array (Word width)) (H channels : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap H channels raw) :
    H + (originalPacket width channels raw).size ≤ heap.size := by
  have positive : 0 < (originalPacket width channels raw).size := by
    rw [original_packet_size]
    omega
  have cell := image ⟨(originalPacket width channels raw).size - 1, by omega⟩
  obtain ⟨bound, value⟩ := Array.getElem?_eq_some_iff.mp cell
  change H + ((originalPacket width channels raw).size - 1) < heap.size at bound
  omega

theorem copied_header_words_length (rows : List (HeaderSourceRow width)) :
    (copiedHeaderWords rows).length = 2 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    dsimp only [copiedHeaderWords] at ih
    simp only [copiedHeaderWords, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem copied_arity_words_length (rows : List DirectorySourceRow) :
    (copiedArityWords (width := width) rows).length = 2 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    dsimp only [copiedArityWords] at ih
    simp only [copiedArityWords, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem extract_copy_section (resident whole before fragment after : Program width 8)
    (entry offset length : Nat)
    (layout : whole = (before ++ fragment) ++ after)
    (beforeSize : before.size = offset) (sectionSize : fragment.size = length)
    (physical : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]?) :
    ∀ phase : Fin length, resident[(entry + offset) + phase.val]? = fragment[phase.val]? := by
  intro phase
  have partBound : offset + phase.val < (before ++ fragment).size := by
    simp only [Array.size_append, beforeSize, sectionSize]
    omega
  have wholeBound : offset + phase.val < whole.size := by
    rw [layout]
    simp only [Array.size_append, beforeSize, sectionSize]
    omega
  have selected := physical ⟨offset + phase.val, wholeBound⟩
  change resident[entry + (offset + phase.val)]? = whole[offset + phase.val]? at selected
  rw [layout, Array.getElem?_append_left partBound,
    Array.getElem?_append_right (by rw [beforeSize]; omega)] at selected
  have indexEq : offset + phase.val - before.size = phase.val := by rw [beforeSize]; omega
  rw [indexEq] at selected
  simpa only [Nat.add_assoc] using selected

theorem source_global_stage (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (state : State width 8) (H base rankBase entry headerEntry : Nat)
    (facts : RetainedCopyFacts raw valid numbering state.heap H base rankBase)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedGlobalCopyCode width raw.nodes.size base headerEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 31 < 2 ^ width) (room : state.heap.size + 5 < 2 ^ width)
    (allocation : state.heap.size = rankBase + raw.nodes.size)
    (rankHeld : state.reg 4 = word width rankBase)
    (nextBelow : Controller.Horn.WorklistBucketReady.nextSlot (n := raw.nodes.size) base < H)
    (rankAfter : H ≤ rankBase) :
    ∃ final peak, Execution resident state final 31 peak ∧ peak ≤ state.liveWords + 5 ∧
      final.pc = word width headerEntry ∧
      OrderedCopyInvariant raw valid numbering state final H base rankBase state.heap.size
        (numberedGlobalWords (width := width) raw channels) ∧
      final.reg 0 = word width raw.nodes.size ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base) := by
  obtain ⟨final, peak, trace, space, heap, stack, output, pc, halted, count, cursor, rank, zero, mask⟩ :=
    typed_global_execution resident raw.nodes.size channels raw.roots.length
      (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
      base entry headerEntry H rankBase state physical position running codeFits room allocation rankHeld
      nextBelow facts.rawBase (original_global_cells raw state.heap H channels facts.image)
  let slot := Controller.Horn.WorklistBucketReady.nextSlot (n := raw.nodes.size) base
  let globals := numberedGlobalWords (width := width) raw channels
  have slotValid : slot < state.heap.size := by omega
  have heapEq : final.heap = state.heap.setIfInBounds slot (word width state.heap.size) ++ globals.toArray := by
    simpa only [slot, globals, numberedGlobalWords] using heap
  refine ⟨final, peak, trace, space, pc, ?_, count, cursor⟩
  refine ⟨?_, ?_, ?_, ?_, stack, output, rank.trans rankHeld, zero, mask, halted⟩
  · rw [heapEq]
    exact retained_copy_global raw valid numbering state.heap H base rankBase globals.toArray facts nextBelow rankAfter
  · rw [heapEq]
    have empty : CopiedPacketCells (state.heap.setIfInBounds slot (word width state.heap.size))
        state.heap.size [] := by intro index; exact False.elim (Nat.not_lt_zero _ index.isLt)
    exact copied_packet_append _ state.heap.size [] globals
      (by simp only [Array.size_setIfInBounds, List.length_nil, Nat.add_zero]) empty
  · rw [heapEq]
    simp only [Array.size_append, Array.size_setIfInBounds, List.size_toArray]
    rfl
  · rw [heapEq]
    exact global_origin_cell state.heap slot globals.toArray slotValid

theorem source_header_stage (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (initial state : State width 8) (H base rankBase origin entry done : Nat)
    (beforeWords : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin beforeWords)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedHeaderCopyCode width raw.nodes.size base entry done)[phase.val]?)
    (position : state.pc = word width entry) (codeFits : entry + 31 < 2 ^ width)
    (room : state.heap.size + 2 * numbering.order.length < 2 ^ width)
    (cursorFits : Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base +
      numbering.order.length < 2 ^ width)
    (channelsFit : channels < 2 ^ width) (nodesFit : raw.nodes.size < 2 ^ width)
    (countHeld : state.reg 0 = word width numbering.order.length)
    (cursorHeld : state.reg 1 = word width
      (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 28 * numbering.order.length + 1 ∧
      peak ≤ state.liveWords + 2 * numbering.order.length ∧
      final.pc = word width done ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase origin
        (beforeWords ++ copiedHeaderWords (numberedHeaderRows raw valid numbering)) := by
  let rows := numberedHeaderRows (width := width) raw valid numbering
  have rowLength : rows.length = numbering.order.length := by
    simp only [rows, numberedHeaderRows, List.length_map, List.length_finRange]
  have stored := original_numbered_headers_stored raw valid numbering state.heap H
    (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base) rankBase
    invariant.retained.image channelsFit nodesFit invariant.retained.queue invariant.retained.ranks
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, output, pc, running,
    count, cursor, ranks, zero, mask⟩ := header_loop_execution resident raw.nodes.size base entry done H
      rankBase physical codeFits rows _ state position invariant.running
      (by simpa only [rowLength] using room)
      (by simpa only [rowLength] using cursorFits)
      (by rw [rowLength, numbering.length_eq_nodeCount]; exact nodesFit)
      (by simpa only [rowLength] using countHeld) cursorHeld invariant.rankRegister
      invariant.zeroRegister invariant.maskRegister invariant.retained.rawBase stored
  dsimp only [rows] at heap
  refine ⟨final, ticks, peak, trace, by simpa only [rowLength] using time,
    by simpa only [rowLength] using space, pc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, stack.trans invariant.stack, output.trans invariant.output,
    ranks.trans invariant.rankRegister, zero.trans invariant.zeroRegister,
    mask.trans invariant.maskRegister, running⟩
  · rw [heap]
    exact retained_copy_append raw valid numbering state.heap H base rankBase _ invariant.retained
  · rw [heap]
    exact copied_packet_append state.heap origin beforeWords _ invariant.allocation invariant.packet
  · rw [heap]
    simp only [Array.size_append, List.size_toArray, List.length_append, invariant.allocation]
    omega
  · rw [heap]
    exact appended_cell_frame state.heap _ _ _ invariant.originCell

theorem source_directory_setup (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (initial state : State width 8) (H base rankBase origin entry loop children : Nat)
    (beforeWords : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin beforeWords)
    (physical : ∀ phase : Fin 11, resident[entry + phase.val]? =
      (typedDirectorySetupCode width raw.nodes.size children base loop)[phase.val]?)
    (position : state.pc = word width entry) (codeFits : entry + 11 < 2 ^ width)
    (room : state.heap.size < 2 ^ width)
    (scratchBelow : Controller.Horn.WorklistBucketReady.tailSlot (n := raw.nodes.size) base < H)
    (rankAfter : H ≤ rankBase) (originAfter : H ≤ origin) :
    ∃ final, Execution resident state final 11 state.liveWords ∧ final.pc = word width loop ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase origin beforeWords ∧
      final.reg 0 = word width raw.nodes.size ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base) ∧
      final.heap[Controller.Horn.WorklistFIFO.headSlot (n := raw.nodes.size) base]? =
        some (word width (5 + 6 * raw.nodes.size)) ∧
      final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := raw.nodes.size) base]? =
        some (word width (5 + 6 * raw.nodes.size + children)) := by
  let head := Controller.Horn.WorklistFIFO.headSlot (n := raw.nodes.size) base
  let tail := Controller.Horn.WorklistBucketReady.tailSlot (n := raw.nodes.size) base
  have headTail : head < tail := by simp only [head, tail, Controller.Horn.WorklistFIFO.headSlot,
    Controller.Horn.WorklistBucketReady.tailSlot]; omega
  have sourceRoom : H < state.heap.size := by
    have cell := invariant.retained.image ⟨0, by rw [original_packet_size]; omega⟩
    obtain ⟨bound, value⟩ := Array.getElem?_eq_some_iff.mp cell
    simpa only [Nat.add_zero] using bound
  obtain ⟨final, trace, heap, stack, output, pc, running, count, cursor, ranks, zero, mask⟩ :=
    directory_setup_execution resident raw.nodes.size children base entry loop rankBase state physical
      position invariant.running codeFits room (by omega) invariant.rankRegister
  have tailValid : tail < state.heap.size := by omega
  have headValid : head < state.heap.size := by omega
  have headCell : final.heap[head]? = some (word width (5 + 6 * raw.nodes.size)) := by
    rw [heap]
    change ((state.heap.setIfInBounds head (word width (5 + 6 * raw.nodes.size))).setIfInBounds
      tail (word width (5 + 6 * raw.nodes.size + children)))[head]? = _
    simp only [Array.getElem?_setIfInBounds, headValid, ite_true,
      show tail ≠ head from Ne.symm (Nat.ne_of_lt headTail), ite_false]
  have tailCell : final.heap[tail]? = some (word width (5 + 6 * raw.nodes.size + children)) := by
    rw [heap]
    change ((state.heap.setIfInBounds head (word width (5 + 6 * raw.nodes.size))).setIfInBounds
      tail (word width (5 + 6 * raw.nodes.size + children)))[tail]? = _
    simp only [Array.getElem?_setIfInBounds, Array.size_setIfInBounds, tailValid, ite_true]
  refine ⟨final, trace, pc, ?_, count, cursor, headCell, tailCell⟩
  refine ⟨?_, ?_, ?_, ?_, stack.trans invariant.stack, output.trans invariant.output,
    ranks.trans invariant.rankRegister, zero, mask, running⟩
  · rw [heap]
    apply retained_copy_setup_stores raw valid numbering state.heap H base rankBase head tail _ _ invariant.retained
    all_goals simp only [head, tail, Controller.Horn.WorklistFIFO.headSlot,
      Controller.Horn.WorklistBucketReady.tailSlot, Controller.Horn.WorklistMark.queueStart,
      Controller.Horn.WorklistFIFO.activeSlot] at * <;> omega
  · rw [heap]
    apply copied_packet_frame state.heap _ origin beforeWords invariant.packet
    intro address value afterOrigin cell
    exact directory_set_cell _ tail address _ value (by omega)
      (directory_set_cell state.heap head address _ value (by omega) cell)
  · rw [heap]
    simpa only [Array.size_setIfInBounds] using invariant.allocation
  · rw [heap]
    exact directory_set_cell _ tail _ _ _ (by
        simp only [tail, Controller.Horn.WorklistBucketReady.tailSlot,
          Controller.Horn.WorklistBucketReady.nextSlot]; omega)
      (directory_set_cell state.heap head _ _ _ (by
        simp only [head, Controller.Horn.WorklistFIFO.headSlot,
          Controller.Horn.WorklistBucketReady.nextSlot]; omega) invariant.originCell)

theorem source_directory_stage (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (initial state : State width 8) (H base rankBase origin entry done childCursor guardCursor : Nat)
    (beforeWords : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin beforeWords)
    (physical : ∀ phase : Fin 32, resident[entry + phase.val]? =
      (typedDirectoryCopyCode width raw.nodes.size base entry done)[phase.val]?)
    (position : state.pc = word width entry) (codeFits : entry + 32 < 2 ^ width)
    (room : state.heap.size + 2 * numbering.order.length < 2 ^ width)
    (cursorFits : Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base +
      numbering.order.length < 2 ^ width)
    (nodesFit : raw.nodes.size < 2 ^ width)
    (childFits : childCursor + ((numberedDirectoryRows raw valid numbering).map DirectorySourceRow.children).sum < 2 ^ width)
    (guardFits : guardCursor + ((numberedDirectoryRows raw valid numbering).map DirectorySourceRow.guards).sum < 2 ^ width)
    (countHeld : state.reg 0 = word width numbering.order.length)
    (cursorHeld : state.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base))
    (childCell : state.heap[Controller.Horn.WorklistFIFO.headSlot (n := raw.nodes.size) base]? = some (word width childCursor))
    (guardCell : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := raw.nodes.size) base]? = some (word width guardCursor))
    (scratchBelow : Controller.Horn.WorklistBucketReady.tailSlot (n := raw.nodes.size) base < H)
    (rankAfter : H ≤ rankBase) (originAfter : H ≤ origin) :
    ∃ final peak, Execution resident state final (32 * numbering.order.length + 1) peak ∧
      peak ≤ state.liveWords + 2 * numbering.order.length ∧ final.pc = word width done ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase origin
        (beforeWords ++ directoryCursorWords childCursor guardCursor (numberedDirectoryRows raw valid numbering)) := by
  let rows := numberedDirectoryRows raw valid numbering
  let head := Controller.Horn.WorklistFIFO.headSlot (n := raw.nodes.size) base
  let tail := Controller.Horn.WorklistBucketReady.tailSlot (n := raw.nodes.size) base
  let cursor := Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base
  have headTail : head < tail := by simp only [head, tail, Controller.Horn.WorklistFIFO.headSlot,
    Controller.Horn.WorklistBucketReady.tailSlot]; omega
  have tailQueue : tail < cursor := by simp only [tail, cursor,
    Controller.Horn.WorklistBucketReady.tailSlot, Controller.Horn.WorklistMark.queueStart]; omega
  have rowLength : rows.length = numbering.order.length := by
    simp only [rows, numberedDirectoryRows, List.length_map, List.length_finRange]
  have stored := original_numbered_directory_stored raw valid numbering state.heap H cursor
    invariant.retained.image invariant.retained.queue
  obtain ⟨final, peak, trace, space, heap, stack, output, pc, running, count, nextCursor,
      ranks, zero, mask⟩ := directory_loop_execution resident raw.nodes.size base entry done H
    childCursor guardCursor rows physical codeFits cursor state position invariant.running
    (by simpa only [rowLength] using room) (by simpa only [rowLength] using cursorFits)
    (by rw [rowLength, numbering.length_eq_nodeCount]; exact nodesFit) childFits guardFits
    (by simpa only [rowLength] using countHeld) cursorHeld invariant.zeroRegister invariant.maskRegister
    childCell guardCell invariant.retained.rawBase scratchBelow tailQueue stored
  dsimp only [rows] at heap
  refine ⟨final, peak, by simpa only [rowLength] using trace,
    by simpa only [rowLength] using space, pc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, stack.trans invariant.stack, output.trans invariant.output,
    ranks.trans invariant.rankRegister, zero.trans invariant.zeroRegister,
    mask.trans invariant.maskRegister, running⟩
  · rw [heap]
    apply retained_copy_directory raw valid numbering state.heap H base rankBase head tail
      childCursor guardCursor rows invariant.retained <;>
      simp only [head, tail, Controller.Horn.WorklistFIFO.headSlot,
        Controller.Horn.WorklistBucketReady.tailSlot, Controller.Horn.WorklistMark.queueStart,
        Controller.Horn.WorklistFIFO.activeSlot] at * <;> omega
  · rw [heap]
    exact copied_packet_directory state.heap origin beforeWords head tail childCursor guardCursor
      rows invariant.allocation (by omega) (by omega) invariant.packet
  · rw [heap, directory_fold_size, invariant.allocation]
    simp only [List.length_append, directory_cursor_words_length]
    omega
  · rw [heap]
    exact directory_next_slot_preserved state.heap head tail _ childCursor guardCursor origin rows
      (by simp only [head, Controller.Horn.WorklistFIFO.headSlot, Controller.Horn.WorklistBucketReady.nextSlot]; omega)
      (by simp only [tail, Controller.Horn.WorklistBucketReady.tailSlot, Controller.Horn.WorklistBucketReady.nextSlot]; omega)
      invariant.originCell

theorem source_copy_restart (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (initial state : State width 8) (H base rankBase origin entry next : Nat)
    (copied : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin copied)
    (physical : ∀ phase : Fin 3, resident[entry + phase.val]? =
      (typedCopyRestartCode width raw.nodes.size base next)[phase.val]?)
    (position : state.pc = word width entry) (codeFits : entry + 3 < 2 ^ width) :
    ∃ final, Execution resident state final 3 state.liveWords ∧ final.pc = word width next ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase origin copied ∧
      final.reg 0 = word width raw.nodes.size ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base) := by
  obtain ⟨final, trace, heap, stack, output, pc, running, count, cursor, ranks, zero, mask⟩ :=
    typed_copy_restart_execution resident raw.nodes.size base entry next state physical position
      invariant.running codeFits invariant.zeroRegister
  refine ⟨final, trace, pc, ?_, count, cursor⟩
  refine ⟨?_, ?_, ?_, ?_, stack.trans invariant.stack, output.trans invariant.output,
    ranks.trans invariant.rankRegister, zero.trans invariant.zeroRegister,
    mask.trans invariant.maskRegister, running⟩
  · simpa only [heap] using invariant.retained
  · simpa only [heap] using invariant.packet
  · simpa only [heap] using invariant.allocation
  · simpa only [heap] using invariant.originCell

theorem source_arity_stage (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (initial state : State width 8) (H base rankBase origin entry done : Nat)
    (beforeWords : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin beforeWords)
    (physical : ∀ phase : Fin 17, resident[entry + phase.val]? =
      (typedArityCopyCode width raw.nodes.size base entry done)[phase.val]?)
    (position : state.pc = word width entry) (codeFits : entry + 17 < 2 ^ width)
    (room : state.heap.size + 2 * numbering.order.length < 2 ^ width)
    (cursorFits : Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base +
      numbering.order.length < 2 ^ width)
    (nodesFit : raw.nodes.size < 2 ^ width)
    (countHeld : state.reg 0 = word width numbering.order.length)
    (cursorHeld : state.reg 1 = word width
      (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)) :
    ∃ final peak, Execution resident state final (17 * numbering.order.length + 1) peak ∧
      peak ≤ state.liveWords + 2 * numbering.order.length ∧
      final.pc = word width done ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase origin
        (beforeWords ++ copiedArityWords (numberedDirectoryRows raw valid numbering)) := by
  let rows := numberedDirectoryRows raw valid numbering
  have rowLength : rows.length = numbering.order.length := by
    simp only [rows, numberedDirectoryRows, List.length_map, List.length_finRange]
  have stored := original_numbered_directory_stored raw valid numbering state.heap H
    (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)
    invariant.retained.image invariant.retained.queue
  obtain ⟨final, peak, trace, space, heap, stack, output, pc, running,
    count, cursor, ranks, zero, mask⟩ := arity_loop_execution resident raw.nodes.size base entry done H physical codeFits rows _ state position invariant.running
      (by simpa only [rowLength] using room)
      (by simpa only [rowLength] using cursorFits)
      (by rw [rowLength, numbering.length_eq_nodeCount]; exact nodesFit)
      (by simpa only [rowLength] using countHeld) cursorHeld
      invariant.zeroRegister invariant.maskRegister invariant.retained.rawBase stored
  dsimp only [rows] at heap
  refine ⟨final, peak, by simpa only [rowLength] using trace,
    by simpa only [rowLength] using space, pc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, stack.trans invariant.stack, output.trans invariant.output,
    ranks.trans invariant.rankRegister, zero.trans invariant.zeroRegister,
    mask.trans invariant.maskRegister, running⟩
  · rw [heap]
    exact retained_copy_append raw valid numbering state.heap H base rankBase _ invariant.retained
  · rw [heap]
    exact copied_packet_append state.heap origin beforeWords _ invariant.allocation invariant.packet
  · rw [heap]
    simp only [Array.size_append, List.size_toArray, List.length_append, invariant.allocation]
    omega
  · rw [heap]
    exact appended_cell_frame state.heap _ _ _ invariant.originCell

theorem source_child_stage (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (initial state : State width 8) (H base rankBase origin entry done : Nat)
    (beforeWords : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin beforeWords)
    (setupPhysical : ∀ phase : Fin 16, resident[entry + phase.val]? =
      (typedSliceSetupCode width raw.nodes.size base done (entry + 16) 0)[phase.val]?)
    (streamPhysical : ∀ phase : Fin 9, resident[entry + 16 + phase.val]? =
      (mappedOccurrenceCopyCode width (entry + 16) (entry + 25))[phase.val]?)
    (backPhysical : ∀ phase : Fin 4, resident[entry + 25 + phase.val]? =
      (typedRowsBackedgeCode width entry)[phase.val]?)
    (position : state.pc = word width entry) (codeFits : entry + 29 < 2 ^ width)
    (room : state.heap.size + childOccurrenceCount (numberedChildRows (width := width) raw valid numbering) < 2 ^ width)
    (cursorFits : Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + numbering.order.length < 2 ^ width)
    (nodesFit : raw.nodes.size < 2 ^ width)
    (sourceFits : ∀ row ∈ numberedChildRows (width := width) raw valid numbering,
      H + row.relative + row.occurrences.length < 2 ^ width)
    (countHeld : state.reg 0 = word width numbering.order.length)
    (cursorHeld : state.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)) :
    ∃ final peak, Execution resident state final
      (21 * numbering.order.length + 9 * childOccurrenceCount (numberedChildRows (width := width) raw valid numbering) + 1) peak ∧
      peak ≤ state.liveWords + childOccurrenceCount (numberedChildRows (width := width) raw valid numbering) ∧
      final.pc = word width done ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase origin
        (beforeWords ++ copiedChildWords (numberedChildRows (width := width) raw valid numbering)) := by
  let rows := numberedChildRows (width := width) raw valid numbering
  have rowLength : rows.length = numbering.order.length := by
    simp only [rows, numberedChildRows, List.length_map, List.length_finRange]
  have stored := original_numbered_children_stored raw valid numbering state.heap H
    (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base) rankBase
    invariant.retained.image nodesFit invariant.retained.queue invariant.retained.ranks
  obtain ⟨final, peak, trace, space, heap, stack, output, pc, running, count, cursor, ranks, zero, mask⟩ :=
    child_rows_execution resident raw.nodes.size base entry done rankBase H setupPhysical streamPhysical
      backPhysical codeFits rows _ state position invariant.running room
      (by simpa only [rowLength] using cursorFits)
      (by rw [rowLength, numbering.length_eq_nodeCount]; exact nodesFit) sourceFits
      (by simpa only [rowLength] using countHeld) cursorHeld invariant.rankRegister invariant.zeroRegister
      invariant.maskRegister invariant.retained.rawBase stored
  dsimp only [rows] at heap
  refine ⟨final, peak, by simpa only [rowLength] using trace, space, pc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, stack.trans invariant.stack, output.trans invariant.output,
    ranks.trans invariant.rankRegister, zero.trans invariant.zeroRegister, mask.trans invariant.maskRegister, running⟩
  · rw [heap]
    exact retained_copy_append raw valid numbering state.heap H base rankBase _ invariant.retained
  · rw [heap]
    exact copied_packet_append state.heap origin beforeWords _ invariant.allocation invariant.packet
  · rw [heap]
    simp only [Array.size_append, List.size_toArray, List.length_append, invariant.allocation]
    omega
  · rw [heap]
    exact appended_cell_frame state.heap _ _ _ invariant.originCell

theorem source_guard_stage (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (initial state : State width 8) (H base rankBase origin entry done : Nat)
    (beforeWords : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin beforeWords)
    (setupPhysical : ∀ phase : Fin 16, resident[entry + phase.val]? =
      (typedSliceSetupCode width raw.nodes.size base done (entry + 16) 1)[phase.val]?)
    (streamPhysical : ∀ phase : Fin 7, resident[entry + 16 + phase.val]? =
      (unchangedOccurrenceCopyCode width (entry + 16) (entry + 23))[phase.val]?)
    (backPhysical : ∀ phase : Fin 4, resident[entry + 23 + phase.val]? =
      (typedRowsBackedgeCode width entry)[phase.val]?)
    (position : state.pc = word width entry) (codeFits : entry + 27 < 2 ^ width)
    (room : state.heap.size + guardOccurrenceCount (numberedGuardRows (width := width) raw valid numbering) < 2 ^ width)
    (cursorFits : Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + numbering.order.length < 2 ^ width)
    (nodesFit : raw.nodes.size < 2 ^ width)
    (sourceFits : ∀ row ∈ numberedGuardRows (width := width) raw valid numbering,
      H + row.relative + row.values.length < 2 ^ width)
    (countHeld : state.reg 0 = word width numbering.order.length)
    (cursorHeld : state.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)) :
    ∃ final peak, Execution resident state final
      (21 * numbering.order.length + 7 * guardOccurrenceCount (numberedGuardRows (width := width) raw valid numbering) + 1) peak ∧
      peak ≤ state.liveWords + guardOccurrenceCount (numberedGuardRows (width := width) raw valid numbering) ∧
      final.pc = word width done ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase origin
        (beforeWords ++ copiedGuardWords (numberedGuardRows (width := width) raw valid numbering)) := by
  let rows := numberedGuardRows (width := width) raw valid numbering
  have rowLength : rows.length = numbering.order.length := by
    simp only [rows, numberedGuardRows, List.length_map, List.length_finRange]
  have stored := original_numbered_guards_stored raw valid numbering state.heap H
    (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base) rankBase
    invariant.retained.image invariant.retained.queue
  obtain ⟨final, peak, trace, space, heap, stack, output, pc, running, count, cursor, ranks, zero, mask⟩ :=
    guard_rows_execution resident raw.nodes.size base entry done rankBase H setupPhysical streamPhysical
      backPhysical codeFits rows _ state position invariant.running room
      (by simpa only [rowLength] using cursorFits)
      (by rw [rowLength, numbering.length_eq_nodeCount]; exact nodesFit) sourceFits
      (by simpa only [rowLength] using countHeld) cursorHeld invariant.rankRegister invariant.zeroRegister
      invariant.maskRegister invariant.retained.rawBase stored
  dsimp only [rows] at heap
  refine ⟨final, peak, by simpa only [rowLength] using trace, space, pc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, stack.trans invariant.stack, output.trans invariant.output,
    ranks.trans invariant.rankRegister, zero.trans invariant.zeroRegister, mask.trans invariant.maskRegister, running⟩
  · rw [heap]
    exact retained_copy_append raw valid numbering state.heap H base rankBase _ invariant.retained
  · rw [heap]
    exact copied_packet_append state.heap origin beforeWords _ invariant.allocation invariant.packet
  · rw [heap]
    simp only [Array.size_append, List.size_toArray, List.length_append, invariant.allocation]
    omega
  · rw [heap]
    exact appended_cell_frame state.heap _ _ _ invariant.originCell

theorem source_root_stage (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering)
    (initial state : State width 8) (H base rankBase origin entry done : Nat)
    (beforeWords : List (Word width))
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase origin beforeWords)
    (setupAt : ∀ phase : Fin 11, resident[entry + phase.val]? =
      (typedRootSetupCode width raw.nodes.size base (entry + 11))[phase.val]?)
    (streamAt : ∀ phase : Fin 9, resident[entry + 11 + phase.val]? =
      (mappedOccurrenceCopyCode width (entry + 11) done)[phase.val]?)
    (position : state.pc = word width entry) (codeFits : entry + 20 < 2 ^ width)
    (room : state.heap.size + raw.roots.length < 2 ^ width)
    (sourceFits : H + originalRootStart raw + raw.roots.length < 2 ^ width)
    (nodesFit : raw.nodes.size < 2 ^ width) :
    ∃ final peak, Execution resident state final (9 * raw.roots.length + 12) peak ∧
      peak ≤ state.liveWords + raw.roots.length ∧ final.pc = word width done ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase origin
        (beforeWords ++ (numbering.toDAG.roots.map Fin.val).map (word width)) := by
  obtain ⟨final, peak, trace, space, heap, stack, output, pc, running, remaining, held⟩ :=
    original_roots_execution raw valid numbering resident raw.nodes.size base entry done H rankBase
      rfl state setupAt streamAt position invariant.running codeFits room sourceFits nodesFit
      invariant.rankRegister invariant.zeroRegister invariant.maskRegister invariant.retained.rawBase
      invariant.retained.image invariant.retained.ranks
  refine ⟨final, peak, trace, space, pc, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, stack.trans invariant.stack, output.trans invariant.output,
    (held 4 (by decide) (by decide) (by decide)).trans invariant.rankRegister,
    (held 6 (by decide) (by decide) (by decide)).trans invariant.zeroRegister,
    (held 7 (by decide) (by decide) (by decide)).trans invariant.maskRegister, running⟩
  · rw [heap]
    exact retained_copy_append raw valid numbering state.heap H base rankBase _ invariant.retained
  · rw [heap]
    exact copied_packet_append state.heap origin beforeWords _ invariant.allocation invariant.packet
  · rw [heap]
    simp only [Array.size_append, List.size_toArray, List.length_append, invariant.allocation]
    omega
  · rw [heap]
    exact appended_cell_frame state.heap _ _ _ invariant.originCell


structure OrderedCopyParts (resident : Program width 8) (nodes children base entry done : Nat) : Prop where
  globalPart : ∀ phase : Fin 31, resident[(entry + 0) + phase.val]? =
    (typedGlobalCopyCode width nodes base (entry + 31))[phase.val]?
  header : ∀ phase : Fin 31, resident[(entry + 31) + phase.val]? =
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62))[phase.val]?
  directorySetup : ∀ phase : Fin 11, resident[(entry + 62) + phase.val]? =
    (typedDirectorySetupCode width nodes children base (entry + 73))[phase.val]?
  directory : ∀ phase : Fin 32, resident[(entry + 73) + phase.val]? =
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105))[phase.val]?
  restartArity : ∀ phase : Fin 3, resident[(entry + 105) + phase.val]? =
    (typedCopyRestartCode width nodes base (entry + 108))[phase.val]?
  arity : ∀ phase : Fin 17, resident[(entry + 108) + phase.val]? =
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125))[phase.val]?
  restartChild : ∀ phase : Fin 3, resident[(entry + 125) + phase.val]? =
    (typedCopyRestartCode width nodes base (entry + 128))[phase.val]?
  childSetup : ∀ phase : Fin 16, resident[(entry + 128) + phase.val]? =
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0)[phase.val]?
  childStream : ∀ phase : Fin 9, resident[(entry + 144) + phase.val]? =
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25))[phase.val]?
  childBack : ∀ phase : Fin 4, resident[(entry + 153) + phase.val]? =
    (typedRowsBackedgeCode width (entry + 128))[phase.val]?
  restartGuard : ∀ phase : Fin 3, resident[(entry + 157) + phase.val]? =
    (typedCopyRestartCode width nodes base (entry + 160))[phase.val]?
  guardSetup : ∀ phase : Fin 16, resident[(entry + 160) + phase.val]? =
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1)[phase.val]?
  guardStream : ∀ phase : Fin 7, resident[(entry + 176) + phase.val]? =
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23))[phase.val]?
  guardBack : ∀ phase : Fin 4, resident[(entry + 183) + phase.val]? =
    (typedRowsBackedgeCode width (entry + 160))[phase.val]?
  rootSetup : ∀ phase : Fin 11, resident[(entry + 187) + phase.val]? =
    (typedRootSetupCode width nodes base (entry + 198))[phase.val]?
  rootStream : ∀ phase : Fin 9, resident[(entry + 198) + phase.val]? =
    (mappedOccurrenceCopyCode width (entry + 198) done)[phase.val]?

theorem emptyCopyCode_size (width : Nat) : (#[] : Program width 8).size = 0 := rfl

theorem typedGlobalCopyCode_opaque_size (width nodes base headerEntry : Nat) :
    (typedGlobalCopyCode width nodes base headerEntry).size = 31 := by rfl

theorem typedHeaderCopyCode_opaque_size (width nodes base entry done : Nat) :
    (typedHeaderCopyCode width nodes base entry done).size = 31 := by rfl

theorem typedDirectorySetupCode_opaque_size (width nodes children base entry : Nat) :
    (typedDirectorySetupCode width nodes children base entry).size = 11 := by rfl

theorem typedDirectoryCopyCode_opaque_size (width nodes base entry done : Nat) :
    (typedDirectoryCopyCode width nodes base entry done).size = 32 := by rfl

theorem typedCopyRestartCode_opaque_size (width nodes base entry : Nat) :
    (typedCopyRestartCode width nodes base entry).size = 3 := by rfl

theorem typedArityCopyCode_opaque_size (width nodes base entry done : Nat) :
    (typedArityCopyCode width nodes base entry done).size = 17 := by rfl

theorem typedSliceSetupCode_opaque_size (width nodes base done stream offset : Nat) :
    (typedSliceSetupCode width nodes base done stream offset).size = 16 := by rfl

theorem mappedOccurrenceCopyCode_opaque_size (width entry done : Nat) :
    (mappedOccurrenceCopyCode width entry done).size = 9 := by rfl

theorem typedRowsBackedgeCode_opaque_size (width entry : Nat) :
    (typedRowsBackedgeCode width entry).size = 4 := by rfl

theorem unchangedOccurrenceCopyCode_opaque_size (width entry done : Nat) :
    (unchangedOccurrenceCopyCode width entry done).size = 7 := by rfl

theorem typedRootSetupCode_opaque_size (width nodes base rootEntry : Nat) :
    (typedRootSetupCode width nodes base rootEntry).size = 11 := by rfl

attribute [local irreducible] typedGlobalCopyCode typedHeaderCopyCode typedDirectorySetupCode typedDirectoryCopyCode typedCopyRestartCode typedArityCopyCode typedSliceSetupCode mappedOccurrenceCopyCode typedRowsBackedgeCode unchangedOccurrenceCopyCode typedRootSetupCode

theorem ordered_copy_part_globalPart (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 31, resident[(entry + 0) + phase.val]? =
    (typedGlobalCopyCode width nodes base (entry + 31))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := #[]
  let fragment : Program width 8 := typedGlobalCopyCode width nodes base (entry + 31)
  let after : Program width 8 := (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 0 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 31 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 0 31
    layout beforeSize sectionSize actual

theorem ordered_copy_part_header (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 31, resident[(entry + 31) + phase.val]? =
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31))
  let fragment : Program width 8 := typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)
  let after : Program width 8 := (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 31 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 31 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 31 31
    layout beforeSize sectionSize actual

theorem ordered_copy_part_directorySetup (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 11, resident[(entry + 62) + phase.val]? =
    (typedDirectorySetupCode width nodes children base (entry + 73))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62))
  let fragment : Program width 8 := typedDirectorySetupCode width nodes children base (entry + 73)
  let after : Program width 8 := (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 62 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 11 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 62 11
    layout beforeSize sectionSize actual

theorem ordered_copy_part_directory (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 32, resident[(entry + 73) + phase.val]? =
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73))
  let fragment : Program width 8 := typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)
  let after : Program width 8 := (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 73 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 32 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 73 32
    layout beforeSize sectionSize actual

theorem ordered_copy_part_restartArity (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 3, resident[(entry + 105) + phase.val]? =
    (typedCopyRestartCode width nodes base (entry + 108))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105))
  let fragment : Program width 8 := typedCopyRestartCode width nodes base (entry + 108)
  let after : Program width 8 := (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 105 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 3 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 105 3
    layout beforeSize sectionSize actual

theorem ordered_copy_part_arity (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 17, resident[(entry + 108) + phase.val]? =
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108))
  let fragment : Program width 8 := typedArityCopyCode width nodes base (entry + 108) (entry + 125)
  let after : Program width 8 := (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 108 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 17 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 108 17
    layout beforeSize sectionSize actual

theorem ordered_copy_part_restartChild (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 3, resident[(entry + 125) + phase.val]? =
    (typedCopyRestartCode width nodes base (entry + 128))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125))
  let fragment : Program width 8 := typedCopyRestartCode width nodes base (entry + 128)
  let after : Program width 8 := (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 125 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 3 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 125 3
    layout beforeSize sectionSize actual

theorem ordered_copy_part_childSetup (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 16, resident[(entry + 128) + phase.val]? =
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0)[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128))
  let fragment : Program width 8 := typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0
  let after : Program width 8 := (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 128 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 16 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 128 16
    layout beforeSize sectionSize actual

theorem ordered_copy_part_childStream (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 9, resident[(entry + 144) + phase.val]? =
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0)
  let fragment : Program width 8 := mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)
  let after : Program width 8 := (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 144 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 9 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 144 9
    layout beforeSize sectionSize actual

theorem ordered_copy_part_childBack (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 4, resident[(entry + 153) + phase.val]? =
    (typedRowsBackedgeCode width (entry + 128))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25))
  let fragment : Program width 8 := typedRowsBackedgeCode width (entry + 128)
  let after : Program width 8 := (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 153 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 4 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 153 4
    layout beforeSize sectionSize actual

theorem ordered_copy_part_restartGuard (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 3, resident[(entry + 157) + phase.val]? =
    (typedCopyRestartCode width nodes base (entry + 160))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128))
  let fragment : Program width 8 := typedCopyRestartCode width nodes base (entry + 160)
  let after : Program width 8 := (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 157 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 3 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 157 3
    layout beforeSize sectionSize actual

theorem ordered_copy_part_guardSetup (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 16, resident[(entry + 160) + phase.val]? =
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1)[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160))
  let fragment : Program width 8 := typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1
  let after : Program width 8 := (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 160 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 16 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 160 16
    layout beforeSize sectionSize actual

theorem ordered_copy_part_guardStream (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 7, resident[(entry + 176) + phase.val]? =
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1)
  let fragment : Program width 8 := unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)
  let after : Program width 8 := (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 176 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 7 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 176 7
    layout beforeSize sectionSize actual

theorem ordered_copy_part_guardBack (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 4, resident[(entry + 183) + phase.val]? =
    (typedRowsBackedgeCode width (entry + 160))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23))
  let fragment : Program width 8 := typedRowsBackedgeCode width (entry + 160)
  let after : Program width 8 := (typedRootSetupCode width nodes base (entry + 198)) ++
    (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 183 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 4 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 183 4
    layout beforeSize sectionSize actual

theorem ordered_copy_part_rootSetup (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 11, resident[(entry + 187) + phase.val]? =
    (typedRootSetupCode width nodes base (entry + 198))[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160))
  let fragment : Program width 8 := typedRootSetupCode width nodes base (entry + 198)
  let after : Program width 8 := (mappedOccurrenceCopyCode width (entry + 198) done)
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 187 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 11 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 187 11
    layout beforeSize sectionSize actual

theorem ordered_copy_part_rootStream (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    ∀ phase : Fin 9, resident[(entry + 198) + phase.val]? =
    (mappedOccurrenceCopyCode width (entry + 198) done)[phase.val]? := by
  let whole := orderedTypedCopyCode width nodes children base entry done
  have wholeSize : whole.size = 207 := orderedTypedCopyCode_size width nodes children base entry done
  have actual : ∀ phase : Fin whole.size, resident[entry + phase.val]? = whole[phase.val]? := by
    intro phase
    exact physical ⟨phase.val, by rw [← wholeSize]; exact phase.isLt⟩
  let before : Program width 8 := (typedGlobalCopyCode width nodes base (entry + 31)) ++
    (typedHeaderCopyCode width nodes base (entry + 31) (entry + 62)) ++
    (typedDirectorySetupCode width nodes children base (entry + 73)) ++
    (typedDirectoryCopyCode width nodes base (entry + 73) (entry + 105)) ++
    (typedCopyRestartCode width nodes base (entry + 108)) ++
    (typedArityCopyCode width nodes base (entry + 108) (entry + 125)) ++
    (typedCopyRestartCode width nodes base (entry + 128)) ++
    (typedSliceSetupCode width nodes base (entry + 157) ((entry + 128) + 16) 0) ++
    (mappedOccurrenceCopyCode width ((entry + 128) + 16) ((entry + 128) + 25)) ++
    (typedRowsBackedgeCode width (entry + 128)) ++
    (typedCopyRestartCode width nodes base (entry + 160)) ++
    (typedSliceSetupCode width nodes base (entry + 187) ((entry + 160) + 16) 1) ++
    (unchangedOccurrenceCopyCode width ((entry + 160) + 16) ((entry + 160) + 23)) ++
    (typedRowsBackedgeCode width (entry + 160)) ++
    (typedRootSetupCode width nodes base (entry + 198))
  let fragment : Program width 8 := mappedOccurrenceCopyCode width (entry + 198) done
  let after : Program width 8 := #[]
  have layout : whole = (before ++ fragment) ++ after := by
    unfold whole orderedTypedCopyCode typedChildrenCopyCode typedGuardsCopyCode before fragment after
    simp only [Array.append_assoc, Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 198 := by
    dsimp only [before]
    simp only [Array.size_append, typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size, emptyCopyCode_size]
  have sectionSize : fragment.size = 9 := by
    dsimp only [fragment]
    simp only [typedGlobalCopyCode_opaque_size, typedHeaderCopyCode_opaque_size, typedDirectorySetupCode_opaque_size, typedDirectoryCopyCode_opaque_size, typedCopyRestartCode_opaque_size, typedArityCopyCode_opaque_size, typedSliceSetupCode_opaque_size, mappedOccurrenceCopyCode_opaque_size, typedRowsBackedgeCode_opaque_size, unchangedOccurrenceCopyCode_opaque_size, typedRootSetupCode_opaque_size]
  exact extract_copy_section resident whole before fragment after entry 198 9
    layout beforeSize sectionSize actual



theorem ordered_copy_parts (resident : Program width 8) (nodes children base entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry done)[phase.val]?) :
    OrderedCopyParts resident nodes children base entry done := by
  exact ⟨ordered_copy_part_globalPart resident nodes children base entry done physical,
    ordered_copy_part_header resident nodes children base entry done physical,
    ordered_copy_part_directorySetup resident nodes children base entry done physical,
    ordered_copy_part_directory resident nodes children base entry done physical,
    ordered_copy_part_restartArity resident nodes children base entry done physical,
    ordered_copy_part_arity resident nodes children base entry done physical,
    ordered_copy_part_restartChild resident nodes children base entry done physical,
    ordered_copy_part_childSetup resident nodes children base entry done physical,
    ordered_copy_part_childStream resident nodes children base entry done physical,
    ordered_copy_part_childBack resident nodes children base entry done physical,
    ordered_copy_part_restartGuard resident nodes children base entry done physical,
    ordered_copy_part_guardSetup resident nodes children base entry done physical,
    ordered_copy_part_guardStream resident nodes children base entry done physical,
    ordered_copy_part_guardBack resident nodes children base entry done physical,
    ordered_copy_part_rootSetup resident nodes children base entry done physical,
    ordered_copy_part_rootStream resident nodes children base entry done physical⟩

theorem original_count_vectors (raw : RawDAG) (valid : raw.WellFormed channels) :
    (originalRows raw).map (fun row => row.children.length) =
      List.ofFn (fun old : Fin (raw.toUnordered valid).nodeCount =>
        ((raw.toUnordered valid).node old).children.length) ∧
    (originalRows raw).map (fun row => row.guards.length) =
      List.ofFn (fun old : Fin (raw.toUnordered valid).nodeCount =>
        ((raw.toUnordered valid).node old).guardLabels.length) := by
  constructor
  · apply List.ext_getElem
    · simp only [List.length_map, original_rows_length, List.length_ofFn] <;> rfl
    · intro position left right
      have bounded : position < (raw.toUnordered valid).nodeCount := by
        simpa only [List.length_ofFn] using right
      let old : Fin (raw.toUnordered valid).nodeCount := ⟨position, bounded⟩
      have counts := erased_typed_row_counts ((raw.toUnordered valid).node old)
      rw [← original_selected_row raw valid old] at counts
      simpa only [List.getElem_map, List.getElem_ofFn, old] using counts.1
  · apply List.ext_getElem
    · simp only [List.length_map, original_rows_length, List.length_ofFn] <;> rfl
    · intro position left right
      have bounded : position < (raw.toUnordered valid).nodeCount := by
        simpa only [List.length_ofFn] using right
      let old : Fin (raw.toUnordered valid).nodeCount := ⟨position, bounded⟩
      have counts := erased_typed_row_counts ((raw.toUnordered valid).node old)
      rw [← original_selected_row raw valid old] at counts
      simpa only [List.getElem_map, List.getElem_ofFn, old] using counts.2

theorem numbered_directory_totals (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    ((numberedDirectoryRows raw valid numbering).map DirectorySourceRow.children).sum =
      (rowChildren (originalRows raw)).length ∧
    ((numberedDirectoryRows raw valid numbering).map DirectorySourceRow.guards).sum =
      (rowGuards (originalRows raw)).length := by
  obtain ⟨originalChildren, originalGuards⟩ := original_count_vectors raw valid
  constructor
  · have sourceLength : (rowChildren (originalRows raw)).length =
        ((originalRows raw).map (fun row => row.children.length)).sum := by
      simp only [rowChildren, List.length_flatMap]
    rw [sourceLength, originalChildren, List.sum_ofFn]
    simp only [numberedDirectoryRows, List.map_map, Function.comp_def, numberedDirectoryRow]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    simpa only [← List.ofFn_eq_map, List.sum_ofFn] using RawNumberingCounts.numbering_sum
      (raw.toUnordered valid) numbering (fun old => ((raw.toUnordered valid).node old).children.length)
  · have sourceLength : (rowGuards (originalRows raw)).length =
        ((originalRows raw).map (fun row => row.guards.length)).sum := by
      simp only [rowGuards, List.length_flatMap]
    rw [sourceLength, originalGuards, List.sum_ofFn]
    simp only [numberedDirectoryRows, List.map_map, Function.comp_def, numberedDirectoryRow]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    simpa only [← List.ofFn_eq_map, List.sum_ofFn] using RawNumberingCounts.numbering_sum
      (raw.toUnordered valid) numbering (fun old => ((raw.toUnordered valid).node old).guardLabels.length)

theorem child_count_sum (rows : List (ChildSourceRow width)) :
    childOccurrenceCount rows = (rows.map (fun row => row.occurrences.length)).sum := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [childOccurrenceCount, List.map_cons, List.sum_cons, ih]

theorem guard_count_sum (rows : List (GuardSourceRow width)) :
    guardOccurrenceCount rows = (rows.map (fun row => row.values.length)).sum := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [guardOccurrenceCount, List.map_cons, List.sum_cons, ih]

theorem numbered_stream_totals (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    childOccurrenceCount (numberedChildRows (width := width) raw valid numbering) =
      (rowChildren (originalRows raw)).length ∧
    guardOccurrenceCount (numberedGuardRows (width := width) raw valid numbering) =
      (rowGuards (originalRows raw)).length := by
  constructor
  · simpa only [child_count_sum, numberedChildRows, numberedChildRow,
      numberedDirectoryRows, numberedDirectoryRow, List.map_map, Function.comp_def,
      List.length_map] using (numbered_directory_totals raw valid numbering).1
  · simpa only [guard_count_sum, numberedGuardRows, numberedGuardRow,
      numberedDirectoryRows, numberedDirectoryRow, List.map_map, Function.comp_def,
      List.length_map] using (numbered_directory_totals raw valid numbering).2

theorem numbered_packet_length (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    (numberedPacketWords (width := width) raw valid numbering).length =
      5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length := by
  obtain ⟨children, guards⟩ := numbered_stream_totals (width := width) raw valid numbering
  have roots : numbering.toDAG.roots.length = raw.roots.length := by
    simp only [UnorderedDAG.Numbering.toDAG, RawDAG.toUnordered, List.length_map,
      List.length_attach]
  have originalCount : (raw.toUnordered valid).nodeCount = raw.nodes.size := rfl
  simp only [numberedPacketWords, numberedGlobalWords, List.length_append,
    List.length_cons, List.length_nil, copied_header_words_length, directory_cursor_words_length,
    copied_arity_words_length, copied_child_words_length, copied_guard_words_length,
    numberedHeaderRows, numberedDirectoryRows, List.length_map, List.length_finRange,
    children, guards, roots, numbering.length_eq_nodeCount, originalCount]
  omega


theorem row_prefix_incidence_bound (field : Row → List Nat) (rows : List Row)
    (index : Nat) (valid : index < rows.length) :
    ((rows.take index).flatMap field).length + (field rows[index]).length ≤
      (rows.flatMap field).length := by
  have split : rows.flatMap field =
      (rows.take (index + 1)).flatMap field ++ (rows.drop (index + 1)).flatMap field := by
    rw [← List.flatMap_append, List.take_append_drop]
  have sizes := congrArg List.length split
  rw [List.take_succ_eq_append_getElem valid] at sizes
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.length_append] at sizes
  omega

theorem numbered_child_source_room (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (heap : Array (Word width)) (H : Nat)
    (image : OriginalImageStored heap H channels raw) (room : heap.size < 2 ^ width) :
    ∀ row ∈ numberedChildRows (width := width) raw valid numbering,
      H + row.relative + row.occurrences.length < 2 ^ width := by
  intro row member
  change row ∈ (List.finRange numbering.order.length).map
    (numberedChildRow (width := width) raw valid numbering) at member
  obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
  let old := numbering.oldIndex index
  have oldBound : old.val < (originalRows raw).length := by
    rw [original_rows_length]
    exact old.isLt
  have counts := erased_typed_row_counts ((raw.toUnordered valid).node old)
  rw [← original_selected_row raw valid old] at counts
  have visitedBound := row_prefix_incidence_bound Row.children (originalRows raw) old.val oldBound
  have sourceEnd := original_packet_stored_end heap H channels raw image
  rw [original_packet_size] at sourceEnd
  simp only [numberedChildRow, List.length_map]
  change H + (9 + 6 * raw.nodes.size +
      (rowChildren ((originalRows raw).take old.val)).length) +
      ((raw.toUnordered valid).node old).children.length < 2 ^ width
  rw [← counts.1]
  change (rowChildren ((originalRows raw).take old.val)).length +
    ((originalRows raw)[old.val]).children.length ≤ (rowChildren (originalRows raw)).length at visitedBound
  omega

theorem numbered_guard_source_room (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (heap : Array (Word width)) (H : Nat)
    (image : OriginalImageStored heap H channels raw) (room : heap.size < 2 ^ width) :
    ∀ row ∈ numberedGuardRows (width := width) raw valid numbering,
      H + row.relative + row.values.length < 2 ^ width := by
  intro row member
  change row ∈ (List.finRange numbering.order.length).map
    (numberedGuardRow (width := width) raw valid numbering) at member
  obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
  let old := numbering.oldIndex index
  have oldBound : old.val < (originalRows raw).length := by
    rw [original_rows_length]
    exact old.isLt
  have counts := erased_typed_row_counts ((raw.toUnordered valid).node old)
  rw [← original_selected_row raw valid old] at counts
  have visitedBound := row_prefix_incidence_bound Row.guards (originalRows raw) old.val oldBound
  have sourceEnd := original_packet_stored_end heap H channels raw image
  rw [original_packet_size] at sourceEnd
  simp only [numberedGuardRow, List.length_map]
  change H + (9 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
      (rowGuards ((originalRows raw).take old.val)).length) +
      ((raw.toUnordered valid).node old).guardLabels.length < 2 ^ width
  rw [← counts.2]
  change (rowGuards ((originalRows raw).take old.val)).length +
    ((originalRows raw)[old.val]).guards.length ≤ (rowGuards (originalRows raw)).length at visitedBound
  omega


def numberedFixedWords (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) : List (Word width) :=
  numberedGlobalWords (width := width) raw channels ++
  copiedHeaderWords (numberedHeaderRows raw valid numbering) ++
  directoryCursorWords (width := width) (5 + 6 * raw.nodes.size)
    (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length)
    (numberedDirectoryRows raw valid numbering) ++
  copiedArityWords (width := width) (numberedDirectoryRows raw valid numbering)

theorem ordered_source_copy_fixed_execution (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (initial : State width 8)
    (H base rankBase entry done : Nat)
    (facts : RetainedCopyFacts raw valid numbering initial.heap H base rankBase)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width raw.nodes.size
        (rowChildren (originalRows raw)).length base entry done)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 207 < 2 ^ width)
    (capacity : channels + initial.heap.size +
      (numberedPacketWords (width := width) raw valid numbering).length < 2 ^ width)
    (allocation : initial.heap.size = rankBase + raw.nodes.size)
    (rankHeld : initial.reg 4 = word width rankBase)
    (scratchBefore : base + 4 * raw.nodes.size + 4 ≤ H)
    (rankAfter : H ≤ rankBase) :
    ∃ final ticks peak, Execution resident initial final ticks peak ∧
      ticks ≤ 77 * raw.nodes.size + 51 ∧ peak ≤ initial.liveWords + 5 + 6 * raw.nodes.size ∧
      final.pc = word width (entry + 128) ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase initial.heap.size
        (numberedFixedWords (width := width) raw valid numbering) ∧
      final.reg 0 = word width raw.nodes.size ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base) := by
  let V := raw.nodes.size
  let E := (rowChildren (originalRows raw)).length
  let U := (rowGuards (originalRows raw)).length
  let R := raw.roots.length
  let S := initial.heap.size
  let M := 2 ^ width
  have orderLength : numbering.order.length = V := numbering.length_eq_nodeCount
  have packetLength : (numberedPacketWords (width := width) raw valid numbering).length =
      5 + 6 * V + E + U + R := numbered_packet_length raw valid numbering
  have cap : channels + S + (5 + 6 * V + E + U + R) < M := by
    simpa only [packetLength] using capacity
  have channelsFit : channels < M := by omega
  have nodesFit : V < M := by omega
  have originAfter : H ≤ S := by dsimp only [S]; omega
  have scratchBelow : Controller.Horn.WorklistBucketReady.tailSlot (n := V) base < H := by
    simp only [Controller.Horn.WorklistBucketReady.tailSlot]
    dsimp only [V] at scratchBefore ⊢
    omega
  have nextBelow : Controller.Horn.WorklistBucketReady.nextSlot (n := V) base < H := by
    simp only [Controller.Horn.WorklistBucketReady.nextSlot]
    dsimp only [V] at scratchBefore ⊢
    omega
  have queueFits : Controller.Horn.WorklistMark.queueStart (n := V) base + numbering.order.length < M := by
    simp only [Controller.Horn.WorklistMark.queueStart, orderLength]
    dsimp only [V, S, M] at cap scratchBefore allocation rankAfter ⊢
    omega
  have parts := ordered_copy_parts resident V E base entry done physical
  obtain ⟨childTotal, guardTotal⟩ := numbered_directory_totals raw valid numbering
  obtain ⟨childCount, guardCount⟩ := numbered_stream_totals (width := width) raw valid numbering
  let g := numberedGlobalWords (width := width) raw channels
  let h := copiedHeaderWords (numberedHeaderRows (width := width) raw valid numbering)
  let d := directoryCursorWords (width := width) (5 + 6 * V) (5 + 6 * V + E)
    (numberedDirectoryRows raw valid numbering)
  let a := copiedArityWords (width := width) (numberedDirectoryRows raw valid numbering)
  let c := copiedChildWords (numberedChildRows (width := width) raw valid numbering)
  let u := copiedGuardWords (numberedGuardRows (width := width) raw valid numbering)
  let r := (numbering.toDAG.roots.map Fin.val).map (word width)
  have gl : g.length = 5 := rfl
  have hl : h.length = 2 * V := by
    simp only [h, copied_header_words_length, numberedHeaderRows,
      List.length_map, List.length_finRange, orderLength]
  have dl : d.length = 2 * V := by
    simp only [d, directory_cursor_words_length, numberedDirectoryRows,
      List.length_map, List.length_finRange, orderLength]
  have al : a.length = 2 * V := by
    simp only [a, copied_arity_words_length, numberedDirectoryRows,
      List.length_map, List.length_finRange, orderLength]
  have cl : c.length = E := by
    simpa only [c, copied_child_words_length] using childCount
  have ul : u.length = U := by
    simpa only [u, copied_guard_words_length] using guardCount
  have rl : r.length = R := by
    simp only [r, UnorderedDAG.Numbering.toDAG, RawDAG.toUnordered,
      List.length_map, List.length_attach]
    rfl
  obtain ⟨s1, p1, t1, b1, pc1, i1, count1, cursor1⟩ :=
    source_global_stage resident raw valid numbering initial H base rankBase entry (entry + 31)
      facts (by simpa only [Nat.add_zero] using parts.globalPart) position running (by omega)
      (by omega) allocation rankHeld nextBelow rankAfter
  have l1 := ordered_copy_live raw valid numbering initial s1 H base rankBase S g i1 rfl
  have s1size : s1.heap.size = S + 5 := by
    have bound : s1.heap.size = S + (g).length := i1.allocation
    simp only [List.length_append, gl] at bound
    omega
  obtain ⟨s2, ht, p2, t2, bt2, b2, pc2, i2⟩ :=
    source_header_stage resident raw valid numbering initial s1 H base rankBase S
      (entry + 31) (entry + 62) g i1 parts.header pc1 (by omega)
      (by omega) queueFits channelsFit nodesFit (by simpa only [orderLength] using count1) cursor1
  have l2 := ordered_copy_live raw valid numbering initial s2 H base rankBase S (g ++ h) i2 rfl
  have s2size : s2.heap.size = S + 5 + 2 * V := by
    have bound : s2.heap.size = S + ((g ++ h)).length := i2.allocation
    simp only [List.length_append, gl, hl] at bound
    omega
  obtain ⟨s3, t3, pc3, i3, count3, cursor3, childCell3, guardCell3⟩ :=
    source_directory_setup resident raw valid numbering initial s2 H base rankBase S
      (entry + 62) (entry + 73) E (g ++ h) i2 parts.directorySetup pc2 (by omega)
      (by omega) scratchBelow rankAfter originAfter
  have l3 := ordered_copy_live raw valid numbering initial s3 H base rankBase S (g ++ h) i3 rfl
  have s3size : s3.heap.size = S + 5 + 2 * V := by
    have bound : s3.heap.size = S + ((g ++ h)).length := i3.allocation
    simp only [List.length_append, gl, hl] at bound
    omega
  obtain ⟨s4, p4, t4, b4, pc4, i4⟩ :=
    source_directory_stage resident raw valid numbering initial s3 H base rankBase S
      (entry + 73) (entry + 105) (5 + 6 * V) (5 + 6 * V + E)
      (g ++ h) i3 parts.directory pc3 (by omega) (by omega) queueFits nodesFit
      (by rw [childTotal]; omega) (by rw [guardTotal]; omega)
      (by simpa only [orderLength] using count3) cursor3 childCell3 guardCell3
      scratchBelow rankAfter originAfter
  have l4 := ordered_copy_live raw valid numbering initial s4 H base rankBase S ((g ++ h) ++ d) i4 rfl
  have s4size : s4.heap.size = S + 5 + 4 * V := by
    have bound : s4.heap.size = S + (((g ++ h) ++ d)).length := i4.allocation
    simp only [List.length_append, gl, hl, dl] at bound
    omega
  obtain ⟨s5, t5, pc5, i5, count5, cursor5⟩ :=
    source_copy_restart resident raw valid numbering initial s4 H base rankBase S
      (entry + 105) (entry + 108) ((g ++ h) ++ d) i4 parts.restartArity pc4 (by omega)
  have l5 := ordered_copy_live raw valid numbering initial s5 H base rankBase S ((g ++ h) ++ d) i5 rfl
  have s5size : s5.heap.size = S + 5 + 4 * V := by
    have bound : s5.heap.size = S + (((g ++ h) ++ d)).length := i5.allocation
    simp only [List.length_append, gl, hl, dl] at bound
    omega
  obtain ⟨s6, p6, t6, b6, pc6, i6⟩ :=
    source_arity_stage resident raw valid numbering initial s5 H base rankBase S
      (entry + 108) (entry + 125) ((g ++ h) ++ d) i5 parts.arity pc5 (by omega)
      (by omega) queueFits nodesFit (by simpa only [orderLength] using count5) cursor5
  have l6 := ordered_copy_live raw valid numbering initial s6 H base rankBase S (((g ++ h) ++ d) ++ a) i6 rfl
  have s6size : s6.heap.size = S + 5 + 6 * V := by
    have bound : s6.heap.size = S + ((((g ++ h) ++ d) ++ a)).length := i6.allocation
    simp only [List.length_append, gl, hl, dl, al] at bound
    omega
  obtain ⟨s7, t7, pc7, i7, count7, cursor7⟩ :=
    source_copy_restart resident raw valid numbering initial s6 H base rankBase S
      (entry + 125) (entry + 128) (((g ++ h) ++ d) ++ a) i6 parts.restartChild pc6 (by omega)
  have l7 := ordered_copy_live raw valid numbering initial s7 H base rankBase S (((g ++ h) ++ d) ++ a) i7 rfl
  have s7size : s7.heap.size = S + 5 + 6 * V := by
    have bound : s7.heap.size = S + ((((g ++ h) ++ d) ++ a)).length := i7.allocation
    simp only [List.length_append, gl, hl, dl, al] at bound
    omega
  have trace := (((((t1.append t2).append t3).append t4).append t5).append t6).append t7
  refine ⟨s7, _, _, trace, ?_, ?_, pc7, ?_, count7, cursor7⟩
  · simp only [orderLength]
    have headerTime : ht ≤ 28 * V + 1 := by simpa only [orderLength] using bt2
    dsimp only [V] at headerTime ⊢
    omega
  · simp only [max_le_iff]
    simp only [List.length_append, gl, hl, dl, al] at l1 l2 l3 l4 l5 l6
    have headerSpace : p2 ≤ s1.liveWords + 2 * V := by simpa only [orderLength] using b2
    have directorySpace : p4 ≤ s3.liveWords + 2 * V := by simpa only [orderLength] using b4
    have aritySpace : p6 ≤ s5.liveWords + 2 * V := by simpa only [orderLength] using b6
    dsimp only [V] at headerSpace directorySpace aritySpace l1 l2 l3 l4 l5 l6 ⊢
    omega
  · simpa only [numberedFixedWords, g, h, d, a, List.append_assoc] using i7


theorem ordered_source_copy_suffix_execution (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (initial state : State width 8)
    (H base rankBase entry done : Nat)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width raw.nodes.size
        (rowChildren (originalRows raw)).length base entry done)[phase.val]?)
    (codeFits : entry + 207 < 2 ^ width)
    (capacity : channels + initial.heap.size +
      (numberedPacketWords (width := width) raw valid numbering).length < 2 ^ width)
    (allocation : initial.heap.size = rankBase + raw.nodes.size)
    (scratchBefore : base + 4 * raw.nodes.size + 4 ≤ H)
    (rankAfter : H ≤ rankBase)
    (invariant : OrderedCopyInvariant raw valid numbering initial state H base rankBase initial.heap.size
      (numberedFixedWords (width := width) raw valid numbering))
    (position : state.pc = word width (entry + 128))
    (count : state.reg 0 = word width raw.nodes.size)
    (cursor : state.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base)) :
    ∃ final peak, Execution resident state final
      (42 * raw.nodes.size + 9 * (rowChildren (originalRows raw)).length +
        7 * (rowGuards (originalRows raw)).length + 9 * raw.roots.length + 17) peak ∧
      peak ≤ state.liveWords + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length ∧
      final.pc = word width done ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase initial.heap.size
        (numberedPacketWords (width := width) raw valid numbering) := by
  let V := raw.nodes.size
  let E := (rowChildren (originalRows raw)).length
  let U := (rowGuards (originalRows raw)).length
  let R := raw.roots.length
  let S := initial.heap.size
  let M := 2 ^ width
  have orderLength : numbering.order.length = V := numbering.length_eq_nodeCount
  have packetLength : (numberedPacketWords (width := width) raw valid numbering).length =
      5 + 6 * V + E + U + R := numbered_packet_length raw valid numbering
  have cap : channels + S + (5 + 6 * V + E + U + R) < M := by
    simpa only [packetLength] using capacity
  have channelsFit : channels < M := by omega
  have nodesFit : V < M := by omega
  have originAfter : H ≤ S := by dsimp only [S]; omega
  have scratchBelow : Controller.Horn.WorklistBucketReady.tailSlot (n := V) base < H := by
    simp only [Controller.Horn.WorklistBucketReady.tailSlot]
    dsimp only [V] at scratchBefore ⊢
    omega
  have nextBelow : Controller.Horn.WorklistBucketReady.nextSlot (n := V) base < H := by
    simp only [Controller.Horn.WorklistBucketReady.nextSlot]
    dsimp only [V] at scratchBefore ⊢
    omega
  have queueFits : Controller.Horn.WorklistMark.queueStart (n := V) base + numbering.order.length < M := by
    simp only [Controller.Horn.WorklistMark.queueStart, orderLength]
    dsimp only [V, S, M] at cap scratchBefore allocation rankAfter ⊢
    omega
  have parts := ordered_copy_parts resident V E base entry done physical
  obtain ⟨childTotal, guardTotal⟩ := numbered_directory_totals raw valid numbering
  obtain ⟨childCount, guardCount⟩ := numbered_stream_totals (width := width) raw valid numbering
  let g := numberedGlobalWords (width := width) raw channels
  let h := copiedHeaderWords (numberedHeaderRows (width := width) raw valid numbering)
  let d := directoryCursorWords (width := width) (5 + 6 * V) (5 + 6 * V + E)
    (numberedDirectoryRows raw valid numbering)
  let a := copiedArityWords (width := width) (numberedDirectoryRows raw valid numbering)
  let c := copiedChildWords (numberedChildRows (width := width) raw valid numbering)
  let u := copiedGuardWords (numberedGuardRows (width := width) raw valid numbering)
  let r := (numbering.toDAG.roots.map Fin.val).map (word width)
  have gl : g.length = 5 := rfl
  have hl : h.length = 2 * V := by
    simp only [h, copied_header_words_length, numberedHeaderRows,
      List.length_map, List.length_finRange, orderLength]
  have dl : d.length = 2 * V := by
    simp only [d, directory_cursor_words_length, numberedDirectoryRows,
      List.length_map, List.length_finRange, orderLength]
  have al : a.length = 2 * V := by
    simp only [a, copied_arity_words_length, numberedDirectoryRows,
      List.length_map, List.length_finRange, orderLength]
  have cl : c.length = E := by
    simpa only [c, copied_child_words_length] using childCount
  have ul : u.length = U := by
    simpa only [u, copied_guard_words_length] using guardCount
  have rl : r.length = R := by
    simp only [r, UnorderedDAG.Numbering.toDAG, RawDAG.toUnordered,
      List.length_map, List.length_attach]
    rfl
  let s7 := state
  have i7 : OrderedCopyInvariant raw valid numbering initial s7 H base rankBase S
      (((g ++ h) ++ d) ++ a) := by
    simpa only [numberedFixedWords, g, h, d, a, List.append_assoc] using invariant
  have pc7 : s7.pc = word width (entry + 128) := position
  have count7 : s7.reg 0 = word width raw.nodes.size := count
  have cursor7 : s7.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base) := cursor
  have l7 := ordered_copy_live raw valid numbering initial s7 H base rankBase S (((g ++ h) ++ d) ++ a) i7 rfl
  have s7size : s7.heap.size = S + 5 + 6 * V := by
    have bound : s7.heap.size = S + (((g ++ h) ++ d) ++ a).length := i7.allocation
    simp only [List.length_append, gl, hl, dl, al] at bound
    omega
  obtain ⟨s8, p8, t8, b8, pc8, i8⟩ :=
    source_child_stage resident raw valid numbering initial s7 H base rankBase S
      (entry + 128) (entry + 157) (((g ++ h) ++ d) ++ a) i7 parts.childSetup
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using parts.childStream)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using parts.childBack)
      pc7 (by omega) (by rw [childCount]; omega) queueFits nodesFit
      (numbered_child_source_room raw valid numbering s7.heap H i7.retained.image (by omega))
      (by simpa only [orderLength] using count7) cursor7
  have l8 := ordered_copy_live raw valid numbering initial s8 H base rankBase S ((((g ++ h) ++ d) ++ a) ++ c) i8 rfl
  have s8size : s8.heap.size = S + 5 + 6 * V + E := by
    have bound : s8.heap.size = S + (((((g ++ h) ++ d) ++ a) ++ c)).length := i8.allocation
    simp only [List.length_append, gl, hl, dl, al, cl] at bound
    omega
  obtain ⟨s9, t9, pc9, i9, count9, cursor9⟩ :=
    source_copy_restart resident raw valid numbering initial s8 H base rankBase S
      (entry + 157) (entry + 160) ((((g ++ h) ++ d) ++ a) ++ c) i8 parts.restartGuard pc8 (by omega)
  have l9 := ordered_copy_live raw valid numbering initial s9 H base rankBase S ((((g ++ h) ++ d) ++ a) ++ c) i9 rfl
  have s9size : s9.heap.size = S + 5 + 6 * V + E := by
    have bound : s9.heap.size = S + (((((g ++ h) ++ d) ++ a) ++ c)).length := i9.allocation
    simp only [List.length_append, gl, hl, dl, al, cl] at bound
    omega
  obtain ⟨s10, p10, t10, b10, pc10, i10⟩ :=
    source_guard_stage resident raw valid numbering initial s9 H base rankBase S
      (entry + 160) (entry + 187) ((((g ++ h) ++ d) ++ a) ++ c) i9 parts.guardSetup
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using parts.guardStream)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using parts.guardBack)
      pc9 (by omega) (by rw [guardCount]; omega) queueFits nodesFit
      (numbered_guard_source_room raw valid numbering s9.heap H i9.retained.image (by omega))
      (by simpa only [orderLength] using count9) cursor9
  have l10 := ordered_copy_live raw valid numbering initial s10 H base rankBase S (((((g ++ h) ++ d) ++ a) ++ c) ++ u) i10 rfl
  have s10size : s10.heap.size = S + 5 + 6 * V + E + U := by
    have bound : s10.heap.size = S + ((((((g ++ h) ++ d) ++ a) ++ c) ++ u)).length := i10.allocation
    simp only [List.length_append, gl, hl, dl, al, cl, ul] at bound
    omega
  have sourceEnd := original_packet_stored_end s10.heap H channels raw i10.retained.image
  rw [original_packet_size] at sourceEnd
  obtain ⟨final, p11, t11, b11, pc11, i11⟩ :=
    source_root_stage resident raw valid numbering initial s10 H base rankBase S
      (entry + 187) done (((((g ++ h) ++ d) ++ a) ++ c) ++ u) i10
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using parts.rootSetup)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using parts.rootStream)
      pc10 (by omega) (by omega)
      (by
        simp only [originalRootStart, original_rows_length]
        dsimp only [V, E, U, R] at cap s10size
        omega) nodesFit
  have trace := ((t8.append t9).append t10).append t11
  refine ⟨final, max (max (max p8 s8.liveWords) p10) p11, ?_, ?_, pc11, ?_⟩
  · have ticksEq :
        (((21 * numbering.order.length + 9 * childOccurrenceCount (numberedChildRows (width := width) raw valid numbering) + 1) + 3) +
          (21 * numbering.order.length + 7 * guardOccurrenceCount (numberedGuardRows (width := width) raw valid numbering) + 1)) +
          (9 * raw.roots.length + 12) =
        42 * raw.nodes.size + 9 * (rowChildren (originalRows raw)).length +
          7 * (rowGuards (originalRows raw)).length + 9 * raw.roots.length + 17 := by
      rw [orderLength, childCount, guardCount]
      dsimp only [V]
      omega
    rw [← ticksEq]
    exact trace
  · simp only [max_le_iff]
    simp only [List.length_append, gl, hl, dl, al, cl, ul] at l7 l8 l9 l10
    have childSpace : p8 ≤ s7.liveWords + E := by simpa only [childCount] using b8
    have guardSpace : p10 ≤ s9.liveWords + U := by simpa only [guardCount] using b10
    dsimp only [V, E, U, R, s7] at childSpace guardSpace l7 l8 l9 l10 ⊢
    omega
  · simpa only [numberedPacketWords, numberedGlobalWords, g, h, d, a, c, u, r,
      List.append_assoc] using i11

theorem ordered_source_copy_execution (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (initial : State width 8)
    (H base rankBase entry done : Nat)
    (facts : RetainedCopyFacts raw valid numbering initial.heap H base rankBase)
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width raw.nodes.size
        (rowChildren (originalRows raw)).length base entry done)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 207 < 2 ^ width)
    (capacity : channels + initial.heap.size +
      (numberedPacketWords (width := width) raw valid numbering).length < 2 ^ width)
    (allocation : initial.heap.size = rankBase + raw.nodes.size)
    (rankHeld : initial.reg 4 = word width rankBase)
    (scratchBefore : base + 4 * raw.nodes.size + 4 ≤ H)
    (rankAfter : H ≤ rankBase) :
    ∃ final ticks peak, Execution resident initial final ticks peak ∧
      ticks ≤ 119 * raw.nodes.size + 9 * (rowChildren (originalRows raw)).length +
        7 * (rowGuards (originalRows raw)).length + 9 * raw.roots.length + 68 ∧
      peak ≤ initial.liveWords + (numberedPacketWords (width := width) raw valid numbering).length ∧
      final.pc = word width done ∧
      OrderedCopyInvariant raw valid numbering initial final H base rankBase initial.heap.size
        (numberedPacketWords (width := width) raw valid numbering) := by
  obtain ⟨first, firstTicks, firstPeak, firstTrace, firstTime, firstSpace, firstPC,
      firstInvariant, firstCount, firstCursor⟩ :=
    ordered_source_copy_fixed_execution resident raw valid numbering initial H base rankBase entry done
      facts physical position running codeFits capacity allocation rankHeld scratchBefore rankAfter
  obtain ⟨final, suffixPeak, suffixTrace, suffixSpace, finalPC, finalInvariant⟩ :=
    ordered_source_copy_suffix_execution resident raw valid numbering initial first H base rankBase entry done
      physical codeFits capacity allocation scratchBefore rankAfter firstInvariant firstPC firstCount firstCursor
  have firstLive := ordered_copy_live raw valid numbering initial first H base rankBase initial.heap.size
    (numberedFixedWords (width := width) raw valid numbering) firstInvariant rfl
  have fixedLength : (numberedFixedWords (width := width) raw valid numbering).length =
      5 + 6 * raw.nodes.size := by
    have originalCount : (raw.toUnordered valid).nodeCount = raw.nodes.size := rfl
    simp only [numberedFixedWords, numberedGlobalWords, List.length_append, List.length_cons,
      List.length_nil, copied_header_words_length, directory_cursor_words_length,
      copied_arity_words_length, numberedHeaderRows, numberedDirectoryRows,
      List.length_map, List.length_finRange, numbering.length_eq_nodeCount, originalCount]
    omega
  rw [fixedLength] at firstLive
  have packetLength := numbered_packet_length (width := width) raw valid numbering
  have trace := firstTrace.append suffixTrace
  refine ⟨final, _, _, trace, ?_, ?_, finalPC, finalInvariant⟩
  · omega
  · simp only [max_le_iff]
    rw [packetLength]
    omega

/-- The original-source copy caller executes all 207 fetched instructions, including
all ordered duplicate occurrences, and retains its source and produced rank table. -/
theorem ordered_copy_execution (resident : Program width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (initial : State width 8)
    (H base rankBase entry done : Nat)
    (image : OriginalImageStored initial.heap H channels raw)
    (rawCell : initial.heap[Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base]? = some (word width H))
    (queue : ∀ index : Fin numbering.order.length,
      initial.heap[Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + index.val]? =
        some (word width (numbering.order[index.val].val)))
    (ranks : ∀ index : Fin numbering.order.length,
      initial.heap[rankBase + numbering.order[index.val].val]? = some (word width index.val))
    (physical : ∀ phase : Fin 207, resident[entry + phase.val]? =
      (orderedTypedCopyCode width raw.nodes.size
        (rowChildren (originalRows raw)).length base entry done)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 207 < 2 ^ width)
    (capacity : channels + initial.heap.size +
      (numberedPacketWords (width := width) raw valid numbering).length < 2 ^ width)
    (allocation : initial.heap.size = rankBase + raw.nodes.size)
    (rankHeld : initial.reg 4 = word width rankBase)
    (scratchBefore : base + 4 * raw.nodes.size + 4 ≤ H)
    (rankAfter : H ≤ rankBase) :
    ∃ final ticks peak, Execution resident initial final ticks peak ∧
      ticks ≤ 119 * raw.nodes.size + 9 * (rowChildren (originalRows raw)).length +
        7 * (rowGuards (originalRows raw)).length + 9 * raw.roots.length + 68 ∧
      peak ≤ initial.liveWords + (numberedPacketWords (width := width) raw valid numbering).length ∧
      final.pc = word width done ∧ final.halted = false ∧
      CopiedPacketCells final.heap initial.heap.size (numberedPacketWords (width := width) raw valid numbering) ∧
      final.heap.size = initial.heap.size + (numberedPacketWords (width := width) raw valid numbering).length ∧
      OriginalImageStored final.heap H channels raw ∧
      (∀ index : Fin numbering.order.length,
        final.heap[Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + index.val]? =
          some (word width (numbering.order[index.val].val))) ∧
      (∀ index : Fin numbering.order.length,
        final.heap[rankBase + numbering.order[index.val].val]? = some (word width index.val)) ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width rankBase ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) ∧
      final.heap[Controller.Horn.WorklistBucketReady.nextSlot (n := raw.nodes.size) base]? =
        some (word width initial.heap.size) := by
  obtain ⟨final, ticks, peak, trace, time, space, pc, invariant⟩ :=
    ordered_source_copy_execution resident raw valid numbering initial H base rankBase entry done
      ⟨image, rawCell, queue, ranks⟩ physical position running codeFits capacity allocation
      rankHeld scratchBefore rankAfter
  exact ⟨final, ticks, peak, trace, time, space, pc, invariant.running,
    invariant.packet, invariant.allocation, invariant.retained.image,
    invariant.retained.queue, invariant.retained.ranks, invariant.stack, invariant.output,
    invariant.rankRegister, invariant.zeroRegister, invariant.maskRegister, invariant.originCell⟩


theorem mapped_header_words (gate : Gate channels available)
    (mapper : (child : Fin available) → child ∈ gate.children → Fin target) :
    let source := originalRow (RawGate.ofGate gate)
    let result := originalRow (RawGate.ofGate (gate.mapChildren mapper))
    [word width source.tag,
      if source.tag < 3 then word width source.head else word width result.head] =
      [word width result.tag, word width result.head] := by
  cases gate <;> simp [originalRow, RawGate.ofGate, Gate.mapChildren]

theorem mapped_arity_words (gate : Gate channels available)
    (mapper : (child : Fin available) → child ∈ gate.children → Fin target) :
    let source := originalRow (RawGate.ofGate gate)
    let result := originalRow (RawGate.ofGate (gate.mapChildren mapper))
    [word width source.children.length, word width source.guards.length] =
      [word width result.children.length, word width result.guards.length] := by
  cases gate <;> simp [originalRow, RawGate.ofGate, Gate.mapChildren]

theorem numbered_header_image (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    copiedHeaderWords (numberedHeaderRows (width := width) raw valid numbering) =
      (rowHeaders (numberedRows raw valid numbering)).map (word width) := by
  simp only [copiedHeaderWords, numberedHeaderRows, numberedRows, rowHeaders,
    List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro index member
  let old := numbering.oldIndex index
  have original := raw.toUnordered_node valid old
  have mapped := mapped_header_words (width := width)
    ((raw.toUnordered valid).node old) (numbering.child index)
  change [word width (originalRow raw.nodes[old.val]).tag,
    if (originalRow raw.nodes[old.val]).tag < 3 then
      word width (originalRow raw.nodes[old.val]).head else
      word width (UniformDAGSource.typedHead (numbering.toDAG.node index))] = _
  rw [← original, ← erased_typed_row_head (numbering.toDAG.node index)]
  simpa only [UnorderedDAG.Numbering.toDAG, old, List.map_cons, List.map_nil] using mapped

theorem directory_row_image (indices : List α) (directory : α → DirectorySourceRow)
    (row : α → Row) (childCursor guardCursor : Nat)
    (counts : ∀ index ∈ indices,
      (directory index).children = (row index).children.length ∧
      (directory index).guards = (row index).guards.length) :
    directoryCursorWords (width := width) childCursor guardCursor (indices.map directory) =
      (rowBases (indices.map row) childCursor guardCursor).map (word width) := by
  induction indices generalizing childCursor guardCursor with
  | nil => rfl
  | cons index rest ih =>
    obtain ⟨children, guards⟩ := counts index (by simp)
    have restCounts : ∀ index ∈ rest,
        (directory index).children = (row index).children.length ∧
        (directory index).guards = (row index).guards.length := by
      intro next member
      exact counts next (by simp only [List.mem_cons]; exact Or.inr member)
    simp only [List.map_cons, rowBases, directoryCursorWords, List.map_append,
      List.map_cons, List.map_nil, countSource_value, Nat.zero_add, children, guards]
    exact congrArg (fun words => word width childCursor :: word width guardCursor :: words)
      (ih _ _ restCounts)

theorem arity_row_image (indices : List α) (directory : α → DirectorySourceRow)
    (row : α → Row)
    (counts : ∀ index ∈ indices,
      (directory index).children = (row index).children.length ∧
      (directory index).guards = (row index).guards.length) :
    copiedArityWords (width := width) (indices.map directory) =
      (rowArities (indices.map row)).map (word width) := by
  simp only [copiedArityWords, rowArities, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro index member
  obtain ⟨children, guards⟩ := counts index member
  simp only [countSource_value, Nat.zero_add, children, guards, List.map_cons, List.map_nil]

theorem numbered_incidence_image (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    (rowChildren (numberedRows raw valid numbering)).length =
      (rowChildren (originalRows raw)).length ∧
    (rowGuards (numberedRows raw valid numbering)).length =
      (rowGuards (originalRows raw)).length := by
  have incidenceMatch := matched_incidence_lengths numbering.toDAG (numberedRows raw valid numbering)
    (numbered_rows_match raw valid numbering)
  have children := RawNumberingCounts.numbered_children raw valid numbering
  have guards := RawNumberingCounts.numbered_guards raw valid numbering
  have rowEq : RawNumberingCounts.rowOfGate = originalRow := by
    funext gate
    cases gate <;> rfl
  have rowsEq : RawNumberingCounts.rawRows raw = originalRows raw := by
    simp only [RawNumberingCounts.rawRows, originalRows, rowEq]
  constructor
  · exact incidenceMatch.1.trans (by simpa only [RawNumberingCounts.rawChildren, rowsEq] using children)
  · exact incidenceMatch.2.trans (by simpa only [RawNumberingCounts.rawGuards, rowsEq] using guards)

theorem copied_child_flat (rows : List (ChildSourceRow width)) :
    copiedChildWords rows = rows.flatMap (fun row => row.occurrences.map MappedOccurrence.mapped) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [copiedChildWords, List.flatMap_cons, ih]

theorem copied_guard_flat (rows : List (GuardSourceRow width)) :
    copiedGuardWords rows = rows.flatMap GuardSourceRow.values := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [copiedGuardWords, List.flatMap_cons, ih]

theorem numbered_children_image (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    copiedChildWords (numberedChildRows (width := width) raw valid numbering) =
      (rowChildren (numberedRows raw valid numbering)).map (word width) := by
  simp only [copied_child_flat, numberedChildRows, numberedRows, rowChildren,
    List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro index member
  have rows := (erased_typed_row_matches (numbering.toDAG.node index)).2.2.1
  have children := Gate.mapChildren_children_map
    ((raw.toUnordered valid).node (numbering.oldIndex index)) (numbering.child index)
    Fin.val (fun child => (numbering.newIndex child).val) (by intro child present; rfl)
  rw [rows]
  simpa only [numberedChildRow, UnorderedDAG.Numbering.toDAG,
    List.map_map, Function.comp_def] using
    congrArg (fun values : List Nat => values.map (word width)) children.symm

theorem numbered_guards_image (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    copiedGuardWords (numberedGuardRows (width := width) raw valid numbering) =
      (rowGuards (numberedRows raw valid numbering)).map (word width) := by
  simp only [copied_guard_flat, numberedGuardRows, numberedRows, rowGuards,
    List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro index member
  rw [(erased_typed_row_matches (numbering.toDAG.node index)).2.2.2]
  change _ = ((((raw.toUnordered valid).node (numbering.oldIndex index)).mapChildren
    (numbering.child index)).guardLabels.map Fin.val).map (word width)
  rw [Gate.mapChildren_guardLabels]
  rfl

theorem numbered_row_count_agreement (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (index : Fin numbering.order.length) :
    (numberedDirectoryRow raw valid numbering index).children =
      (originalRow (RawGate.ofGate (numbering.toDAG.node index))).children.length ∧
    (numberedDirectoryRow raw valid numbering index).guards =
      (originalRow (RawGate.ofGate (numbering.toDAG.node index))).guards.length := by
  have counts := erased_typed_row_counts (numbering.toDAG.node index)
  constructor
  · exact (numbering.toDAG_child_length index).symm.trans counts.1.symm
  · have unchanged : (numbering.toDAG.node index).guardLabels =
        ((raw.toUnordered valid).node (numbering.oldIndex index)).guardLabels := by
      exact Gate.mapChildren_guardLabels _ _
    exact (congrArg List.length unchanged).symm.trans counts.2.symm

/-- The image identity is derived from the produced ordering and the original
ordered source lists, including repeated children, guards, and roots. -/
theorem numbered_packet_image (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    numberedPacketWords (width := width) raw valid numbering =
      [word width channels, word width numbering.toDAG.nodeCount,
        word width numbering.toDAG.childIncidences, word width numbering.toDAG.guardIncidences,
        word width numbering.toDAG.roots.length] ++
      (serializedRows 5 (numberedRows raw valid numbering)
        (numbering.toDAG.roots.map Fin.val)).map (word width) := by
  have rowCount := numbered_rows_length raw valid numbering
  have nodes : numbering.toDAG.nodeCount = raw.nodes.size := numbering.toDAG_nodeCount
  obtain ⟨childCount, guardCount⟩ := numbered_incidence_image raw valid numbering
  have children := RawNumberingCounts.numbered_children raw valid numbering
  have guards := RawNumberingCounts.numbered_guards raw valid numbering
  have rowEq : RawNumberingCounts.rowOfGate = originalRow := by funext gate; cases gate <;> rfl
  have rowsEq : RawNumberingCounts.rawRows raw = originalRows raw := by
    simp only [RawNumberingCounts.rawRows, originalRows, rowEq]
  have typedChildren : numbering.toDAG.childIncidences = (rowChildren (originalRows raw)).length := by
    simpa only [RawNumberingCounts.rawChildren, rowsEq] using children
  have typedGuards : numbering.toDAG.guardIncidences = (rowGuards (originalRows raw)).length := by
    simpa only [RawNumberingCounts.rawGuards, rowsEq] using guards
  have roots := RawNumberingCounts.numbered_roots raw valid numbering
  have directory := directory_row_image (width := width)
    (List.finRange numbering.order.length) (numberedDirectoryRow raw valid numbering)
    (fun index => originalRow (RawGate.ofGate (numbering.toDAG.node index)))
    (5 + 6 * raw.nodes.size) (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length)
    (by intro index member; exact numbered_row_count_agreement raw valid numbering index)
  have arity := arity_row_image (width := width)
    (List.finRange numbering.order.length) (numberedDirectoryRow raw valid numbering)
    (fun index => originalRow (RawGate.ofGate (numbering.toDAG.node index)))
    (by intro index member; exact numbered_row_count_agreement raw valid numbering index)
  change directoryCursorWords (width := width) _ _ (numberedDirectoryRows raw valid numbering) =
    (rowBases (numberedRows raw valid numbering) _ _).map (word width) at directory
  change copiedArityWords (width := width) (numberedDirectoryRows raw valid numbering) =
    (rowArities (numberedRows raw valid numbering)).map (word width) at arity
  simp only [numberedPacketWords, numberedGlobalWords, serializedRows, List.map_append,
    rowCount, nodes, childCount, typedChildren, typedGuards, roots,
    numbered_header_image, directory, arity, numbered_children_image, numbered_guards_image,
    List.append_assoc]



def typedOriginRecoverCode (width nodes base : Nat) : Program width 8 :=
  #[.constant 4 (word width (Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base)),
    .load 4 4]

theorem typed_origin_recover_execution (resident : Program width 8)
    (nodes base entry origin : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 2, resident[entry + phase.val]? =
      (typedOriginRecoverCode width nodes base)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 2 < 2 ^ width)
    (slotFits : Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base < 2 ^ width)
    (originCell : state.heap[Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base]? =
      some (word width origin)) :
    ∃ final, Execution resident state final 2 state.liveWords ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width origin ∧
      (∀ register : Fin 8, register ≠ 4 → final.reg register = state.reg register) := by
  let slot := Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base
  let middle := state.advance.put 4 (word width slot)
  let final := middle.advance.put 4 (word width origin)
  have first : programStep resident state = some middle := by
    rw [fetched resident state entry (.constant 4 (word width slot)) position (by omega)
      (by simpa [typedOriginRecoverCode, slot] using physical ⟨0, by decide⟩)]
    exact copy_constant_step state 4 (word width slot) running
  have middlePC : middle.pc = word width (entry + 1) :=
    referenceAdvancePC state entry position (by omega)
  have last : programStep resident middle = some final := by
    rw [fetched resident middle (entry + 1) (.load 4 4) middlePC (by omega)
      (by simpa [typedOriginRecoverCode] using physical ⟨1, by decide⟩)]
    exact copy_load_step middle 4 4 slot (word width origin)
      (by simpa [middle, State.advance, State.put] using running) slotFits
      (by simp [middle, State.advance, State.put])
      (by simpa [middle, State.advance, State.put] using originCell)
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [middleLive, finalLive, max_self, Nat.reduceAdd] using
      Execution.cons first (Execution.cons last (Execution.refl final))
  · simpa only [final, State.put, Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC middle (entry + 1) middlePC (by omega)
  · simpa [final, middle, State.advance, State.put] using running
  · simp [final, middle, State.advance, State.put]
  · intro register different
    simp [final, middle, State.advance, State.put, ite_eq_right different]


def typedReleaseSetupCode (width releaseEntry : Nat) : Program width 8 :=
  #[.add 0 2 6, .branchZero 6 (word width releaseEntry)]

theorem typed_release_setup_execution (resident : Program width 8)
    (entry releaseEntry total : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 2, resident[entry + phase.val]? =
      (typedReleaseSetupCode width releaseEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 2 < 2 ^ width) (totalFits : total < 2 ^ width)
    (totalHeld : state.reg 2 = word width total) (zeroHeld : state.reg 6 = word width 0) :
    ∃ final, Execution resident state final 2 state.liveWords ∧
      final.pc = word width releaseEntry ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width total ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  let middle := state.advance.put 0 (word width total)
  let final : State width 8 := { middle.advance with pc := word width releaseEntry }
  have first : programStep resident state = some middle := by
    rw [fetched resident state entry (.add 0 2 6) position (by omega)
      (by simpa [typedReleaseSetupCode] using physical ⟨0, by decide⟩)]
    simpa [Nat.add_zero] using copy_add_step state 0 2 6 total 0 running totalFits
      (Nat.two_pow_pos width) totalHeld zeroHeld
  have middlePC : middle.pc = word width (entry + 1) :=
    referenceAdvancePC state entry position (by omega)
  have last : programStep resident middle = some final := by
    rw [fetched resident middle (entry + 1) (.branchZero 6 (word width releaseEntry))
      middlePC (by omega) (by simpa [typedReleaseSetupCode] using physical ⟨1, by decide⟩)]
    exact copy_branch_zero middle 6 releaseEntry
      (by simpa [middle, State.advance, State.put] using running)
      (by simpa [middle, State.advance, State.put] using zeroHeld)
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, rfl, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [middleLive, finalLive, max_self, Nat.reduceAdd] using
      Execution.cons first (Execution.cons last (Execution.refl final))
  · simpa [final, middle, State.advance, State.put] using running
  · simp [final, middle, State.advance, State.put]
  · intro register different
    simp [final, middle, State.advance, State.put, ite_eq_right different]



def typedSaveSetupCode (width count saveEntry : Nat) : Program width 8 :=
  #[.constant 0 (word width count), .constant 1 (word width (count - 1)),
    .add 1 1 4, .constant 2 (word width count), .add 2 2 4,
    .constant 6 (word width 0), .constant 7 (word width (2 ^ width - 1)),
    .branchZero 6 (word width saveEntry)]

theorem typed_save_setup_execution (resident : Program width 8)
    (entry saveEntry origin count : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 8, resident[entry + phase.val]? =
      (typedSaveSetupCode width count saveEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 8 < 2 ^ width) (room : origin + count < 2 ^ width)
    (positive : 0 < count) (originHeld : state.reg 4 = word width origin) :
    ∃ final, Execution resident state final 8 state.liveWords ∧
      final.pc = word width saveEntry ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width count ∧ final.reg 1 = word width (origin + count - 1) ∧
      final.reg 2 = word width (origin + count) ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) := by
  let s1 : State width 8 := state.advance.put 0 (word width count)
  let s2 : State width 8 := s1.advance.put 1 (word width (count - 1))
  let s3 : State width 8 := s2.advance.put 1 (word width ((count - 1) + origin))
  let s4 : State width 8 := s3.advance.put 2 (word width count)
  let s5 : State width 8 := s4.advance.put 2 (word width (count + origin))
  let s6 : State width 8 := s5.advance.put 6 (word width 0)
  let s7 : State width 8 := s6.advance.put 7 (word width (2 ^ width - 1))
  let s8 : State width 8 := { s7.advance with pc := word width saveEntry }
  have pc0 : state.pc = word width (entry + 0) := by
    simpa [Nat.add_zero] using position
  have t1 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 0 (word width count)) pc0 (by omega)
      (by simpa [typedSaveSetupCode] using physical ⟨0, by decide⟩)]
    exact copy_constant_step state 0 (word width count) (by simpa [State.advance, State.put] using running)
  have pc1 : s1.pc = word width (entry + 1) := by
    simpa only [s1, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state _ pc0 (by omega)
  have t2 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 1 (word width (count - 1))) pc1 (by omega)
      (by simpa [typedSaveSetupCode] using physical ⟨1, by decide⟩)]
    exact copy_constant_step s1 1 (word width (count - 1)) (by simpa [s1, State.advance, State.put] using running)
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 _ pc1 (by omega)
  have t3 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.add 1 1 4) pc2 (by omega)
      (by simpa [typedSaveSetupCode] using physical ⟨2, by decide⟩)]
    exact copy_add_step s2 1 1 4 (count - 1) origin
      (by simpa [s1, s2, State.advance, State.put] using running) (by omega) (by omega)
      (by simp [s1, s2, State.advance, State.put])
      (by simpa [s1, s2, State.advance, State.put] using originHeld)
  have pc3 : s3.pc = word width (entry + 3) := by
    simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 _ pc2 (by omega)
  have t4 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.constant 2 (word width count)) pc3 (by omega)
      (by simpa [typedSaveSetupCode] using physical ⟨3, by decide⟩)]
    exact copy_constant_step s3 2 (word width count) (by simpa [s1, s2, s3, State.advance, State.put] using running)
  have pc4 : s4.pc = word width (entry + 4) := by
    simpa only [s4, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 _ pc3 (by omega)
  have t5 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 2 2 4) pc4 (by omega)
      (by simpa [typedSaveSetupCode] using physical ⟨4, by decide⟩)]
    exact copy_add_step s4 2 2 4 (count) origin
      (by simpa [s1, s2, s3, s4, State.advance, State.put] using running) (by omega) (by omega)
      (by simp [s1, s2, s3, s4, State.advance, State.put])
      (by simpa [s1, s2, s3, s4, State.advance, State.put] using originHeld)
  have pc5 : s5.pc = word width (entry + 5) := by
    simpa only [s5, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 _ pc4 (by omega)
  have t6 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.constant 6 (word width 0)) pc5 (by omega)
      (by simpa [typedSaveSetupCode] using physical ⟨5, by decide⟩)]
    exact copy_constant_step s5 6 (word width 0) (by simpa [s1, s2, s3, s4, s5, State.advance, State.put] using running)
  have pc6 : s6.pc = word width (entry + 6) := by
    simpa only [s6, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5 _ pc5 (by omega)
  have t7 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 7 (word width (2 ^ width - 1))) pc6 (by omega)
      (by simpa [typedSaveSetupCode] using physical ⟨6, by decide⟩)]
    exact copy_constant_step s6 7 (word width (2 ^ width - 1)) (by simpa [s1, s2, s3, s4, s5, s6, State.advance, State.put] using running)
  have pc7 : s7.pc = word width (entry + 7) := by
    simpa only [s7, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6 _ pc6 (by omega)
  have t8 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.branchZero 6 (word width saveEntry)) pc7 (by omega)
      (by simpa [typedSaveSetupCode] using physical ⟨7, by decide⟩)]
    exact copy_branch_zero s7 6 saveEntry
      (by simpa [s1, s2, s3, s4, s5, s6, s7, State.advance, State.put] using running)
      (by simp [s1, s2, s3, s4, s5, s6, s7, State.advance, State.put])
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4
    (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s8))))))))
  have live1 : s1.liveWords = state.liveWords := rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have live4 : s4.liveWords = state.liveWords := rfl
  have live5 : s5.liveWords = state.liveWords := rfl
  have live6 : s6.liveWords = state.liveWords := rfl
  have live7 : s7.liveWords = state.liveWords := rfl
  have live8 : s8.liveWords = state.liveWords := rfl
  refine ⟨s8, ?_, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [live1, live2, live3, live4, live5, live6, live7, live8, max_self, Nat.reduceAdd] using trace
  all_goals simp [s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, Nat.add_comm]
  all_goals congr 1 <;> omega



theorem typed_packet_save_release_execution (resident : Program width 8)
    (nodes base origin recoverEntry saveSetupEntry saveEntry releaseSetupEntry releaseEntry done : Nat)
    (packet : List (Word width)) (state : State width 8)
    (recoverPhysical : ∀ phase : Fin 2, resident[recoverEntry + phase.val]? =
      (typedOriginRecoverCode width nodes base)[phase.val]?)
    (setupPhysical : ∀ phase : Fin 8, resident[saveSetupEntry + phase.val]? =
      (typedSaveSetupCode width packet.length saveEntry)[phase.val]?)
    (savePhysical : RawTransferLoops.CodeAt resident saveEntry
      (RawTransferLoops.reverseSaveCode width saveEntry releaseSetupEntry))
    (releaseSetupPhysical : ∀ phase : Fin 2, resident[releaseSetupEntry + phase.val]? =
      (typedReleaseSetupCode width releaseEntry)[phase.val]?)
    (releasePhysical : RawTransferLoops.CodeAt resident releaseEntry
      (RawTransferLoops.countedReleaseCode width releaseEntry done))
    (recoverNext : recoverEntry + 2 = saveSetupEntry)
    (position : state.pc = word width recoverEntry) (running : state.halted = false)
    (recoverFits : recoverEntry + 2 < 2 ^ width) (setupFits : saveSetupEntry + 8 < 2 ^ width)
    (saveFits : saveEntry + 6 < 2 ^ width)
    (releaseSetupFits : releaseSetupEntry + 2 < 2 ^ width)
    (releaseFits : releaseEntry + 4 < 2 ^ width)
    (originPositive : 0 < origin) (packetPositive : 0 < packet.length)
    (room : origin + packet.length < 2 ^ width)
    (allocation : state.heap.size = origin + packet.length)
    (slotFits : Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base < 2 ^ width)
    (originCell : state.heap[Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base]? =
      some (word width origin))
    (cells : CopiedPacketCells state.heap origin packet) :
    ∃ final peak, Execution resident state final
      (6 * packet.length + 4 * state.heap.size + 14) peak ∧
      peak ≤ state.liveWords + packet.length ∧
      final.heap = #[] ∧ final.stack = packet ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 6 = word width 0 := by
  obtain ⟨recovered, tr, pcr, runr, hr, sr, outr, originHeld, retainedr⟩ :=
    typed_origin_recover_execution resident nodes base recoverEntry origin state recoverPhysical
      position running recoverFits slotFits originCell
  obtain ⟨setup, ts, pcs, runs, hs, ss, outs, counts, cursors, totals, zeros, masks⟩ :=
    typed_save_setup_execution resident saveSetupEntry saveEntry origin packet.length recovered
      setupPhysical (by simpa only [recoverNext] using pcr) runr setupFits room packetPositive originHeld
  have copied : ∀ index : Nat, ∀ bound : index < packet.length,
      setup.heap[origin + index]? = some packet[index] := by
    intro index bound
    rw [hs, hr]
    exact cells ⟨index, bound⟩
  obtain ⟨saved, savePeak, tv, bv, hv, sv, outv, pcv, runv, countv, retainedv⟩ :=
    RawTransferLoops.reverse_save_execution resident saveEntry releaseSetupEntry origin packet setup
      pcs runs saveFits originPositive room (by omega) counts cursors masks zeros copied savePhysical
  have totalv : saved.reg 2 = word width (origin + packet.length) :=
    (retainedv 2 (by decide) (by decide) (by decide)).trans totals
  have zerov : saved.reg 6 = word width 0 :=
    (retainedv 6 (by decide) (by decide) (by decide)).trans zeros
  have maskv : saved.reg 7 = word width (2 ^ width - 1) :=
    (retainedv 7 (by decide) (by decide) (by decide)).trans masks
  obtain ⟨releaseSetup, tu, pcu, runu, hu, su, outu, countu, retainedu⟩ :=
    typed_release_setup_execution resident releaseSetupEntry releaseEntry (origin + packet.length)
      saved releaseSetupPhysical pcv runv releaseSetupFits room totalv zerov
  have heapu : releaseSetup.heap.size = origin + packet.length := by
    rw [hu, hv, hs, hr]
    exact allocation
  have masku : releaseSetup.reg 7 = word width (2 ^ width - 1) :=
    (retainedu 7 (by decide)).trans maskv
  have zerou : releaseSetup.reg 6 = word width 0 :=
    (retainedu 6 (by decide)).trans zerov
  obtain ⟨final, releasePeak, tf, bf, hf, sf, outf, pcf, runf, countf, retainedf⟩ :=
    RawTransferLoops.counted_release_execution resident releaseEntry done (origin + packet.length)
      releaseSetup pcu runu releaseFits heapu room countu masku zerou releasePhysical
  have recoveredLive : recovered.liveWords = state.liveWords := by
    simp only [State.liveWords, hr, sr, outr]
  have setupLive : setup.liveWords = state.liveWords := by
    simp only [State.liveWords, hs, ss, outs, hr, sr, outr]
  have savedLive : saved.liveWords = state.liveWords + packet.length := by
    simp only [State.liveWords, hv, sv, outv, hs, ss, outs, hr, sr, outr, List.length_append]
    omega
  have releaseSetupLive : releaseSetup.liveWords = state.liveWords + packet.length := by
    simpa only [State.liveWords, hu, su, outu] using savedLive
  have trace := (((tr.append ts).append tv).append tu).append tf
  refine ⟨final, max (max (max (max state.liveWords recovered.liveWords) savePeak) saved.liveWords) releasePeak, ?_, ?_, hf, ?_, ?_, pcf, runf, ?_⟩
  · have ticksEq : (((2 + 8) + (6 * packet.length + 1)) + 2) +
        (4 * (origin + packet.length) + 1) =
        6 * packet.length + 4 * state.heap.size + 14 := by rw [allocation]; omega
    rw [← ticksEq]
    exact trace
  · simp only [max_le_iff]
    omega
  · rw [sf, su, sv, ss, sr]
  · exact outf.trans (outu.trans (outv.trans (outs.trans outr)))
  · exact (retainedf 6 (by decide)).trans zerou


-- Fixed fetched handoff after counted release. Low registers0/1/2 may retain
-- arbitrary words because ForestCounter.counterState exposes those inputs;
-- low register3 is explicitly cleared by the actual code, not state reset.
open Controller.Cost.SparseConeTraversal

def typedColdHandoffCode (width typedEntry : Nat) : Program width 8 :=
  #[.constant 3 (word width 0), .branchZero 6 (word width typedEntry)]

theorem typed_cold_handoff_execution (resident : Program width 8)
    (entry typedEntry : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 2, resident[entry + phase.val]? =
      (typedColdHandoffCode width typedEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 2 < 2 ^ width) (zeroHeld : state.reg 6 = word width 0)
    (empty : state.heap = #[]) :
    ∃ final, Execution resident state final 2 state.liveWords ∧
      final = { (widenState
        ((ForestCounter.counterState (#[] : Array (Word width)) 0
          (state.reg 0) (state.reg 1) (state.reg 2)).frame state.stack state.output)
        state.reg) with pc := word width typedEntry } := by
  let middle := state.advance.put 3 (word width 0)
  let final : State width 8 := { middle.advance with pc := word width typedEntry }
  have first : programStep resident state = some middle := by
    rw [fetched resident state entry (.constant 3 (word width 0)) position (by omega)
      (by simpa [typedColdHandoffCode] using physical ⟨0, by decide⟩)]
    exact copy_constant_step state 3 (word width 0) running
  have middlePC : middle.pc = word width (entry + 1) := by
    exact referenceAdvancePC state entry position (by omega)
  have last : programStep resident middle = some final := by
    rw [fetched resident middle (entry + 1) (.branchZero 6 (word width typedEntry))
      middlePC (by omega)
      (by simpa [typedColdHandoffCode] using physical ⟨1, by decide⟩)]
    exact copy_branch_zero middle 6 typedEntry running (by simpa [middle, State.put, State.advance] using zeroHeld)
  have trace := Execution.cons first (Execution.cons last (Execution.refl final))
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, ?_⟩
  · simpa only [Nat.reduceAdd, middleLive, finalLive, max_self] using trace
  · apply copy_state_ext
    · intro register
      fin_cases register <;>
        simp [final, middle, widenState, ForestCounter.counterState,
          Controller.Cost.State.frame, State.advance, State.put]
    · exact empty
    · rfl
    · rfl
    · rfl
    · exact running


open Controller.Decoder Controller.Cost.SparseConeTraversal

def typedWarmCode (width entry nodeBase temporary : Nat)
    (layout : UniformDAGNode.Layout) : Program width 8 :=
  #[.branchZero 4 (word width (entry + 125)), .load 5 6, .add 3 5 5,
    .branchZero 2 (word width (entry + 4))] ++
  widenProgram (UniformDAGNode.code width (entry + 4) layout).toArray ++
  commitResultCode width temporary nodeBase ++
  #[.constant 2 (word width 0), .constant 3 (word width 1),
    .constant 5 (word width (2 ^ width - 1)), .add 4 4 5, .add 6 6 3,
    .branchZero 2 (word width entry)]

def typedShapeLayout (channels nodes children guards roots : Nat) : SharedLayout where
  sourceEnd := 5 + 6 * nodes + children + guards + roots
  nodeCount := nodes
  channels := channels

def typedShapeNodeLayout (channels nodes children guards roots : Nat) : UniformDAGNode.Layout where
  tagBase := 5
  headBase := 6
  channelBase := 5 + 6 * nodes + children + guards + roots
  nodeBase := 5 + 6 * nodes + children + guards + roots + channels
  childArityBase := 5 + 4 * nodes
  childSourceBase := 5 + 2 * nodes
  guardArityBase := 5 + 4 * nodes + 1
  guardSourceBase := 5 + 2 * nodes + 1

def typedShapeDFS (width base channels nodes children guards roots : Nat) : Program width 8 :=
  let shared := typedShapeLayout channels nodes children guards roots
  dfsProgram width base (5 + 4 * nodes) (5 + 2 * nodes) (5 + 4 * nodes + 1) (5 + 2 * nodes + 1)
    5 6 shared.nodeMarkerBase shared.channelMarkerBase shared.nodeCountSlot shared.channelCountSlot
    shared.mapBase shared.nodeLedgerBase shared.channelLedgerBase
    (5 + 6 * nodes + children + guards) roots

def typedShapeOuter (width base channels nodes children guards roots : Nat) : Program width 8 :=
  let shared := typedShapeLayout channels nodes children guards roots
  #[.branchZero 4 (word width (base + 297)), .push 4,
    .constant 4 (word width 1), .branchZero 2 (word width (base + 9))] ++
  typedShapeDFS width (base + 4) channels nodes children guards roots ++
  #[.push 6, .constant 1 (word width (2 ^ width - 1)), .add 7 6 1, .load 7 7,
    .constant 6 (word width shared.nodeLedgerBase), .constant 1 (word width shared.nodeCountSlot), .load 4 1] ++
  typedWarmCode width (base + 131) shared.nodeValueBase shared.storageEnd
    (typedShapeNodeLayout channels nodes children guards roots) ++
  #[.constant 6 (word width shared.nodeLedgerBase), .constant 1 (word width shared.nodeCountSlot), .load 4 1] ++
  SparseConeReuse.resetNodesCode width (base + 259) shared.nodeMarkerBase shared.mapBase ++
  #[.constant 6 (word width shared.channelLedgerBase), .constant 1 (word width shared.channelCountSlot), .load 4 1] ++
  SparseConeReuse.resetChannelsCode width (base + 274) shared.channelMarkerBase ++
  SparseConeReuse.clearLedgerCountsCode width shared.nodeCountSlot shared.channelCountSlot ++
  #[.constant 1 (word width shared.nodeValueBase), .add 1 1 7, .load 0 1, .emit 0] ++
  #[.constant 7 (word width 0), .pop 6, .pop 4, .constant 5 (word width (2 ^ width - 1)),
    .add 4 4 5, .branchZero 2 (word width base)] ++ #[.halt]

/-- Resident code depends only on counted sizes. All original-ID values are
read from the copied packet; numbering never selects a new program. -/
@[irreducible] def typedShapeCode (width channels nodes children guards roots : Nat) : Program width 8 :=
  let low := (ForestInputMetadata.fullCode width 0 ++
    (InputLoad.code channels ++ UniformDAGLoop.code width (33 + 2 * channels) 1
      (typedShapeNodeLayout channels nodes children guards roots))).toArray ++
    (Initialize.code (word width 0) (2 * channels + 3 * nodes + 2)).toArray
  widenProgram low ++
  #[.constant 2 (word width 0), .constant 3 (word width 1), .constant 7 (word width 0),
    .constant 4 (word width roots), .constant 6 (word width (5 + 6 * nodes + children + guards))] ++
  typedShapeOuter width (low.size + 5) channels nodes children guards roots

-- Next proof consumes cold_sparse_execution at its actual widened cold state.
-- Its program equality is derived solely from packetHeaderHeap_size,
-- cacheHeap_size/channelHeap_size, matched lengths, and scalar layout fields.
-- The actual adapter must supply fetched low-register setup and relocation;
-- this code template does not reset state or assume a cold continuation.


open Controller.Cost.SparseConeReuse

def typedSourceWarmLayout (caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (layout : SharedLayout) : UniformDAGNode.Layout where
  tagBase := caller.size
  headBase := caller.size + 1
  channelBase := layout.channelValueBase
  nodeBase := layout.nodeValueBase
  childArityBase := caller.size + 4 * rows.length
  childSourceBase := caller.size + 2 * rows.length
  guardArityBase := caller.size + 4 * rows.length + 1
  guardSourceBase := caller.size + 2 * rows.length + 1

def typedSourceOuter (width base : Nat) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (layout : SharedLayout) : Program width 8 :=
  let dfsBase := base + 4
  let warmBase := base + 131
  let nodeResetBase := base + 259
  let channelResetBase := base + 274
  #[.branchZero 4 (word width (base + 297)), .push 4,
    .constant 4 (word width 1), .branchZero 2 (word width (dfsBase + 5))] ++
  dfsFromCache width caller rows roots dfsBase layout ++
  #[.push 6, .constant 1 (word width (2 ^ width - 1)), .add 7 6 1, .load 7 7,
    .constant 6 (word width layout.nodeLedgerBase), .constant 1 (word width layout.nodeCountSlot), .load 4 1] ++
  typedWarmCode width warmBase layout.nodeValueBase layout.storageEnd (typedSourceWarmLayout caller rows layout) ++
  #[.constant 6 (word width layout.nodeLedgerBase), .constant 1 (word width layout.nodeCountSlot), .load 4 1] ++
  resetNodesCode width nodeResetBase layout.nodeMarkerBase layout.mapBase ++
  #[.constant 6 (word width layout.channelLedgerBase), .constant 1 (word width layout.channelCountSlot), .load 4 1] ++
  resetChannelsCode width channelResetBase layout.channelMarkerBase ++
  clearLedgerCountsCode width layout.nodeCountSlot layout.channelCountSlot ++
  #[.constant 1 (word width layout.nodeValueBase), .add 1 1 7, .load 0 1, .emit 0] ++
  #[.constant 7 (word width 0), .pop 6, .pop 4, .constant 5 (word width (2 ^ width - 1)),
    .add 4 4 5, .branchZero 2 (word width base)] ++ #[.halt]

def typedSourceLayout (width : Nat) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) : SharedLayout where
  sourceEnd := (ForestIndexedOperands.cacheHeap width
    (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots).size
  nodeCount := graph.nodeCount
  channels := n

def typedSourceScratch (graph : DAG n) : Nat := 2 * n + 3 * graph.nodeCount + 2

def typedSourceCode (width : Nat) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n) : Program width 8 :=
  let caller := UniformDAGRun.packetHeaderHeap width n rows roots
  let layout := typedSourceLayout width graph rows roots
  let low := UniformDAGResources.program width n rows roots assignment ++
    (Initialize.code (word width 0) (typedSourceScratch graph)).toArray
  let outer := low.size + 5
  let rootStart := caller.size + 6 * rows.length +
    (ForestIndexedOperands.rowChildren rows).length + (ForestIndexedOperands.rowGuards rows).length
  widenProgram low ++
  #[.constant 2 (word width 0), .constant 3 (word width 1), .constant 7 (word width 0),
    .constant 4 (word width roots.length), .constant 6 (word width rootStart)] ++
  typedSourceOuter width outer caller rows roots layout

theorem typed_source_layout_shape (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows) :
    typedSourceLayout width graph rows roots = typedShapeLayout n graph.nodeCount
      (ForestIndexedOperands.rowChildren rows).length
      (ForestIndexedOperands.rowGuards rows).length roots.length := by
  simp only [typedSourceLayout, typedShapeLayout, ForestIndexedOperands.cacheHeap_size,
    UniformDAGRun.packetHeaderHeap_size, matched.length_eq]

theorem typed_source_dense_layout_shape (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n)
    (matched : ForestIndexedOperands.RowsMatch graph rows) :
    UniformDAGTypedNode.layout (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots assignment =
      typedShapeNodeLayout n graph.nodeCount (ForestIndexedOperands.rowChildren rows).length
        (ForestIndexedOperands.rowGuards rows).length roots.length := by
  simp only [UniformDAGTypedNode.layout, typedShapeNodeLayout,
    ForestInputPrefixStored.channelHeap_size, ForestIndexedOperands.cacheHeap_size,
    UniformDAGRun.packetHeaderHeap_size, matched.length_eq]

theorem typed_source_warm_layout_shape (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows) :
    typedSourceWarmLayout (UniformDAGRun.packetHeaderHeap width n rows roots) rows
      (typedSourceLayout width graph rows roots) =
      typedShapeNodeLayout n graph.nodeCount (ForestIndexedOperands.rowChildren rows).length
        (ForestIndexedOperands.rowGuards rows).length roots.length := by
  rw [typed_source_layout_shape graph rows roots matched]
  simp only [typedSourceWarmLayout, typedShapeNodeLayout, typedShapeLayout,
    SharedLayout.channelValueBase, SharedLayout.nodeValueBase,
    UniformDAGRun.packetHeaderHeap_size, matched.length_eq]

theorem typed_source_outer_shape (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows) (base : Nat) :
    typedSourceOuter width base (UniformDAGRun.packetHeaderHeap width n rows roots)
      rows roots (typedSourceLayout width graph rows roots) =
      typedShapeOuter width base n graph.nodeCount (ForestIndexedOperands.rowChildren rows).length
        (ForestIndexedOperands.rowGuards rows).length roots.length := by
  unfold typedSourceOuter typedShapeOuter
  rw [typed_source_warm_layout_shape graph rows roots matched,
    typed_source_layout_shape graph rows roots matched]
  simp only [dfsFromCache, typedShapeDFS, UniformDAGRun.packetHeaderHeap_size,
    matched.length_eq, Nat.add_assoc, Nat.reduceAdd]

/-- The accepted numbering changes packet data, while the resident code is
fixed by the original counted sizes and shared layout. -/
theorem typed_source_code_shape (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n)
    (matched : ForestIndexedOperands.RowsMatch graph rows) :
    typedSourceCode width graph rows roots assignment =
      typedShapeCode width n graph.nodeCount (ForestIndexedOperands.rowChildren rows).length
        (ForestIndexedOperands.rowGuards rows).length roots.length := by
  have dense : UniformDAGResources.program width n rows roots assignment =
      (ForestInputMetadata.fullCode width 0 ++
        (InputLoad.code n ++ UniformDAGLoop.code width (33 + 2 * n) 1
          (typedShapeNodeLayout n graph.nodeCount (ForestIndexedOperands.rowChildren rows).length
            (ForestIndexedOperands.rowGuards rows).length roots.length))).toArray := by
    unfold UniformDAGResources.program UniformDAGResources.code
    rw [typed_source_dense_layout_shape graph rows roots assignment matched]
  unfold typedSourceCode typedShapeCode
  rw [dense]
  dsimp only
  rw [typed_source_outer_shape graph rows roots matched]
  simp only [typedSourceScratch, UniformDAGRun.packetHeaderHeap_size, matched.length_eq]

/-- Concrete typed cold continuation at its actual low-register ABI. A raw
caller must reach this state by fetched setup and use relocation; this theorem
supplies the checked complete root driver rather than a runtime hypothesis. -/
def typedConeIncidenceSize (graph : DAG n) (root : Fin graph.nodeCount) : Nat :=
  ∑ node ∈ graph.cone root,
    (1 + (graph.node node).children.length + (graph.node node).guardLabels.length)

theorem typed_shape_cold_execution (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (assignment : Assignment n)
    (suffix output : List (Word (Nat.log 2 (graph.countedSize + 1) + 13)))
    (address loaded temporary : Word (Nat.log 2 (graph.countedSize + 1) + 13))
    (saved : Fin 8 → Word (Nat.log 2 (graph.countedSize + 1) + 13)) :
    ∃ final ticks peak,
      Execution (typedShapeCode (Nat.log 2 (graph.countedSize + 1) + 13) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length)
        (widenState
          ((ForestCounter.counterState (#[] : Array (Word (Nat.log 2 (graph.countedSize + 1) + 13)))
            0 address loaded temporary).frame
            ((ForestIndexedOperands.inputPacket n 0 rows roots).map (word (Nat.log 2 (graph.countedSize + 1) + 13)) ++
              List.ofFn (fun channel => boolWord (Nat.log 2 (graph.countedSize + 1) + 13) (assignment channel)) ++ suffix) output)
          saved)
        final ticks peak ∧
      ticks ≤ 142 * graph.countedSize +
        226 * (graph.roots.map (typedConeIncidenceSize graph)).sum + 44 ∧
      peak + programWords (typedShapeCode (Nat.log 2 (graph.countedSize + 1) + 13) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length) ≤
        38 * graph.countedSize + 1884 + suffix.length + output.length ∧
      final.stack = suffix ∧
      final.output = (graph.roots.map (fun node => boolWord (Nat.log 2 (graph.countedSize + 1) + 13)
        (graph.eval assignment node))).reverse ++ output ∧ final.halted = true := by
  obtain ⟨final, ticks, peak, trace, time, space, stored, stack, result, halted⟩ :=
    SparseConeReuse.cold_sparse_execution graph rows roots matched heads rootMatches assignment suffix output
      address loaded temporary saved
  change Execution (typedSourceCode _ graph rows roots assignment) _ final ticks peak at trace
  change peak + programWords (typedSourceCode _ graph rows roots assignment) ≤ _ at space
  rw [typed_source_code_shape graph rows roots assignment matched] at trace space
  exact ⟨final, ticks, peak, trace, time, space, stack, result, halted⟩


theorem typed_shape_resident_execution (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (assignment : Assignment n)
    (suffix output : List (Word (Nat.log 2 (graph.countedSize + 1) + 13)))
    (address loaded temporary : Word (Nat.log 2 (graph.countedSize + 1) + 13))
    (saved : Fin 8 → Word (Nat.log 2 (graph.countedSize + 1) + 13))
    (resident : Program (Nat.log 2 (graph.countedSize + 1) + 13) 8) (entry : Nat)
    (physical : ∀ index (valid : index <
      (typedShapeCode (Nat.log 2 (graph.countedSize + 1) + 13) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length).size),
      resident[entry + index]? = some (RawAdapterProgram.relocatedInstruction entry
        ((typedShapeCode (Nat.log 2 (graph.countedSize + 1) + 13) n graph.nodeCount
          (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length)[index]'valid)))
    (capacity : entry +
      (typedShapeCode (Nat.log 2 (graph.countedSize + 1) + 13) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length).size <
      2 ^ (Nat.log 2 (graph.countedSize + 1) + 13)) :
    ∃ final ticks peak,
      Execution resident
        (RawAdapterProgram.relocatedState entry (widenState
          ((ForestCounter.counterState (#[] : Array (Word (Nat.log 2 (graph.countedSize + 1) + 13)))
            0 address loaded temporary).frame
            ((ForestIndexedOperands.inputPacket n 0 rows roots).map (word (Nat.log 2 (graph.countedSize + 1) + 13)) ++
              List.ofFn (fun channel => boolWord (Nat.log 2 (graph.countedSize + 1) + 13) (assignment channel)) ++ suffix) output)
          saved)) final ticks peak ∧
      ticks ≤ 142 * graph.countedSize +
        226 * (graph.roots.map (typedConeIncidenceSize graph)).sum + 44 ∧
      peak + programWords (typedShapeCode (Nat.log 2 (graph.countedSize + 1) + 13) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length) ≤
        38 * graph.countedSize + 1884 + suffix.length + output.length ∧
      final.stack = suffix ∧
      final.output = (graph.roots.map (fun node => boolWord (Nat.log 2 (graph.countedSize + 1) + 13)
        (graph.eval assignment node))).reverse ++ output ∧ final.halted = true := by
  obtain ⟨final, ticks, peak, trace, time, space, stack, result, halted⟩ :=
    typed_shape_cold_execution graph rows roots matched heads rootMatches assignment suffix output
      address loaded temporary saved
  have moved := RawAdapterProgram.relocated_execution resident _ entry physical capacity trace
  exact ⟨RawAdapterProgram.relocatedState entry final, ticks, peak, moved,
    time, space, stack, result, halted⟩

abbrev typedExecutionWidth (graph : DAG n) : Nat := Nat.log 2 (graph.countedSize + 1) + 13

def typedPacketWords (graph : DAG n) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) : List (Word (typedExecutionWidth graph)) :=
  (ForestIndexedOperands.inputPacket n 0 rows roots).map (word (typedExecutionWidth graph))

/-- Fetched packet transfers continue into the complete typed evaluator and
ordered root driver on the same machine, reaching the emitted result and halt. -/
theorem copied_packet_cold_execution (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (assignment : Assignment n)
    (suffix : List (Word (typedExecutionWidth graph)))
    (resident : Program (typedExecutionWidth graph) 8)
    (nodes base origin recoverEntry saveSetupEntry saveEntry releaseSetupEntry releaseEntry handoffEntry typedEntry : Nat)
    (state : State (typedExecutionWidth graph) 8)
    (recoverPhysical : ∀ phase : Fin 2, resident[recoverEntry + phase.val]? =
      (typedOriginRecoverCode (typedExecutionWidth graph) nodes base)[phase.val]?)
    (setupPhysical : ∀ phase : Fin 8, resident[saveSetupEntry + phase.val]? =
      (typedSaveSetupCode (typedExecutionWidth graph) (typedPacketWords graph rows roots).length saveEntry)[phase.val]?)
    (savePhysical : RawTransferLoops.CodeAt resident saveEntry
      (RawTransferLoops.reverseSaveCode (typedExecutionWidth graph) saveEntry releaseSetupEntry))
    (releaseSetupPhysical : ∀ phase : Fin 2, resident[releaseSetupEntry + phase.val]? =
      (typedReleaseSetupCode (typedExecutionWidth graph) releaseEntry)[phase.val]?)
    (releasePhysical : RawTransferLoops.CodeAt resident releaseEntry
      (RawTransferLoops.countedReleaseCode (typedExecutionWidth graph) releaseEntry handoffEntry))
    (handoffPhysical : ∀ phase : Fin 2, resident[handoffEntry + phase.val]? =
      (typedColdHandoffCode (typedExecutionWidth graph) typedEntry)[phase.val]?)
    (coldPhysical : ∀ index (valid : index <
      (typedShapeCode (typedExecutionWidth graph) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length).size),
      resident[typedEntry + index]? = some (RawAdapterProgram.relocatedInstruction typedEntry
        ((typedShapeCode (typedExecutionWidth graph) n graph.nodeCount
          (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length)[index]'valid)))
    (recoverNext : recoverEntry + 2 = saveSetupEntry)
    (position : state.pc = word (typedExecutionWidth graph) recoverEntry)
    (running : state.halted = false)
    (recoverFits : recoverEntry + 2 < 2 ^ typedExecutionWidth graph)
    (setupFits : saveSetupEntry + 8 < 2 ^ typedExecutionWidth graph)
    (saveFits : saveEntry + 6 < 2 ^ typedExecutionWidth graph)
    (releaseSetupFits : releaseSetupEntry + 2 < 2 ^ typedExecutionWidth graph)
    (releaseFits : releaseEntry + 4 < 2 ^ typedExecutionWidth graph)
    (handoffFits : handoffEntry + 2 < 2 ^ typedExecutionWidth graph)
    (coldFits : typedEntry +
      (typedShapeCode (typedExecutionWidth graph) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length).size <
      2 ^ typedExecutionWidth graph)
    (originPositive : 0 < origin)
    (packetPositive : 0 < (typedPacketWords graph rows roots).length)
    (room : origin + (typedPacketWords graph rows roots).length < 2 ^ typedExecutionWidth graph)
    (allocation : state.heap.size = origin + (typedPacketWords graph rows roots).length)
    (slotFits : Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base < 2 ^ typedExecutionWidth graph)
    (originCell : state.heap[Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base]? =
      some (word (typedExecutionWidth graph) origin))
    (cells : CopiedPacketCells state.heap origin (typedPacketWords graph rows roots))
    (inputStack : state.stack =
      List.ofFn (fun channel => boolWord (typedExecutionWidth graph) (assignment channel)) ++ suffix) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 6 * (typedPacketWords graph rows roots).length + 4 * state.heap.size +
        142 * graph.countedSize + 226 * (graph.roots.map (typedConeIncidenceSize graph)).sum + 60 ∧
      peak ≤ max (state.liveWords + (typedPacketWords graph rows roots).length)
        (38 * graph.countedSize + 1884 + suffix.length + state.output.length) ∧
      final.stack = suffix ∧
      final.output = (graph.roots.map (fun node => boolWord (typedExecutionWidth graph)
        (graph.eval assignment node))).reverse ++ state.output ∧ final.halted = true := by
  obtain ⟨released, transferPeak, transfer, transferBound, empty, savedStack,
      savedOutput, releasedPC, releasedRunning, releasedZero⟩ :=
    typed_packet_save_release_execution resident nodes base origin recoverEntry saveSetupEntry saveEntry
      releaseSetupEntry releaseEntry handoffEntry (typedPacketWords graph rows roots) state
      recoverPhysical setupPhysical savePhysical releaseSetupPhysical releasePhysical recoverNext
      position running recoverFits setupFits saveFits releaseSetupFits releaseFits originPositive
      packetPositive room allocation slotFits originCell cells
  obtain ⟨ready, handoff, readyEq⟩ :=
    typed_cold_handoff_execution resident handoffEntry typedEntry released handoffPhysical
      releasedPC releasedRunning handoffFits releasedZero empty
  have readyStart : ready = RawAdapterProgram.relocatedState typedEntry (widenState
      ((ForestCounter.counterState (#[] : Array (Word (typedExecutionWidth graph))) 0
        (released.reg 0) (released.reg 1) (released.reg 2)).frame
        ((typedPacketWords graph rows roots) ++
          List.ofFn (fun channel => boolWord (typedExecutionWidth graph) (assignment channel)) ++ suffix)
        state.output) released.reg) := by
    rw [readyEq, savedStack, inputStack, savedOutput]
    simp only [List.append_assoc, RawAdapterProgram.relocatedState,
      widenState, ForestCounter.counterState, Controller.Cost.State.frame, word,
      Nat.zero_mod, Nat.zero_add]
  obtain ⟨final, coldTicks, coldPeak, cold, coldTime, coldSpace, finalStack, finalOutput, finalHalted⟩ :=
    typed_shape_resident_execution graph rows roots matched heads rootMatches assignment suffix state.output
      (released.reg 0) (released.reg 1) (released.reg 2) released.reg resident typedEntry coldPhysical coldFits
  have coldFromReady : Execution resident ready final coldTicks coldPeak := by
    rw [readyStart]
    exact cold
  have releasedLive : released.liveWords ≤ transferPeak := Execution.final_storage_le transfer
  have readyLive : ready.liveWords ≤ released.liveWords := Execution.final_storage_le handoff
  have coldBound : coldPeak ≤ 38 * graph.countedSize + 1884 + suffix.length + state.output.length := by
    omega
  have joined := (transfer.append handoff).append coldFromReady
  refine ⟨final, _, _, joined, ?_, ?_, finalStack, finalOutput, finalHalted⟩
  · omega
  · simp only [max_le_iff]
    constructor
    · constructor
      · exact le_trans transferBound (le_max_left _ _)
      · exact le_trans (le_trans releasedLive transferBound) (le_max_left _ _)
    · exact le_trans coldBound (le_max_right _ _)

theorem numbered_cold_input_words (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    numberedPacketWords (width := width) raw valid numbering =
      (ForestIndexedOperands.inputPacket channels 0 (numberedRows raw valid numbering)
        (numbering.toDAG.roots.map Fin.val)).map (word width) := by
  exact (numbered_packet_image raw valid numbering).trans
    (ForestIndexedOperands.matched_cold_input_words numbering.toDAG
      (numberedRows raw valid numbering) (numbering.toDAG.roots.map Fin.val)
      (numbered_rows_match raw valid numbering) rfl).symm

theorem numbered_output_original (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (assignment : Assignment channels) :
    numbering.toDAG.outputValues assignment =
      (raw.toUnordered valid).roots.map (numbering.values assignment) :=
  numbering.outputValues_eq assignment _ (numbering.values_evaluate assignment)

theorem typed_input_length (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots) :
    (typedPacketWords graph rows roots).length =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length := by
  have exactInput := ForestIndexedOperands.matched_cold_input_words
    (width := typedExecutionWidth graph) graph rows roots matched rootMatches
  have length := ForestIndexedOperands.matched_packet_length 5 graph rows roots matched rootMatches
  unfold typedPacketWords
  rw [exactInput, List.length_append, List.length_map, length]
  simp only [List.length_cons, List.length_nil]
  omega


def typedRuntimeSaveSetupCode (width saveEntry : Nat) : Program width 8 :=
  #[.constant 1 (word width 1),
    .add 1 4 1,
    .load 0 1,
    .add 0 0 0,
    .copy 3 0,
    .add 0 0 0,
    .add 0 0 3,
    .constant 3 (word width 5),
    .add 0 0 3,
    .constant 1 (word width 2),
    .add 1 4 1,
    .load 3 1,
    .add 0 0 3,
    .constant 3 (word width 1),
    .add 1 1 3,
    .load 3 1,
    .add 0 0 3,
    .constant 3 (word width 1),
    .add 1 1 3,
    .load 3 1,
    .add 0 0 3,
    .add 2 4 0,
    .add 1 2 7,
    .branchZero 6 (word width saveEntry)]

theorem typed_runtime_save_setup_execution (resident : Program width 8)
    (entry saveEntry origin nodes children guards roots : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 24, resident[entry + phase.val]? =
      (typedRuntimeSaveSetupCode width saveEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 24 < 2 ^ width)
    (room : origin + (5 + 6 * nodes + children + guards + roots) < 2 ^ width)
    (originHeld : state.reg 4 = word width origin)
    (zeroHeld : state.reg 6 = word width 0) (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (nodeCell : state.heap[origin + 1]? = some (word width nodes))
    (childCell : state.heap[origin + 2]? = some (word width children))
    (guardCell : state.heap[origin + 3]? = some (word width guards))
    (rootCell : state.heap[origin + 4]? = some (word width roots)) :
    ∃ final, Execution resident state final 24 state.liveWords ∧
      final.pc = word width saveEntry ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width (5 + 6 * nodes + children + guards + roots) ∧
      final.reg 1 = word width (origin + (5 + 6 * nodes + children + guards + roots) - 1) ∧
      final.reg 2 = word width (origin + (5 + 6 * nodes + children + guards + roots)) ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) := by
  let s1 : State width 8 := { state with reg := copyRegisters (state.reg 0) (word width (1)) (state.reg 2) (state.reg 3) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 1), halted := false }
  let s2 : State width 8 := { state with reg := copyRegisters (state.reg 0) (word width ((origin) + (1))) (state.reg 2) (state.reg 3) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 2), halted := false }
  let s3 : State width 8 := { state with reg := copyRegisters (word width (nodes)) (word width ((origin) + (1))) (state.reg 2) (state.reg 3) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 3), halted := false }
  let s4 : State width 8 := { state with reg := copyRegisters (word width ((nodes) + (nodes))) (word width ((origin) + (1))) (state.reg 2) (state.reg 3) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 4), halted := false }
  let s5 : State width 8 := { state with reg := copyRegisters (word width ((nodes) + (nodes))) (word width ((origin) + (1))) (state.reg 2) (word width ((nodes) + (nodes))) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 5), halted := false }
  let s6 : State width 8 := { state with reg := copyRegisters (word width (((nodes) + (nodes)) + ((nodes) + (nodes)))) (word width ((origin) + (1))) (state.reg 2) (word width ((nodes) + (nodes))) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 6), halted := false }
  let s7 : State width 8 := { state with reg := copyRegisters (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes)))) (word width ((origin) + (1))) (state.reg 2) (word width ((nodes) + (nodes))) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 7), halted := false }
  let s8 : State width 8 := { state with reg := copyRegisters (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes)))) (word width ((origin) + (1))) (state.reg 2) (word width (5)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 8), halted := false }
  let s9 : State width 8 := { state with reg := copyRegisters (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) (word width ((origin) + (1))) (state.reg 2) (word width (5)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 9), halted := false }
  let s10 : State width 8 := { state with reg := copyRegisters (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) (word width (2)) (state.reg 2) (word width (5)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 10), halted := false }
  let s11 : State width 8 := { state with reg := copyRegisters (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) (word width ((origin) + (2))) (state.reg 2) (word width (5)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 11), halted := false }
  let s12 : State width 8 := { state with reg := copyRegisters (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) (word width ((origin) + (2))) (state.reg 2) (word width (children)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 12), halted := false }
  let s13 : State width 8 := { state with reg := copyRegisters (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) (word width ((origin) + (2))) (state.reg 2) (word width (children)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 13), halted := false }
  let s14 : State width 8 := { state with reg := copyRegisters (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) (word width ((origin) + (2))) (state.reg 2) (word width (1)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 14), halted := false }
  let s15 : State width 8 := { state with reg := copyRegisters (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) (word width (((origin) + (2)) + (1))) (state.reg 2) (word width (1)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 15), halted := false }
  let s16 : State width 8 := { state with reg := copyRegisters (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) (word width (((origin) + (2)) + (1))) (state.reg 2) (word width (guards)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 16), halted := false }
  let s17 : State width 8 := { state with reg := copyRegisters (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) (word width (((origin) + (2)) + (1))) (state.reg 2) (word width (guards)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 17), halted := false }
  let s18 : State width 8 := { state with reg := copyRegisters (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) (word width (((origin) + (2)) + (1))) (state.reg 2) (word width (1)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 18), halted := false }
  let s19 : State width 8 := { state with reg := copyRegisters (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) (word width ((((origin) + (2)) + (1)) + (1))) (state.reg 2) (word width (1)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 19), halted := false }
  let s20 : State width 8 := { state with reg := copyRegisters (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) (word width ((((origin) + (2)) + (1)) + (1))) (state.reg 2) (word width (roots)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 20), halted := false }
  let s21 : State width 8 := { state with reg := copyRegisters (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) (word width ((((origin) + (2)) + (1)) + (1))) (state.reg 2) (word width (roots)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 21), halted := false }
  let s22 : State width 8 := { state with reg := copyRegisters (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) (word width ((((origin) + (2)) + (1)) + (1))) (word width ((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots)))) (word width (roots)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 22), halted := false }
  let s23 : State width 8 := { state with reg := copyRegisters (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) (word width (((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) + (2 ^ width - 1))) (word width ((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots)))) (word width (roots)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 23), halted := false }
  let s24 : State width 8 := { state with reg := copyRegisters (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) (word width (((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) + (2 ^ width - 1))) (word width ((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots)))) (word width (roots)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (saveEntry), halted := false }
  have pc0 : state.pc = word width (entry + 0) := by simpa only [Nat.add_zero] using position
  have run1 : state.halted = false := by exact running
  have e1 : state.advance.put 1 (word width (1)) = s1 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> simp [s1, copyRegisters, State.advance, State.put, originHeld, zeroHeld, maskHeld]
    · rfl
    · rfl
    · rfl
    · simpa only [s1, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC state (entry + 0) pc0 (by omega)
    · exact running
  have t1 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 1 (word width 1)) pc0 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨0, by decide⟩)]
    rw [← e1]
    exact copy_constant_step state 1 (word width (1)) run1
  have pc1 : s1.pc = word width (entry + 1) := rfl
  have run2 : s1.halted = false := rfl
  have e2 : s1.advance.put 1 (word width ((origin) + (1))) = s2 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (state.reg 0) (word width (1)) (state.reg 2) (state.reg 3) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((origin) + (1)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s1 (entry + 1) pc1 (by omega)
    · rfl
  have t2 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.add 1 4 1) pc1 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨1, by decide⟩)]
    rw [← e2]
    exact copy_add_step s1 1 4 1 (origin) (1) run2 (by omega) (by omega) (by simp [s1, copyRegisters]) (by simp [s1, copyRegisters])
  have pc2 : s2.pc = word width (entry + 2) := rfl
  have run3 : s2.halted = false := rfl
  have e3 : s2.advance.put 0 (word width (nodes)) = s3 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (state.reg 0) (word width ((origin) + (1))) (state.reg 2) (state.reg 3) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (nodes))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s2 (entry + 2) pc2 (by omega)
    · rfl
  have t3 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 0 1) pc2 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨2, by decide⟩)]
    rw [← e3]
    exact copy_load_step s2 0 1 (origin + 1) (word width (nodes)) run3 (by omega)
      (by simp [s2, copyRegisters] <;> congr 1 <;> omega) (by simpa only [s2] using nodeCell)
  have pc3 : s3.pc = word width (entry + 3) := rfl
  have run4 : s3.halted = false := rfl
  have e4 : s3.advance.put 0 (word width ((nodes) + (nodes))) = s4 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (nodes)) (word width ((origin) + (1))) (state.reg 2) (state.reg 3) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((nodes) + (nodes)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s4, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s3 (entry + 3) pc3 (by omega)
    · rfl
  have t4 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.add 0 0 0) pc3 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨3, by decide⟩)]
    rw [← e4]
    exact copy_add_step s3 0 0 0 (nodes) (nodes) run4 (by omega) (by omega) (by simp [s3, copyRegisters]) (by simp [s3, copyRegisters])
  have pc4 : s4.pc = word width (entry + 4) := rfl
  have run5 : s4.halted = false := rfl
  have e5 : s4.advance.put 3 (word width ((nodes) + (nodes))) = s5 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width ((nodes) + (nodes))) (word width ((origin) + (1))) (state.reg 2) (state.reg 3) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((nodes) + (nodes)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s5, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s4 (entry + 4) pc4 (by omega)
    · rfl
  have t5 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.copy 3 0) pc4 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨4, by decide⟩)]
    rw [← e5]
    exact copy_copy_step s4 3 0 (word width ((nodes) + (nodes))) run5 (by simp [s4, copyRegisters])
  have pc5 : s5.pc = word width (entry + 5) := rfl
  have run6 : s5.halted = false := rfl
  have e6 : s5.advance.put 0 (word width (((nodes) + (nodes)) + ((nodes) + (nodes)))) = s6 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width ((nodes) + (nodes))) (word width ((origin) + (1))) (state.reg 2) (word width ((nodes) + (nodes))) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (((nodes) + (nodes)) + ((nodes) + (nodes))))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s6, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s5 (entry + 5) pc5 (by omega)
    · rfl
  have t6 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 0 0 0) pc5 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨5, by decide⟩)]
    rw [← e6]
    exact copy_add_step s5 0 0 0 ((nodes) + (nodes)) ((nodes) + (nodes)) run6 (by omega) (by omega) (by simp [s5, copyRegisters]) (by simp [s5, copyRegisters])
  have pc6 : s6.pc = word width (entry + 6) := rfl
  have run7 : s6.halted = false := rfl
  have e7 : s6.advance.put 0 (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes)))) = s7 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (((nodes) + (nodes)) + ((nodes) + (nodes)))) (word width ((origin) + (1))) (state.reg 2) (word width ((nodes) + (nodes))) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s7, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s6 (entry + 6) pc6 (by omega)
    · rfl
  have t7 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.add 0 0 3) pc6 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨6, by decide⟩)]
    rw [← e7]
    exact copy_add_step s6 0 0 3 (((nodes) + (nodes)) + ((nodes) + (nodes))) ((nodes) + (nodes)) run7 (by omega) (by omega) (by simp [s6, copyRegisters]) (by simp [s6, copyRegisters])
  have pc7 : s7.pc = word width (entry + 7) := rfl
  have run8 : s7.halted = false := rfl
  have e8 : s7.advance.put 3 (word width (5)) = s8 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes)))) (word width ((origin) + (1))) (state.reg 2) (word width ((nodes) + (nodes))) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (5))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s8, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s7 (entry + 7) pc7 (by omega)
    · rfl
  have t8 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.constant 3 (word width 5)) pc7 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨7, by decide⟩)]
    rw [← e8]
    exact copy_constant_step s7 3 (word width (5)) run8
  have pc8 : s8.pc = word width (entry + 8) := rfl
  have run9 : s8.halted = false := rfl
  have e9 : s8.advance.put 0 (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) = s9 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes)))) (word width ((origin) + (1))) (state.reg 2) (word width (5)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s9, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s8 (entry + 8) pc8 (by omega)
    · rfl
  have t9 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.add 0 0 3) pc8 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨8, by decide⟩)]
    rw [← e9]
    exact copy_add_step s8 0 0 3 ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) (5) run9 (by omega) (by omega) (by simp [s8, copyRegisters]) (by simp [s8, copyRegisters])
  have pc9 : s9.pc = word width (entry + 9) := rfl
  have run10 : s9.halted = false := rfl
  have e10 : s9.advance.put 1 (word width (2)) = s10 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) (word width ((origin) + (1))) (state.reg 2) (word width (5)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (2))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s10, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s9 (entry + 9) pc9 (by omega)
    · rfl
  have t10 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.constant 1 (word width 2)) pc9 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨9, by decide⟩)]
    rw [← e10]
    exact copy_constant_step s9 1 (word width (2)) run10
  have pc10 : s10.pc = word width (entry + 10) := rfl
  have run11 : s10.halted = false := rfl
  have e11 : s10.advance.put 1 (word width ((origin) + (2))) = s11 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) (word width (2)) (state.reg 2) (word width (5)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((origin) + (2)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s11, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s10 (entry + 10) pc10 (by omega)
    · rfl
  have t11 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.add 1 4 1) pc10 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨10, by decide⟩)]
    rw [← e11]
    exact copy_add_step s10 1 4 1 (origin) (2) run11 (by omega) (by omega) (by simp [s10, copyRegisters]) (by simp [s10, copyRegisters])
  have pc11 : s11.pc = word width (entry + 11) := rfl
  have run12 : s11.halted = false := rfl
  have e12 : s11.advance.put 3 (word width (children)) = s12 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) (word width ((origin) + (2))) (state.reg 2) (word width (5)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (children))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s12, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s11 (entry + 11) pc11 (by omega)
    · rfl
  have t12 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.load 3 1) pc11 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨11, by decide⟩)]
    rw [← e12]
    exact copy_load_step s11 3 1 (origin + 2) (word width (children)) run12 (by omega)
      (by simp [s11, copyRegisters] <;> congr 1 <;> omega) (by simpa only [s11] using childCell)
  have pc12 : s12.pc = word width (entry + 12) := rfl
  have run13 : s12.halted = false := rfl
  have e13 : s12.advance.put 0 (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) = s13 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5))) (word width ((origin) + (2))) (state.reg 2) (word width (children)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s13, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s12 (entry + 12) pc12 (by omega)
    · rfl
  have t13 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.add 0 0 3) pc12 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨12, by decide⟩)]
    rw [← e13]
    exact copy_add_step s12 0 0 3 (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) (children) run13 (by omega) (by omega) (by simp [s12, copyRegisters]) (by simp [s12, copyRegisters])
  have pc13 : s13.pc = word width (entry + 13) := rfl
  have run14 : s13.halted = false := rfl
  have e14 : s13.advance.put 3 (word width (1)) = s14 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) (word width ((origin) + (2))) (state.reg 2) (word width (children)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s14, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s13 (entry + 13) pc13 (by omega)
    · rfl
  have t14 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.constant 3 (word width 1)) pc13 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨13, by decide⟩)]
    rw [← e14]
    exact copy_constant_step s13 3 (word width (1)) run14
  have pc14 : s14.pc = word width (entry + 14) := rfl
  have run15 : s14.halted = false := rfl
  have e15 : s14.advance.put 1 (word width (((origin) + (2)) + (1))) = s15 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) (word width ((origin) + (2))) (state.reg 2) (word width (1)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (((origin) + (2)) + (1)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s15, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s14 (entry + 14) pc14 (by omega)
    · rfl
  have t15 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.add 1 1 3) pc14 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨14, by decide⟩)]
    rw [← e15]
    exact copy_add_step s14 1 1 3 ((origin) + (2)) (1) run15 (by omega) (by omega) (by simp [s14, copyRegisters]) (by simp [s14, copyRegisters])
  have pc15 : s15.pc = word width (entry + 15) := rfl
  have run16 : s15.halted = false := rfl
  have e16 : s15.advance.put 3 (word width (guards)) = s16 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) (word width (((origin) + (2)) + (1))) (state.reg 2) (word width (1)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (guards))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s16, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s15 (entry + 15) pc15 (by omega)
    · rfl
  have t16 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.load 3 1) pc15 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨15, by decide⟩)]
    rw [← e16]
    exact copy_load_step s15 3 1 (origin + 3) (word width (guards)) run16 (by omega)
      (by simp [s15, copyRegisters] <;> congr 1 <;> omega) (by simpa only [s15] using guardCell)
  have pc16 : s16.pc = word width (entry + 16) := rfl
  have run17 : s16.halted = false := rfl
  have e17 : s16.advance.put 0 (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) = s17 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children))) (word width (((origin) + (2)) + (1))) (state.reg 2) (word width (guards)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s17, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s16 (entry + 16) pc16 (by omega)
    · rfl
  have t17 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.add 0 0 3) pc16 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨16, by decide⟩)]
    rw [← e17]
    exact copy_add_step s16 0 0 3 ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) (guards) run17 (by omega) (by omega) (by simp [s16, copyRegisters]) (by simp [s16, copyRegisters])
  have pc17 : s17.pc = word width (entry + 17) := rfl
  have run18 : s17.halted = false := rfl
  have e18 : s17.advance.put 3 (word width (1)) = s18 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) (word width (((origin) + (2)) + (1))) (state.reg 2) (word width (guards)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s18, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s17 (entry + 17) pc17 (by omega)
    · rfl
  have t18 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 17) (.constant 3 (word width 1)) pc17 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨17, by decide⟩)]
    rw [← e18]
    exact copy_constant_step s17 3 (word width (1)) run18
  have pc18 : s18.pc = word width (entry + 18) := rfl
  have run19 : s18.halted = false := rfl
  have e19 : s18.advance.put 1 (word width ((((origin) + (2)) + (1)) + (1))) = s19 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) (word width (((origin) + (2)) + (1))) (state.reg 2) (word width (1)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((((origin) + (2)) + (1)) + (1)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s19, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s18 (entry + 18) pc18 (by omega)
    · rfl
  have t19 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 18) (.add 1 1 3) pc18 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨18, by decide⟩)]
    rw [← e19]
    exact copy_add_step s18 1 1 3 (((origin) + (2)) + (1)) (1) run19 (by omega) (by omega) (by simp [s18, copyRegisters]) (by simp [s18, copyRegisters])
  have pc19 : s19.pc = word width (entry + 19) := rfl
  have run20 : s19.halted = false := rfl
  have e20 : s19.advance.put 3 (word width (roots)) = s20 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) (word width ((((origin) + (2)) + (1)) + (1))) (state.reg 2) (word width (1)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (roots))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s20, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s19 (entry + 19) pc19 (by omega)
    · rfl
  have t20 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 19) (.load 3 1) pc19 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨19, by decide⟩)]
    rw [← e20]
    exact copy_load_step s19 3 1 (origin + 4) (word width (roots)) run20 (by omega)
      (by simp [s19, copyRegisters] <;> congr 1 <;> omega) (by simpa only [s19] using rootCell)
  have pc20 : s20.pc = word width (entry + 20) := rfl
  have run21 : s20.halted = false := rfl
  have e21 : s20.advance.put 0 (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) = s21 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards))) (word width ((((origin) + (2)) + (1)) + (1))) (state.reg 2) (word width (roots)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s21, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s20 (entry + 20) pc20 (by omega)
    · rfl
  have t21 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 20) (.add 0 0 3) pc20 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨20, by decide⟩)]
    rw [← e21]
    exact copy_add_step s20 0 0 3 (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) (roots) run21 (by omega) (by omega) (by simp [s20, copyRegisters]) (by simp [s20, copyRegisters])
  have pc21 : s21.pc = word width (entry + 21) := rfl
  have run22 : s21.halted = false := rfl
  have e22 : s21.advance.put 2 (word width ((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots)))) = s22 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) (word width ((((origin) + (2)) + (1)) + (1))) (state.reg 2) (word width (roots)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width ((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s22, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s21 (entry + 21) pc21 (by omega)
    · rfl
  have t22 : programStep resident s21 = some s22 := by
    rw [fetched resident s21 (entry + 21) (.add 2 4 0) pc21 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨21, by decide⟩)]
    rw [← e22]
    exact copy_add_step s21 2 4 0 (origin) ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots)) run22 (by omega) (by omega) (by simp [s21, copyRegisters]) (by simp [s21, copyRegisters])
  have pc22 : s22.pc = word width (entry + 22) := rfl
  have run23 : s22.halted = false := rfl
  have e23 : s22.advance.put 1 (word width (((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) + (2 ^ width - 1))) = s23 := by
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) (word width ((((origin) + (2)) + (1)) + (1))) (word width ((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots)))) (word width (roots)) (word width (origin)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) + (2 ^ width - 1)))) register
    · rfl
    · rfl
    · rfl
    · simpa only [s23, State.put, Nat.add_assoc, Nat.reduceAdd] using
        referenceAdvancePC s22 (entry + 22) pc22 (by omega)
    · rfl
  have t23 : programStep resident s22 = some s23 := by
    rw [fetched resident s22 (entry + 22) (.add 1 2 7) pc22 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨22, by decide⟩)]
    rw [← e23]
    exact copy_add_step s22 1 2 7 ((origin) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (5)) + (children)) + (guards)) + (roots))) (2 ^ width - 1) run23 (by omega) (by omega) (by simp [s22, copyRegisters]) (by simp [s22, copyRegisters])
  have pc23 : s23.pc = word width (entry + 23) := rfl
  have run24 : s23.halted = false := rfl
  have e24 : { s23.advance with pc := word width saveEntry } = s24 := by
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have t24 : programStep resident s23 = some s24 := by
    rw [fetched resident s23 (entry + 23) (.branchZero 6 (word width saveEntry)) pc23 (by omega)
      (by simpa [typedRuntimeSaveSetupCode] using physical ⟨23, by decide⟩)]
    rw [← e24]
    exact copy_branch_zero s23 6 saveEntry run24 (by simp [s23, copyRegisters])
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.cons t21 (Execution.cons t22 (Execution.cons t23 (Execution.cons t24 (Execution.refl s24))))))))))))))))))))))))
  have live1 : s1.liveWords = state.liveWords := rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have live4 : s4.liveWords = state.liveWords := rfl
  have live5 : s5.liveWords = state.liveWords := rfl
  have live6 : s6.liveWords = state.liveWords := rfl
  have live7 : s7.liveWords = state.liveWords := rfl
  have live8 : s8.liveWords = state.liveWords := rfl
  have live9 : s9.liveWords = state.liveWords := rfl
  have live10 : s10.liveWords = state.liveWords := rfl
  have live11 : s11.liveWords = state.liveWords := rfl
  have live12 : s12.liveWords = state.liveWords := rfl
  have live13 : s13.liveWords = state.liveWords := rfl
  have live14 : s14.liveWords = state.liveWords := rfl
  have live15 : s15.liveWords = state.liveWords := rfl
  have live16 : s16.liveWords = state.liveWords := rfl
  have live17 : s17.liveWords = state.liveWords := rfl
  have live18 : s18.liveWords = state.liveWords := rfl
  have live19 : s19.liveWords = state.liveWords := rfl
  have live20 : s20.liveWords = state.liveWords := rfl
  have live21 : s21.liveWords = state.liveWords := rfl
  have live22 : s22.liveWords = state.liveWords := rfl
  have live23 : s23.liveWords = state.liveWords := rfl
  have live24 : s24.liveWords = state.liveWords := rfl
  refine ⟨s24, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, live22, live23, live24, max_self, Nat.reduceAdd] using trace
  all_goals simp [s24, copyRegisters]
  · congr 1 <;> omega
  · rw [marker_word_decrement _ (by omega) (by omega)]
    congr 1 <;> omega
  · congr 1 <;> omega

theorem typed_packet_runtime_save_release_execution (resident : Program width 8)
    (nodes countNodes children guards roots base origin recoverEntry saveSetupEntry saveEntry releaseSetupEntry releaseEntry done : Nat)
    (packet : List (Word width)) (state : State width 8)
    (recoverPhysical : ∀ phase : Fin 2, resident[recoverEntry + phase.val]? =
      (typedOriginRecoverCode width nodes base)[phase.val]?)
    (setupPhysical : ∀ phase : Fin 24, resident[saveSetupEntry + phase.val]? =
      (typedRuntimeSaveSetupCode width saveEntry)[phase.val]?)
    (savePhysical : RawTransferLoops.CodeAt resident saveEntry
      (RawTransferLoops.reverseSaveCode width saveEntry releaseSetupEntry))
    (releaseSetupPhysical : ∀ phase : Fin 2, resident[releaseSetupEntry + phase.val]? =
      (typedReleaseSetupCode width releaseEntry)[phase.val]?)
    (releasePhysical : RawTransferLoops.CodeAt resident releaseEntry
      (RawTransferLoops.countedReleaseCode width releaseEntry done))
    (recoverNext : recoverEntry + 2 = saveSetupEntry)
    (position : state.pc = word width recoverEntry) (running : state.halted = false)
    (recoverFits : recoverEntry + 2 < 2 ^ width) (setupFits : saveSetupEntry + 24 < 2 ^ width)
    (saveFits : saveEntry + 6 < 2 ^ width)
    (releaseSetupFits : releaseSetupEntry + 2 < 2 ^ width)
    (releaseFits : releaseEntry + 4 < 2 ^ width)
    (originPositive : 0 < origin) (packetPositive : 0 < packet.length)
    (room : origin + packet.length < 2 ^ width)
    (allocation : state.heap.size = origin + packet.length)
    (slotFits : Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base < 2 ^ width)
    (originCell : state.heap[Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base]? =
      some (word width origin))
    (packetLength : packet.length = 5 + 6 * countNodes + children + guards + roots)
    (zeroHeld : state.reg 6 = word width 0) (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (nodeCell : state.heap[origin + 1]? = some (word width countNodes))
    (childCell : state.heap[origin + 2]? = some (word width children))
    (guardCell : state.heap[origin + 3]? = some (word width guards))
    (rootCell : state.heap[origin + 4]? = some (word width roots))
    (cells : CopiedPacketCells state.heap origin packet) :
    ∃ final peak, Execution resident state final
      (6 * packet.length + 4 * state.heap.size + 30) peak ∧
      peak ≤ state.liveWords + packet.length ∧
      final.heap = #[] ∧ final.stack = packet ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 6 = word width 0 := by
  obtain ⟨recovered, tr, pcr, runr, hr, sr, outr, originHeld, retainedr⟩ :=
    typed_origin_recover_execution resident nodes base recoverEntry origin state recoverPhysical
      position running recoverFits slotFits originCell
  have recoveredZero : recovered.reg 6 = word width 0 := (retainedr 6 (by decide)).trans zeroHeld
  have recoveredMask : recovered.reg 7 = word width (2 ^ width - 1) := (retainedr 7 (by decide)).trans maskHeld
  obtain ⟨setup, ts, pcs, runs, hs, ss, outs, countRaw, cursorRaw, totalRaw, zeros, masks⟩ :=
    typed_runtime_save_setup_execution resident saveSetupEntry saveEntry origin countNodes children guards roots recovered
      setupPhysical (by simpa only [recoverNext] using pcr) runr setupFits
      (by simpa only [← packetLength] using room) originHeld recoveredZero recoveredMask
      (by simpa only [hr] using nodeCell) (by simpa only [hr] using childCell)
      (by simpa only [hr] using guardCell) (by simpa only [hr] using rootCell)
  have counts : setup.reg 0 = word width packet.length := by simpa only [← packetLength] using countRaw
  have cursors : setup.reg 1 = word width (origin + packet.length - 1) := by simpa only [← packetLength] using cursorRaw
  have totals : setup.reg 2 = word width (origin + packet.length) := by simpa only [← packetLength] using totalRaw
  have copied : ∀ index : Nat, ∀ bound : index < packet.length,
      setup.heap[origin + index]? = some packet[index] := by
    intro index bound
    rw [hs, hr]
    exact cells ⟨index, bound⟩
  obtain ⟨saved, savePeak, tv, bv, hv, sv, outv, pcv, runv, countv, retainedv⟩ :=
    RawTransferLoops.reverse_save_execution resident saveEntry releaseSetupEntry origin packet setup
      pcs runs saveFits originPositive room (by omega) counts cursors masks zeros copied savePhysical
  have totalv : saved.reg 2 = word width (origin + packet.length) :=
    (retainedv 2 (by decide) (by decide) (by decide)).trans totals
  have zerov : saved.reg 6 = word width 0 :=
    (retainedv 6 (by decide) (by decide) (by decide)).trans zeros
  have maskv : saved.reg 7 = word width (2 ^ width - 1) :=
    (retainedv 7 (by decide) (by decide) (by decide)).trans masks
  obtain ⟨releaseSetup, tu, pcu, runu, hu, su, outu, countu, retainedu⟩ :=
    typed_release_setup_execution resident releaseSetupEntry releaseEntry (origin + packet.length)
      saved releaseSetupPhysical pcv runv releaseSetupFits room totalv zerov
  have heapu : releaseSetup.heap.size = origin + packet.length := by
    rw [hu, hv, hs, hr]
    exact allocation
  have masku : releaseSetup.reg 7 = word width (2 ^ width - 1) :=
    (retainedu 7 (by decide)).trans maskv
  have zerou : releaseSetup.reg 6 = word width 0 :=
    (retainedu 6 (by decide)).trans zerov
  obtain ⟨final, releasePeak, tf, bf, hf, sf, outf, pcf, runf, countf, retainedf⟩ :=
    RawTransferLoops.counted_release_execution resident releaseEntry done (origin + packet.length)
      releaseSetup pcu runu releaseFits heapu room countu masku zerou releasePhysical
  have recoveredLive : recovered.liveWords = state.liveWords := by
    simp only [State.liveWords, hr, sr, outr]
  have setupLive : setup.liveWords = state.liveWords := by
    simp only [State.liveWords, hs, ss, outs, hr, sr, outr]
  have savedLive : saved.liveWords = state.liveWords + packet.length := by
    simp only [State.liveWords, hv, sv, outv, hs, ss, outs, hr, sr, outr, List.length_append]
    omega
  have releaseSetupLive : releaseSetup.liveWords = state.liveWords + packet.length := by
    simpa only [State.liveWords, hu, su, outu] using savedLive
  have trace := (((tr.append ts).append tv).append tu).append tf
  refine ⟨final, max (max (max (max state.liveWords recovered.liveWords) savePeak) saved.liveWords) releasePeak, ?_, ?_, hf, ?_, ?_, pcf, runf, ?_⟩
  · have ticksEq : (((2 + 24) + (6 * packet.length + 1)) + 2) +
        (4 * (origin + packet.length) + 1) =
        6 * packet.length + 4 * state.heap.size + 30 := by rw [allocation]; omega
    rw [← ticksEq]
    exact trace
  · simp only [max_le_iff]
    omega
  · rw [sf, su, sv, ss, sr]
  · exact outf.trans (outu.trans (outv.trans (outs.trans outr)))
  · exact (retainedf 6 (by decide)).trans zerou



end Controller.Cost.RawTypedCopy
