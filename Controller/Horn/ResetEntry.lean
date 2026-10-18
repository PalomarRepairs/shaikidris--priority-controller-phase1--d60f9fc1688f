module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.ResetPointer
public import Controller.Cost.Frames
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Actual reset entry and arbitrary-state continuation

The physical touched-header setup yields exactly the configured reset core,
with the caller's original trailing stack and output. The general machine
frame theorem transports the checked pointer traversal and charges those words.
-/
namespace Controller.Horn.ResetEntry

open Controller.Cost Controller.Horn.ResetPointer Controller.Horn.ResetTouched
open Controller.Horn.Worklist.IndexedNormalize

@[simp] private theorem word_eta (value : Word width) : word width value.val = value := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt value.isLt

private theorem state_ext (left right : State width registers)
    (reg : left.reg = right.reg) (heap : left.heap = right.heap)
    (stack : left.stack = right.stack) (output : left.output = right.output)
    (pc : left.pc = right.pc) (halted : left.halted = right.halted) : left = right := by
  cases left
  cases right
  simp_all

/-- Scratch words come from the actual source registers; no list count is
inserted into the configured traversal. The only constants are those already
held by the caller's common register convention. -/
theorem setup_configuration (state : State width 8) (header pointer base entry : Nat)
    (position : state.pc = word width entry) (capacity : entry + 3 < 2 ^ width)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false) :
    setupFinished state header pointer base =
      (configuration state.heap pointer (state.reg 1).val base (state.reg 3).val (state.reg 4).val
        (entry + 3)).frame state.stack state.output := by
  apply state_ext
  · funext register
    fin_cases register <;>
      simp [setupFinished, setupMiddle, State.put, State.advance, configuration,
        State.frame, zero, one, decrement, MarkStorage.encode]
  · rfl
  · rfl
  · rfl
  · exact setupFinished_position state header pointer base entry position capacity
  · exact running

/-- The complete reset begins with the actual header read, transports the
configured pointer loop into the caller's arbitrary stack/output, and charges
all those words at every transition. -/
theorem execution (destination : Program width 8) (entry header base pointer limit : Nat)
    (setupAt : SetupAt destination entry header base)
    (loopAt : ResetPointer.CodeAt destination (entry + 3) limit)
    (state : State width 8) (marks : Marks n) (labels : List (Fin n))
    (marked : MarkStorage.Stored marks base state.heap)
    (stored : LabelsStored labels pointer state.heap) (ends : pointer + labels.length = limit)
    (separate : base + 2 * n ≤ pointer)
    (headerBound : header < state.heap.size)
    (headerValue : state.heap[header]'headerBound = word width pointer)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false)
    (capacity : entry + 14 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution destination state final (11 * labels.length + 6) state.liveWords ∧
      MarkStorage.Stored (Marks.clear labels marks) base final.heap ∧
      final.heap.size = state.heap.size ∧ Frame n base state.heap final.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 14) := by
  have setup := setup_execution destination entry header base pointer setupAt state position running
    (by omega) headerBound (headerBound.trans heapFits) headerValue
  obtain ⟨finalHeap, finalLabel, finalAddress, loop, cleared, size, frame⟩ :=
    ResetPointer.execution destination (entry + 3) limit loopAt labels state.heap marks base pointer
      (state.reg 1).val (state.reg 3).val (state.reg 4).val marked stored ends separate
      (by omega) heapFits
  have framed := loop.frame state.stack state.output
  rw [← setup_configuration state header pointer base entry position (by omega) zero one decrement running] at framed
  have trace := setup.append framed
  let final := (configuration finalHeap limit 0 base finalLabel finalAddress (entry + 3 + 11)).frame state.stack state.output
  refine ⟨final, ?_, cleared, size, frame, rfl, rfl, ?_⟩
  · have peak : 9 + state.heap.size + (state.stack.length + state.output.length) = state.liveWords := by
      simp only [State.liveWords]
      omega
    have ticks : 3 + (11 * labels.length + 3) = 11 * labels.length + 6 := by omega
    simpa only [peak, Nat.max_self, ticks] using trace
  · simp [final, configuration, State.frame, show entry + 3 + 11 = entry + 14 by omega]


/-- Canonical row storage supplies the physical header, suffix endpoint and
separation conditions. A correct normalized row clears every ambient mark. -/
theorem row_execution (destination : Program width 8) (entry base : Nat)
    (setupAt : SetupAt destination entry (base + 2 * n + 2) base)
    (loopAt : ResetPointer.CodeAt destination (entry + 3) (base + 5 * n + 4))
    (state : State width 8) (row : Row n) (clause : CNF.Clause (Fin n))
    (correct : row.Correct clause) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : LiteralDispatch.RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false)
    (capacity : entry + 14 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution destination state final (11 * row.touched.length + 6) state.liveWords ∧
      MarkStorage.Stored (Marks.clear row.touched row.marks) base final.heap ∧
      (Marks.clear row.touched row.marks).Clean ∧
      11 * row.touched.length + 6 ≤ 11 * clause.length + 6 ∧
      final.heap.size = state.heap.size ∧ Frame n base state.heap final.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 14) := by
  obtain ⟨final, trace, marked, size, frame, stack, output, pc⟩ :=
    execution destination entry (base + 2 * n + 2) base touchedCursor (base + 5 * n + 4)
      setupAt loopAt state row.marks row.touched stored.marks stored.touched.buffer.labels
      stored.touched.buffer.ends (by have := stored.touched.buffer.lower_le_cursor; omega)
      stored.touched.bound stored.touched.value position zero one decrement running capacity heapFits
  refine ⟨final, trace, marked, Row.clear_clean correct, ?_, size, frame, stack, output, pc⟩
  have lengthBound := Row.touched_length_le correct
  omega

end Controller.Horn.ResetEntry
