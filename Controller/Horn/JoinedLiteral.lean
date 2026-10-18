module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.LiteralDispatch

@[expose] public section

/-!
# Shared state invariant for the complete normalizer literal block

The control relation retains the actual old polarity words read by the prefix.
Every dispatch stage preserves those words and the constant registers while
updating the canonical row heap. The final joined execution theorem must use
these same states and this same destination program.
-/
namespace Controller.Horn.JoinedLiteral

open Controller.Cost Controller.Horn.NormalizeProgram Controller.Horn.LiteralDispatch
open Controller.Horn.Worklist.IndexedNormalize

structure Control (state : State width 8) (literal : CNF.Literal (Fin n))
    (same opposite : Bool) : Prop where
  zero : state.reg 2 = word width 0
  trueHeld : state.reg 5 = MarkStorage.encode width true
  decrement : state.reg 6 = word width (2 ^ width - 1)
  label : state.reg 3 = word width literal.1.val
  sameHeld : state.reg 1 = MarkStorage.encode width same
  oppositeHeld : state.reg 7 = MarkStorage.encode width opposite
  running : state.halted = false

theorem Control.after_read (state : State width 8) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (marks : Marks n)
    (zero : state.reg 2 = word width 0) (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false) :
    Control (readState state layout literal marks) literal (marks.read literal) (marks.read (CNF.negate literal)) := by
  have frame := (readState_frame state layout literal marks).1
  refine ⟨?_, ?_, ?_, readState_label state layout literal marks,
    readState_same state layout literal marks, readState_opposite state layout literal marks, running⟩
  · exact (frame 2 (by decide) (by decide) (by decide) (by decide)).trans zero
  · exact (frame 5 (by decide) (by decide) (by decide) (by decide)).trans trueHeld
  · exact (frame 6 (by decide) (by decide) (by decide) (by decide)).trans decrement

theorem Control.advance (state : State width 8) (literal : CNF.Literal (Fin n))
    (same opposite : Bool) (control : Control state literal same opposite) :
    Control state.advance literal same opposite :=
  ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld,
    control.oppositeHeld, control.running⟩

theorem Control.jump (state : State width 8) (literal : CNF.Literal (Fin n))
    (same opposite : Bool) (control : Control state literal same opposite) (position : Word width) :
    Control { state with pc := position } literal same opposite :=
  ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld,
    control.oppositeHeld, control.running⟩

theorem Control.after_sign_insert (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (same opposite : Bool)
    (control : Control state literal same opposite) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels (layout.signHeader literal.2) lower cursor limit state.heap)
    (room : lower < cursor) :
    Control (inserted state entry layout literal labels lower cursor limit stored room) literal same opposite := by
  have frame := (inserted_frame state entry layout literal labels lower cursor limit stored room).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, control.running⟩
  · exact (frame 2 (by decide) (by decide)).trans control.zero
  · exact (frame 5 (by decide) (by decide)).trans control.trueHeld
  · exact (frame 6 (by decide) (by decide)).trans control.decrement
  · exact (frame 3 (by decide) (by decide)).trans control.label
  · exact (frame 1 (by decide) (by decide)).trans control.sameHeld
  · exact (frame 7 (by decide) (by decide)).trans control.oppositeHeld

theorem Control.after_conflict (state : State width 8) (literal : CNF.Literal (Fin n))
    (same opposite : Bool) (control : Control state literal same opposite)
    (header : Nat) (valid : header < state.heap.size) :
    Control (conflicted state header valid) literal same opposite := by
  have frame := (conflicted_frame state header valid).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, control.running⟩
  · exact (frame 2 (by decide)).trans control.zero
  · exact (frame 5 (by decide)).trans control.trueHeld
  · exact (frame 6 (by decide)).trans control.decrement
  · exact (frame 3 (by decide)).trans control.label
  · exact (frame 1 (by decide)).trans control.sameHeld
  · exact (frame 7 (by decide)).trans control.oppositeHeld

theorem Control.after_touched_insert (state : State width 8) (entry : Nat) (layout : Layout)
    (literal : CNF.Literal (Fin n)) (same opposite : Bool)
    (control : Control state literal same opposite) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : RecordStorage.HeaderStored labels layout.touchedHeader lower cursor limit state.heap)
    (room : lower < cursor) :
    Control (touchedInserted state entry layout literal labels lower cursor limit stored room) literal same opposite := by
  have frame := (touchedInserted_frame state entry layout literal labels lower cursor limit stored room).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, control.running⟩
  · exact (frame 2 (by decide) (by decide)).trans control.zero
  · exact (frame 5 (by decide) (by decide)).trans control.trueHeld
  · exact (frame 6 (by decide) (by decide)).trans control.decrement
  · exact (frame 3 (by decide) (by decide)).trans control.label
  · exact (frame 1 (by decide) (by decide)).trans control.sameHeld
  · exact (frame 7 (by decide) (by decide)).trans control.oppositeHeld

def signRow (row : Row n) (literal : CNF.Literal (Fin n)) : Row n :=
  if row.marks.read literal then row else
    if literal.2 then { row with positive := literal.1 :: row.positive }
    else { row with negative := literal.1 :: row.negative }

def conflictRow (row : Row n) (literal : CNF.Literal (Fin n)) : Row n :=
  if row.marks.read (CNF.negate literal) then { row with tautology := true } else row

def touchedRow (row : Row n) (literal : CNF.Literal (Fin n)) : Row n :=
  if row.marks.read literal || row.marks.read (CNF.negate literal) then row
    else { row with touched := literal.1 :: row.touched }

@[simp] theorem signRow_marks (row : Row n) (literal : CNF.Literal (Fin n)) :
    (signRow row literal).marks = row.marks := by
  simp only [signRow]
  split <;> first | rfl | split <;> rfl

@[simp] theorem conflictRow_marks (row : Row n) (literal : CNF.Literal (Fin n)) :
    (conflictRow row literal).marks = row.marks := by
  unfold conflictRow
  split <;> rfl

@[simp] theorem touchedRow_marks (row : Row n) (literal : CNF.Literal (Fin n)) :
    (touchedRow row literal).marks = row.marks := by
  unfold touchedRow
  split <;> rfl

theorem stages_record (row : Row n) (literal : CNF.Literal (Fin n)) :
    { touchedRow (conflictRow (signRow row literal) literal) literal with
      marks := MarkStorage.write row.marks literal true } = row.record literal := by
  rcases literal with ⟨label, sign⟩
  cases old : row.marks[label.val] with
  | mk positive negative =>
    cases positive <;> cases negative <;> cases sign <;>
      simp [signRow, conflictRow, touchedRow, Marks.read, CNF.negate,
        Std.Sat.Literal.negate, old, Row.record, MarkStorage.write]

/-- The execution cost retains the correlation between the two old marks. -/
def blockTicks (same opposite : Bool) : Nat :=
  5 + (if same then 2 else 6) + (if opposite then 3 else 1) +
    (if same then 2 else if opposite then 3 else 7) + 2

theorem blockTicks_le (same opposite : Bool) : blockTicks same opposite ≤ 21 := by
  cases same <;> cases opposite <;> decide

def positiveNext (row : Row n) (literal : CNF.Literal (Fin n)) (cursor : Nat) : Nat :=
  if row.marks.read literal then cursor else if literal.2 then cursor - 1 else cursor

def negativeNext (row : Row n) (literal : CNF.Literal (Fin n)) (cursor : Nat) : Nat :=
  if row.marks.read literal then cursor else if literal.2 then cursor else cursor - 1

/-- The actual sign dispatch refines the entire row heap and retains the old
polarity registers for the following two dispatches. -/
theorem sign_stage (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry (rowLayout n base) literal)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 5))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ next : State width 8,
      Execution destination state next (if row.marks.read literal then 2 else 6) state.liveWords ∧
      RowStored (signRow row literal) base (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) touchedCursor next.heap ∧
      Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      next.pc = word width (entry + 12) ∧ next.liveWords = state.liveWords ∧
      next.heap.size = state.heap.size := by
  cases same : row.marks.read literal
  · cases polarity : literal.2
    · have fresh : row.marks.read (literal.1, false) = false := by simpa [Marks.read, polarity] using same
      have room := RowStored.negative_room clause row correct literal.1 fresh base positiveCursor negativeCursor touchedCursor state.heap stored
      have header : RecordStorage.HeaderStored row.negative ((rowLayout n base).signHeader literal.2)
          (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) state.heap := by
        simpa [rowLayout, Layout.signHeader, polarity] using stored.negative
      let next := inserted state entry (rowLayout n base) literal row.negative
        (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) header room
      have upper : negativeCursor ≤ base + 4 * n + 4 := by have := stored.negative.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [same] using signed_insert_execution destination entry (rowLayout n base) literal present
          state position (by simpa [same] using control.sameHeld) control.label control.decrement
          control.running capacity row.negative (base + 3 * n + 4) negativeCursor (base + 4 * n + 4)
          header room (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
      · have refined := RowStored.prepend_negative
          (insertStart state entry ((rowLayout n base).signHeader literal.2)) row literal.1
          base positiveCursor negativeCursor touchedCursor stored room
        simpa [next, inserted, signRow, positiveNext, negativeNext, same, polarity, rowLayout,
          Layout.signHeader] using refined
      · simpa only [same] using Control.after_sign_insert state entry (rowLayout n base) literal _ _ control
          row.negative (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) header room
      · exact inserted_position state entry (rowLayout n base) literal row.negative
          (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) header room capacity
      · simp [next, inserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, State.liveWords, insertStart, State.advance, State.put]
      · simp [next, inserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, insertStart, State.advance, State.put]
    · have fresh : row.marks.read (literal.1, true) = false := by simpa [Marks.read, polarity] using same
      have room := RowStored.positive_room clause row correct literal.1 fresh base positiveCursor negativeCursor touchedCursor state.heap stored
      have header : RecordStorage.HeaderStored row.positive ((rowLayout n base).signHeader literal.2)
          (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) state.heap := by
        simpa [rowLayout, Layout.signHeader, polarity] using stored.positive
      let next := inserted state entry (rowLayout n base) literal row.positive
        (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) header room
      have upper : positiveCursor ≤ base + 3 * n + 4 := by have := stored.positive.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [same] using signed_insert_execution destination entry (rowLayout n base) literal present
          state position (by simpa [same] using control.sameHeld) control.label control.decrement
          control.running capacity row.positive (base + 2 * n + 4) positiveCursor (base + 3 * n + 4)
          header room (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
      · have refined := RowStored.prepend_positive
          (insertStart state entry ((rowLayout n base).signHeader literal.2)) row literal.1
          base positiveCursor negativeCursor touchedCursor stored room
        simpa [next, inserted, signRow, positiveNext, negativeNext, same, polarity, rowLayout,
          Layout.signHeader] using refined
      · simpa only [same] using Control.after_sign_insert state entry (rowLayout n base) literal _ _ control
          row.positive (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) header room
      · exact inserted_position state entry (rowLayout n base) literal row.positive
          (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) header room capacity
      · simp [next, inserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, State.liveWords, insertStart, State.advance, State.put]
      · simp [next, inserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, insertStart, State.advance, State.put]
  · let next : State width 8 := { state.advance.advance with pc := word width (entry + 12) }
    refine ⟨next, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simpa [same] using signed_skip_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) control.zero control.running capacity
    · simpa [next, signRow, positiveNext, negativeNext, same, State.advance] using stored
    · have kept : Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) :=
        ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld, control.oppositeHeld, control.running⟩
      simpa only [same] using kept


/-- Conflict dispatch updates the physical flag word and otherwise retains the
complete row representation. Its branch reads the original opposite register. -/
theorem conflict_stage (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry (rowLayout n base) literal)
    (row : Row n) (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 12))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ next : State width 8,
      Execution destination state next (if row.marks.read (CNF.negate literal) then 3 else 1) state.liveWords ∧
      RowStored (conflictRow row literal) base positiveCursor negativeCursor touchedCursor next.heap ∧
      Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      next.pc = word width (entry + 15) ∧ next.liveWords = state.liveWords ∧
      next.heap.size = state.heap.size := by
  cases opposite : row.marks.read (CNF.negate literal)
  · let next : State width 8 := { state.advance with pc := word width (entry + 15) }
    refine ⟨next, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simpa [opposite] using conflict_skip_execution destination entry (rowLayout n base) literal present
        state position (by simpa [opposite] using control.oppositeHeld) control.running capacity
    · simpa [next, conflictRow, opposite, State.advance] using stored
    · have kept : Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) :=
        ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld, control.oppositeHeld, control.running⟩
      simpa only [opposite] using kept
  · let next := conflicted state (base + 2 * n + 3) stored.flagBound
    refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [opposite, rowLayout] using conflict_set_execution destination entry (rowLayout n base)
        literal present state position (by simpa [opposite] using control.oppositeHeld)
        control.trueHeld control.running capacity stored.flagBound (by change base + 2 * n + 3 < 2 ^ width; have := stored.flagBound; omega)
    · simpa [next, conflictRow, opposite] using
        RowStored.set_conflict state row base positiveCursor negativeCursor touchedCursor stored
    · simpa only [opposite] using Control.after_conflict state literal _ _ control (base + 2 * n + 3) stored.flagBound
    · exact conflicted_position state (base + 2 * n + 3) stored.flagBound entry position capacity
    · simp [next, conflicted, conflictStart, State.liveWords, State.advance, State.put]
    · simp [next, conflicted, conflictStart, State.advance, State.put]


def touchedNext (row : Row n) (literal : CNF.Literal (Fin n)) (cursor : Nat) : Nat :=
  if row.marks.read literal || row.marks.read (CNF.negate literal) then cursor else cursor - 1

/-- The touched dispatch uses the same two old-mark words as the sign and
conflict stages. Room is required only on its actual fresh-channel branch. -/
theorem touched_stage (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry (rowLayout n base) literal)
    (row : Row n) (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 15))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (room : row.marks.read literal = false → row.marks.read (CNF.negate literal) = false →
      base + 4 * n + 4 < touchedCursor) :
    ∃ next : State width 8,
      Execution destination state next
        (if row.marks.read literal then 2 else if row.marks.read (CNF.negate literal) then 3 else 7) state.liveWords ∧
      RowStored (touchedRow row literal) base positiveCursor negativeCursor
        (touchedNext row literal touchedCursor) next.heap ∧
      Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      next.pc = word width (entry + 24) ∧ next.liveWords = state.liveWords ∧
      next.heap.size = state.heap.size := by
  cases same : row.marks.read literal
  · cases opposite : row.marks.read (CNF.negate literal)
    · have freshRoom := room same opposite
      let next := touchedInserted state entry (rowLayout n base) literal row.touched
        (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched freshRoom
      have upper : touchedCursor ≤ base + 5 * n + 4 := by have := stored.touched.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [same, opposite] using touched_insert_execution destination entry (rowLayout n base)
          literal present state position (by simpa [same] using control.sameHeld)
          (by simpa [opposite] using control.oppositeHeld) control.label control.decrement control.running
          capacity row.touched (base + 4 * n + 4) touchedCursor (base + 5 * n + 4)
          stored.touched freshRoom (by change base + 2 * n + 2 < 2 ^ width; omega) (by omega)
      · have refined := RowStored.prepend_touched (touchedStart state entry ((rowLayout n base).touchedHeader))
          row literal.1 base positiveCursor negativeCursor touchedCursor stored freshRoom
        simpa [next, touchedInserted, touchedRow, touchedNext, same, opposite, rowLayout] using refined
      · simpa only [same, opposite] using Control.after_touched_insert state entry (rowLayout n base) literal _ _ control
          row.touched (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched freshRoom
      · exact touchedInserted_position state entry (rowLayout n base) literal row.touched
          (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) stored.touched freshRoom capacity
      · simp [next, touchedInserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, State.liveWords, touchedStart, State.advance, State.put]
      · simp [next, touchedInserted, RecordStorage.finished, RecordStorage.afterPrepend, RecordStorage.loaded,
          LabelBuffer.prependedState, touchedStart, State.advance, State.put]
    · let jumped : State width 8 := { state.advance with pc := word width (entry + 17) }
      let next : State width 8 := { jumped.advance.advance with pc := word width (entry + 24) }
      refine ⟨next, ?_, ?_, ?_, rfl, rfl, rfl⟩
      · simpa [same, opposite, next, jumped] using touched_opposite_skip_execution destination entry
          (rowLayout n base) literal present state position (by simpa [same] using control.sameHeld)
          (by simpa [opposite] using control.oppositeHeld) control.zero control.running capacity
      · simpa [next, jumped, touchedRow, touchedNext, same, opposite, State.advance] using stored
      · have kept : Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) :=
          ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld, control.oppositeHeld, control.running⟩
        simpa only [same, opposite] using kept
  · let next : State width 8 := { state.advance.advance with pc := word width (entry + 24) }
    refine ⟨next, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simpa [same] using touched_same_skip_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) control.zero control.running capacity
    · simpa [next, touchedRow, touchedNext, same, State.advance] using stored
    · have kept : Control next literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) :=
        ⟨control.zero, control.trueHeld, control.decrement, control.label, control.sameHeld, control.oppositeHeld, control.running⟩
      simpa only [same] using kept


/-- One complete relocated block implements the accepted semantic row update.
All transitions occur in the same destination program; its storage peak is the
original state's live-word count. The old mark correlation gives at most 21
executed instructions, although the emitted block contains 26 instructions. -/
theorem record_execution (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n)) (present : LiteralAt destination entry (rowLayout n base) literal)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state : State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : State width 8,
      Execution destination state final
        (blockTicks (row.marks.read literal) (row.marks.read (CNF.negate literal))) state.liveWords ∧
      RowStored (row.record literal) base (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor) final.heap ∧
      final.pc = word width (entry + 26) ∧ final.liveWords = state.liveWords ∧
      blockTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) ≤ 21 := by
  let read := readState state (rowLayout n base) literal row.marks
  have readTrace := read_marks_execution destination entry (rowLayout n base) literal present
    state row.marks stored.marks position running capacity (Nat.le_of_lt heapFits)
  have readLive : read.liveWords = state.liveWords := rfl
  have readStored : RowStored row base positiveCursor negativeCursor touchedCursor read.heap := stored
  have readControl := Control.after_read state (rowLayout n base) literal row.marks zero trueHeld decrement running
  have readPosition := readState_position state (rowLayout n base) literal row.marks entry position (by omega)
  obtain ⟨signed, signTrace, signStored, signControl, signPosition, signLive, signSize⟩ :=
    sign_stage destination entry base literal present clause row correct read positiveCursor negativeCursor
      touchedCursor readStored readControl readPosition capacity heapFits
  let signedRow := signRow row literal
  have signedControl : Control signed literal (signedRow.marks.read literal)
      (signedRow.marks.read (CNF.negate literal)) := by simpa [signedRow] using signControl
  obtain ⟨conflict, conflictTrace, conflictStored, conflictControl, conflictPosition, conflictLive, conflictSize⟩ :=
    conflict_stage destination entry base literal present signedRow signed
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor) touchedCursor
      signStored signedControl signPosition capacity (by simpa [signSize, read, readState_heap] using heapFits)
  let conflictRowValue := conflictRow signedRow literal
  have conflictControl' : Control conflict literal (conflictRowValue.marks.read literal)
      (conflictRowValue.marks.read (CNF.negate literal)) := by simpa [conflictRowValue] using conflictControl
  have freshRoom : conflictRowValue.marks.read literal = false →
      conflictRowValue.marks.read (CNF.negate literal) = false → base + 4 * n + 4 < touchedCursor := by
    intro same opposite
    apply RowStored.touched_room clause row correct literal _ _ base positiveCursor negativeCursor touchedCursor state.heap stored
    · simpa [conflictRowValue, signedRow] using same
    · simpa [conflictRowValue, signedRow] using opposite
  obtain ⟨touched, touchedTrace, touchedStored, touchedControl, touchedPosition, touchedLive, touchedSize⟩ :=
    touched_stage destination entry base literal present conflictRowValue conflict
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor) touchedCursor
      conflictStored conflictControl' conflictPosition capacity
      (by simpa [conflictSize, signSize, read, readState_heap] using heapFits) freshRoom
  let touchedRowValue := touchedRow conflictRowValue literal
  let final := marked touched (rowLayout n base) literal touchedRowValue.marks touchedStored.marks
  have lastTrace := (mark_execution destination entry (rowLayout n base) literal present touched touchedPosition
      touchedControl.trueHeld touchedControl.running capacity touchedRowValue.marks touchedStored.marks
      (by have : touched.heap.size < 2 ^ width := by
            simpa [touchedSize, conflictSize, signSize, read, readState_heap] using heapFits
          exact Nat.le_of_lt this)).1
  have finalStored := RowStored.set_mark touched touchedRowValue literal base
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
      (touchedNext conflictRowValue literal touchedCursor) touchedStored
  have allTrace := ((readTrace.append signTrace).append conflictTrace).append (touchedTrace.append lastTrace)
  refine ⟨final, ?_, ?_, ?_, ?_, blockTicks_le _ _⟩
  · simpa only [blockTicks, signedRow, conflictRowValue, signRow_marks, conflictRow_marks,
      touchedLive, conflictLive, signLive, readLive, Nat.max_self, Nat.add_assoc] using allTrace
  · have equality : { touchedRowValue with marks := MarkStorage.write touchedRowValue.marks literal true } = row.record literal := by
      simpa [touchedRowValue, conflictRowValue, signedRow] using stages_record row literal
    simpa [final, equality, touchedNext, conflictRowValue, signedRow] using finalStored
  · exact marked_position touched (rowLayout n base) literal touchedRowValue.marks touchedStored.marks
      entry touchedPosition capacity
  · have finalLive : final.liveWords = touched.liveWords := by
      simp [final, marked, markStart, State.advance, State.put, State.liveWords]
    exact finalLive.trans (touchedLive.trans (conflictLive.trans (signLive.trans readLive)))

end Controller.Horn.JoinedLiteral
