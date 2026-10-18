module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.NormalizeCNF

@[expose] public section

/-!
# Physical outer CNF normalization loop

The loop invariant connects the remaining stored directory suffix with records
already allocated from source rows. Each source row retains its own record,
including inert tautologies. No normalized rule list is supplied to the machine.
-/
namespace Controller.Horn.NormalizeLoop

open Controller.Cost Controller.Horn.SourceDirectory
open Controller.Horn.Worklist.IndexedNormalize
open Controller.Horn.RowScan Controller.Horn.SourceScan Controller.Horn.LiteralDispatch
open Controller.Horn.JoinedLiteral Controller.Horn.NormalizeProgram

/-- Every source row contributes three headers and its deduplicated positive
body, as established by the actual row allocator. -/
def recordOffset (clauses : List (Controller.CNF.Clause (Fin n))) (start index : Nat) : Nat :=
  start + ((clauses.take index).map fun clause => 3 + (Controller.Horn.Worklist.compileClause clause).positives.length).sum

structure PackedRecords (clauses : List (Controller.CNF.Clause (Fin n)))
    (start count : Nat) (heap : Array (Word width)) : Prop where
  countBound : count ≤ clauses.length
  endpoint : heap.size = recordOffset clauses start count
  entry : ∀ index : Fin count,
    Controller.Horn.RuleCopy.Stored (Controller.Horn.Worklist.compileClause (clauses[index.val]'(by have := index.isLt; omega)))
      (recordOffset clauses start index.val) heap

/-- The program has one directory routine, one shared row routine and one
return branch. These physical fetched-code premises allow relocation. -/
structure CodeAt (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Controller.Horn.SourceDirectory.Layout clauses) : Prop where
  directory : Controller.Horn.ClauseEntry.At program entry layout.directoryHeader layout.endHeader
    layout.inputHeader layout.firstHeader (entry + 161)
  row : Controller.Horn.RowScan.RowAt program (entry + 16) n layout.base layout.inputHeader layout.firstHeader (entry + 93)
  copy : Controller.Horn.JoinedRuleCopy.CodeAt program (entry + 93) layout.base layout.recordHeader n
  setup : Controller.Horn.ResetPointer.SetupAt program (entry + 135) (layout.base + 2 * n + 2) layout.base
  reset : Controller.Horn.ResetPointer.CodeAt program (entry + 138) (layout.base + 5 * n + 4)
  headers : Controller.Horn.ResetReuse.HeaderAt program (entry + 149) n layout.base
  returnBranch : program[entry + 160]? = some (.branchZero 2 (word width entry))

/-- The immutable source and directory coexist with packed records and clean
reusable scratch. The actual heap-end cursor is represented physically. -/
structure Invariant (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (recordStart index : Nat) (marks : Marks n) (state : Controller.Cost.State width 8) : Prop where
  input : Controller.Horn.ClauseEntry.Input clauses layout index state
  records : PackedRecords clauses recordStart index state.heap
  recordCursor : Controller.Horn.SourceScan.CursorStored state.heap.size layout.recordHeader state.heap
  recordsAbove : layout.base + 5 * n + 4 ≤ recordStart
  scratch : Controller.Horn.LiteralDispatch.RowStored (Row.empty marks) layout.base
    (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4) state.heap
  clean : (Row.empty marks).Correct []

/-- Every old cell after scratch survives the source scan. This is an actual
store-address obligation, distinct from the checked low-header frame. -/
def HighFrame (scratchEnd : Nat) (before after : Array (Word width)) : Prop :=
  before.size ≤ after.size ∧ ∀ index, scratchEnd ≤ index → index < before.size →
    after[index]? = before[index]?

theorem HighFrame.refl (scratchEnd : Nat) (heap : Array (Word width)) :
    HighFrame scratchEnd heap heap := ⟨le_rfl, fun _ _ _ => rfl⟩

theorem HighFrame.trans {scratchEnd : Nat} {first middle last : Array (Word width)}
    (left : HighFrame scratchEnd first middle) (right : HighFrame scratchEnd middle last) :
    HighFrame scratchEnd first last := by
  refine ⟨left.1.trans right.1, ?_⟩
  intro index above valid
  exact (right.2 index above (lt_of_lt_of_le valid left.1)).trans (left.2 index above valid)


/-- Scratch instructions preserve every option-index cell after scratch. -/
def AboveCells (scratchEnd : Nat) (before after : Array (Word width)) : Prop :=
  ∀ index, scratchEnd ≤ index → after[index]? = before[index]?

theorem AboveCells.trans {scratchEnd : Nat} {first middle last : Array (Word width)}
    (left : AboveCells scratchEnd first middle) (right : AboveCells scratchEnd middle last) :
    AboveCells scratchEnd first last := fun index above => (right index above).trans (left index above)

/-- The actual prepend writes only its cursor header and cursor-minus-one
buffer cell, both strictly preceding the old record region. -/
theorem finished_above_cells (state : Controller.Cost.State width 8)
    (labels : List (Fin n)) (header lower cursor limit scratchEnd : Nat)
    (stored : Controller.Horn.RecordStorage.HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) (headerBelow : header < scratchEnd)
    (limitBelow : limit ≤ scratchEnd) :
    AboveCells scratchEnd state.heap
      (Controller.Horn.RecordStorage.finished state labels header lower cursor limit stored room label).heap := by
  intro index above
  have upper := stored.buffer.ends
  exact Controller.Horn.RecordStorage.finished_heap_frame state labels header lower cursor limit stored room label
    index (by omega) (by omega)

theorem inserted_above_cells (state : Controller.Cost.State width 8) (entry : Nat)
    (layout : Controller.Horn.NormalizeProgram.Layout) (literal : Controller.CNF.Literal (Fin n))
    (labels : List (Fin n)) (lower cursor limit scratchEnd : Nat)
    (stored : Controller.Horn.RecordStorage.HeaderStored labels (layout.signHeader literal.2) lower cursor limit state.heap)
    (room : lower < cursor) (headerBelow : layout.signHeader literal.2 < scratchEnd)
    (limitBelow : limit ≤ scratchEnd) :
    AboveCells scratchEnd state.heap
      (Controller.Horn.LiteralDispatch.inserted state entry layout literal labels lower cursor limit stored room).heap := by
  simpa [AboveCells, Controller.Horn.LiteralDispatch.inserted, Controller.Horn.LiteralDispatch.insertStart,
    State.put, State.advance] using finished_above_cells
      (Controller.Horn.LiteralDispatch.insertStart state entry (layout.signHeader literal.2))
      labels (layout.signHeader literal.2) lower cursor limit scratchEnd stored room literal.1 headerBelow limitBelow

theorem touched_above_cells (state : Controller.Cost.State width 8) (entry : Nat)
    (layout : Controller.Horn.NormalizeProgram.Layout) (literal : Controller.CNF.Literal (Fin n))
    (labels : List (Fin n)) (lower cursor limit scratchEnd : Nat)
    (stored : Controller.Horn.RecordStorage.HeaderStored labels layout.touchedHeader lower cursor limit state.heap)
    (room : lower < cursor) (headerBelow : layout.touchedHeader < scratchEnd)
    (limitBelow : limit ≤ scratchEnd) :
    AboveCells scratchEnd state.heap
      (Controller.Horn.LiteralDispatch.touchedInserted state entry layout literal labels lower cursor limit stored room).heap := by
  simpa [AboveCells, Controller.Horn.LiteralDispatch.touchedInserted, Controller.Horn.LiteralDispatch.touchedStart,
    State.put, State.advance] using finished_above_cells
      (Controller.Horn.LiteralDispatch.touchedStart state entry layout.touchedHeader)
      labels layout.touchedHeader lower cursor limit scratchEnd stored room literal.1 headerBelow limitBelow

/-- Setting a conflict flag does not mutate an old record cell. -/
theorem conflict_above_cells (state : Controller.Cost.State width 8)
    (header scratchEnd : Nat) (bound : header < state.heap.size) (headerBelow : header < scratchEnd) :
    AboveCells scratchEnd state.heap (Controller.Horn.LiteralDispatch.conflicted state header bound).heap := by
  intro index above
  exact (Controller.Horn.LiteralDispatch.conflicted_frame state header bound).2.2.2 index (by omega)


/-- The computed mark address is below the old record region for every
physically read channel label, including channel zero. -/
theorem mark_above_cells (state : Controller.Cost.State width 8) (base : Nat)
    (literal : Controller.CNF.Literal (Fin n))
    (bound : Controller.Horn.MarkStorage.address base literal < state.heap.size) :
    AboveCells (base + 5 * n + 4) state.heap
      (writeMarkFinished state base literal bound).heap := by
  intro index above
  have addressBelow := Controller.Horn.MarkStorage.address_lt base literal
  cases sign : literal.2 <;>
    simpa [writeMarkFinished, sign, State.put, State.advance] using
      Array.getElem?_set_ne bound
        (show Controller.Horn.MarkStorage.address base literal ≠ index by omega)

/-- The source cursor store lies below scratch and cannot overwrite a packed
record. Its new value is the actual decremented source pointer. -/
theorem source_cursor_above_cells (heap : Array (Word width)) (base header : Nat)
    (bound : header < heap.size) (before : header < base) (value : Word width) :
    AboveCells (base + 5 * n + 4) heap (heap.set header value bound) := by
  intro index above
  exact Array.getElem?_set_ne bound (show header ≠ index by omega)

theorem sign_trace_above_cells (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n))
    (present : SuffixDispatch.SuffixAt destination entry (rowLayout n base) literal)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state next : Controller.Cost.State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 5))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (trace : Execution destination state next (if row.marks.read literal then 2 else 6) state.liveWords) :
    AboveCells (base + 5 * n + 4) state.heap next.heap := by
  cases same : row.marks.read literal
  · cases polarity : literal.2
    · have fresh : row.marks.read (literal.1, false) = false := by simpa [Marks.read, polarity] using same
      have room := RowStored.negative_room clause row correct literal.1 fresh base
        positiveCursor negativeCursor touchedCursor state.heap stored
      have header : RecordStorage.HeaderStored row.negative ((rowLayout n base).signHeader literal.2)
          (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) state.heap := by
        simpa [rowLayout, Layout.signHeader, polarity] using stored.negative
      have upper : negativeCursor ≤ base + 4 * n + 4 := by have := stored.negative.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      have actual := SuffixDispatch.signed_insert_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) control.label control.decrement
        control.running capacity row.negative (base + 3 * n + 4) negativeCursor (base + 4 * n + 4)
        header room (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
      have endpoint := execution_endpoint trace (by simpa [same] using actual)
      rw [endpoint]
      exact inserted_above_cells state entry (rowLayout n base) literal row.negative
        (base + 3 * n + 4) negativeCursor (base + 4 * n + 4) (base + 5 * n + 4) header room
        (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
    · have fresh : row.marks.read (literal.1, true) = false := by simpa [Marks.read, polarity] using same
      have room := RowStored.positive_room clause row correct literal.1 fresh base
        positiveCursor negativeCursor touchedCursor state.heap stored
      have header : RecordStorage.HeaderStored row.positive ((rowLayout n base).signHeader literal.2)
          (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) state.heap := by
        simpa [rowLayout, Layout.signHeader, polarity] using stored.positive
      have upper : positiveCursor ≤ base + 3 * n + 4 := by have := stored.positive.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      have actual := SuffixDispatch.signed_insert_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) control.label control.decrement
        control.running capacity row.positive (base + 2 * n + 4) positiveCursor (base + 3 * n + 4)
        header room (by simp [rowLayout, Layout.signHeader, polarity]; omega) (by omega)
      have endpoint := execution_endpoint trace (by simpa [same] using actual)
      rw [endpoint]
      exact inserted_above_cells state entry (rowLayout n base) literal row.positive
        (base + 2 * n + 4) positiveCursor (base + 3 * n + 4) (base + 5 * n + 4) header room
        (by simp only [rowLayout, Layout.signHeader, polarity, Bool.false_eq_true, ite_false, ite_true]; omega) (by omega)
  · have actual := SuffixDispatch.signed_skip_execution destination entry (rowLayout n base) literal present
      state position (by simpa [same] using control.sameHeld) control.zero control.running capacity
    have endpoint := execution_endpoint trace (by simpa [same] using actual)
    rw [endpoint]
    intro index below
    rfl


theorem conflict_trace_above_cells (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n))
    (present : SuffixDispatch.SuffixAt destination entry (rowLayout n base) literal)
    (row : Row n) (state next : Controller.Cost.State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 12))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (trace : Execution destination state next (if row.marks.read (CNF.negate literal) then 3 else 1) state.liveWords) :
    AboveCells (base + 5 * n + 4) state.heap next.heap := by
  cases opposite : row.marks.read (CNF.negate literal)
  · have actual := SuffixDispatch.conflict_skip_execution destination entry (rowLayout n base) literal present
      state position (by simpa [opposite] using control.oppositeHeld) control.running capacity
    have endpoint := execution_endpoint trace (by simpa [opposite] using actual)
    rw [endpoint]
    intro index below
    rfl
  · have actual := SuffixDispatch.conflict_set_execution destination entry (rowLayout n base) literal present
      state position (by simpa [opposite] using control.oppositeHeld) control.trueHeld control.running capacity
      stored.flagBound (by change base + 2 * n + 3 < 2 ^ width; have := stored.flagBound; omega)
    have endpoint := execution_endpoint trace (by simpa [opposite] using actual)
    rw [endpoint]
    exact conflict_above_cells state (base + 2 * n + 3) (base + 5 * n + 4) stored.flagBound (by omega)


theorem touched_trace_above_cells (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n))
    (present : SuffixDispatch.SuffixAt destination entry (rowLayout n base) literal)
    (row : Row n) (state next : Controller.Cost.State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (control : Control state literal (row.marks.read literal) (row.marks.read (CNF.negate literal)))
    (position : state.pc = word width (entry + 15))
    (capacity : entry + 26 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (freshRoom : row.marks.read literal = false → row.marks.read (CNF.negate literal) = false →
      base + 4 * n + 4 < touchedCursor)
    (trace : Execution destination state next
      (if row.marks.read literal then 2 else if row.marks.read (CNF.negate literal) then 3 else 7) state.liveWords) :
    AboveCells (base + 5 * n + 4) state.heap next.heap := by
  cases same : row.marks.read literal
  · cases opposite : row.marks.read (CNF.negate literal)
    · have room := freshRoom same opposite
      have upper : touchedCursor ≤ base + 5 * n + 4 := by have := stored.touched.buffer.ends; omega
      have fit := RowStored.scratch_fits row base positiveCursor negativeCursor touchedCursor state.heap stored
      have actual := SuffixDispatch.touched_insert_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) (by simpa [opposite] using control.oppositeHeld)
        control.label control.decrement control.running capacity row.touched (base + 4 * n + 4)
        touchedCursor (base + 5 * n + 4) stored.touched room
        (by simp [rowLayout]; have := stored.touched.bound; omega) (by omega)
      have endpoint := execution_endpoint trace (by simpa [same, opposite] using actual)
      rw [endpoint]
      exact touched_above_cells state entry (rowLayout n base) literal row.touched
        (base + 4 * n + 4) touchedCursor (base + 5 * n + 4) (base + 5 * n + 4) stored.touched room
        (by simp [rowLayout]; omega) (by omega)
    · have actual := SuffixDispatch.touched_opposite_skip_execution destination entry (rowLayout n base) literal present
        state position (by simpa [same] using control.sameHeld) (by simpa [opposite] using control.oppositeHeld)
        control.zero control.running capacity
      have endpoint := execution_endpoint trace (by simpa [same, opposite] using actual)
      rw [endpoint]
      intro index below
      rfl
  · have actual := SuffixDispatch.touched_same_skip_execution destination entry (rowLayout n base) literal present
      state position (by simpa [same] using control.sameHeld) control.zero control.running capacity
    have endpoint := execution_endpoint trace (by simpa [same] using actual)
    rw [endpoint]
    intro index below
    rfl



theorem dynamic_record_frames (destination : Program width 8) (entry base : Nat)
    (literal : CNF.Literal (Fin n))
    (readPresent : ReadMarksAt destination entry base literal.2)
    (suffixPresent : SuffixDispatch.SuffixAt destination (entry + 1) (rowLayout n base) literal)
    (writePresent : WriteMarkAt destination (entry + 25) base literal.2)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state : Controller.Cost.State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (label : state.reg 3 = word width literal.1.val) (running : state.halted = false)
    (capacity : entry + 30 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Execution destination state final
        (dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2) state.liveWords ∧
      RowStored (row.record literal) base (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor) final.heap ∧
      Control final literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      final.pc = word width (entry + 25 + if literal.2 then 4 else 5) ∧
      final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧
      Controller.Horn.RowScan.LowFrame base state.heap final.heap ∧
      AboveCells (base + 5 * n + 4) state.heap final.heap ∧
      dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2 ≤ 25 := by
  let read := readMarksFinished state base literal row.marks
  have readTrace := read_marks_execution destination entry base literal row.marks readPresent state
    stored.marks position label trueHeld running (by omega) heapFits
  have readLive : read.liveWords = state.liveWords := by
    cases sign : literal.2 <;> simp [read, readMarksFinished, sign, State.put, State.advance, State.liveWords]
  have readHeap : read.heap = state.heap := (readMarksFinished_frame state base literal row.marks).1
  have readStored : RowStored row base positiveCursor negativeCursor touchedCursor read.heap := by
    simpa only [readHeap] using stored
  have readControl := readMarksFinished_control state base literal row.marks zero trueHeld decrement label running
  have readPosition : read.pc = word width ((entry + 1) + 5) := by
    simpa [read, Nat.add_assoc] using readMarksFinished_position state base literal row.marks entry position (by omega)
  obtain ⟨signed, signTrace, signStored, signControl, signPosition, signLive, signSize⟩ :=
    SuffixDispatch.sign_stage destination (entry + 1) base literal suffixPresent clause row correct read
      positiveCursor negativeCursor touchedCursor readStored readControl readPosition (by omega)
      (by simpa only [readHeap] using heapFits)
  let signedRow := signRow row literal
  have signedControl : Control signed literal (signedRow.marks.read literal)
      (signedRow.marks.read (CNF.negate literal)) := by simpa [signedRow] using signControl
  obtain ⟨conflict, conflictTrace, conflictStored, conflictControl, conflictPosition, conflictLive, conflictSize⟩ :=
    SuffixDispatch.conflict_stage destination (entry + 1) base literal suffixPresent signedRow signed
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor) touchedCursor
      signStored signedControl signPosition (by omega) (by simpa [signSize, readHeap] using heapFits)
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
    SuffixDispatch.touched_stage destination (entry + 1) base literal suffixPresent conflictRowValue conflict
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor) touchedCursor
      conflictStored conflictControl' conflictPosition (by omega)
      (by simpa [conflictSize, signSize, readHeap] using heapFits) freshRoom
  let touchedRowValue := touchedRow conflictRowValue literal
  let final := writeMarkFinished touched base literal (touchedStored.marks.bound literal)
  have lastTrace := write_mark_execution destination (entry + 25) base literal writePresent touched
    (touchedStored.marks.bound literal) (by simpa [Nat.add_assoc] using touchedPosition)
    touchedControl.label touchedControl.trueHeld touchedControl.running (by omega)
    (by simpa [touchedSize, conflictSize, signSize, readHeap] using heapFits)
  have finalStored := writeMarkFinished_stored touched touchedRowValue literal base
    (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
    (touchedNext conflictRowValue literal touchedCursor) touchedStored
  have allTrace := ((readTrace.append signTrace).append conflictTrace).append (touchedTrace.append lastTrace)
  have signAbove := sign_trace_above_cells destination (entry + 1) base literal suffixPresent clause row correct
    read signed positiveCursor negativeCursor touchedCursor readStored readControl readPosition
    (by omega) (by simpa only [readHeap] using heapFits) signTrace
  have conflictAbove := conflict_trace_above_cells destination (entry + 1) base literal suffixPresent signedRow
    signed conflict (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
    touchedCursor signStored signedControl signPosition (by omega)
    (by simpa [signSize, readHeap] using heapFits) conflictTrace
  have touchedAbove := touched_trace_above_cells destination (entry + 1) base literal suffixPresent conflictRowValue
    conflict touched (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
    touchedCursor conflictStored conflictControl' conflictPosition (by omega)
    (by simpa [conflictSize, signSize, readHeap] using heapFits) freshRoom touchedTrace
  have signFrame := sign_trace_low_frame destination (entry + 1) base literal suffixPresent clause row correct
    read signed positiveCursor negativeCursor touchedCursor readStored readControl readPosition
    (by omega) (by simpa only [readHeap] using heapFits) signTrace
  have conflictFrame := conflict_trace_low_frame destination (entry + 1) base literal suffixPresent signedRow
    signed conflict (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
    touchedCursor signStored signedControl signPosition (by omega)
    (by simpa [signSize, readHeap] using heapFits) conflictTrace
  have touchedFrame := touched_trace_low_frame destination (entry + 1) base literal suffixPresent conflictRowValue
    conflict touched (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
    touchedCursor conflictStored conflictControl' conflictPosition (by omega)
    (by simpa [conflictSize, signSize, readHeap] using heapFits) freshRoom touchedTrace
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dynamicTicks_le _ _ _⟩
  · simpa only [dynamicTicks, signedRow, conflictRowValue, signRow_marks, conflictRow_marks,
      touchedLive, conflictLive, signLive, readLive, Nat.max_self, Nat.add_assoc] using allTrace
  · have equality : { touchedRowValue with marks := MarkStorage.write touchedRowValue.marks literal true } = row.record literal := by
      simpa [touchedRowValue, conflictRowValue, signedRow] using stages_record row literal
    simpa [final, equality, touchedNext, conflictRowValue, signedRow] using finalStored
  · simpa only [conflictRowValue, signedRow, conflictRow_marks, signRow_marks] using
      writeMarkFinished_control touched base literal (touchedStored.marks.bound literal) _ _ touchedControl
  · exact writeMarkFinished_position touched base literal (touchedStored.marks.bound literal)
      (entry + 25) (by simpa [Nat.add_assoc] using touchedPosition) (by omega)
  · have finalLive : final.liveWords = touched.liveWords := by
      cases sign : literal.2 <;>
        simp [final, writeMarkFinished, sign, State.advance, State.put, State.liveWords]
    exact finalLive.trans (touchedLive.trans (conflictLive.trans (signLive.trans readLive)))

  · cases sign : literal.2 <;>
      simp [final, writeMarkFinished, sign, State.advance, State.put,
        touchedSize, conflictSize, signSize, readHeap]
  · have readFrame : Controller.Horn.RowScan.LowFrame base state.heap read.heap := by
      rw [readHeap]
      exact Controller.Horn.RowScan.LowFrame.refl base state.heap
    exact (((readFrame.trans signFrame).trans conflictFrame).trans touchedFrame).trans
      (writeMarkFinished_low_frame touched base literal (touchedStored.marks.bound literal))


  · have readAbove : AboveCells (base + 5 * n + 4) state.heap read.heap := by
      intro index above
      rw [readHeap]
    exact (((readAbove.trans signAbove).trans conflictAbove).trans touchedAbove).trans
      (mark_above_cells touched base literal (touchedStored.marks.bound literal))


theorem physical_record_frames (destination : Program width 8)
    (sourceEntry header pointer negativeTarget base : Nat) (literal : CNF.Literal (Fin n))
    (pairPresent : PairAt destination sourceEntry header negativeTarget)
    (readPresent : ReadMarksAt destination (if literal.2 then sourceEntry + 10 else negativeTarget) base literal.2)
    (suffixPresent : SuffixDispatch.SuffixAt destination
      ((if literal.2 then sourceEntry + 10 else negativeTarget) + 1) (rowLayout n base) literal)
    (writePresent : WriteMarkAt destination
      ((if literal.2 then sourceEntry + 10 else negativeTarget) + 25) base literal.2)
    (clause : CNF.Clause (Fin n)) (row : Row n) (correct : row.Correct clause)
    (state : Controller.Cost.State width 8) (positiveCursor negativeCursor touchedCursor : Nat)
    (stored : RowStored row base positiveCursor negativeCursor touchedCursor state.heap)
    (cursor : CursorStored (pointer + 2) header state.heap) (pair : PairStored literal pointer state.heap)
    (headerBefore : header < base) (position : state.pc = word width sourceEntry)
    (zero : state.reg 2 = word width 0) (trueHeld : state.reg 5 = MarkStorage.encode width true)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false)
    (sourceCapacity : sourceEntry + 10 < 2 ^ width)
    (recordCapacity : (if literal.2 then sourceEntry + 10 else negativeTarget) + 30 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Execution destination state final
        (10 + dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2) state.liveWords ∧
      RowStored (row.record literal) base (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor) final.heap ∧
      Control final literal (row.marks.read literal) (row.marks.read (CNF.negate literal)) ∧
      final.pc = word width ((if literal.2 then sourceEntry + 10 else negativeTarget) + 25 +
        if literal.2 then 4 else 5) ∧
      final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧
      Controller.Horn.RowScan.LowFrame base (state.heap.set header (word width pointer) cursor.bound) final.heap ∧
      AboveCells (base + 5 * n + 4) state.heap final.heap ∧
      CursorStored pointer header final.heap ∧
      10 + dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2 ≤ 35 := by
  let readerState := pairFinished state sourceEntry header pointer negativeTarget literal cursor.bound
  have prefixTrace := pair_execution destination sourceEntry header pointer negativeTarget literal pairPresent
    state cursor pair position decrement running sourceCapacity heapFits
  have prefixFrame := pairFinished_frame state sourceEntry header pointer negativeTarget literal cursor.bound
  have prefixHeap : readerState.heap = state.heap.set header (word width pointer) cursor.bound := prefixFrame.2.2.2.2
  have prefixSize : readerState.heap.size = state.heap.size := by rw [prefixHeap]; simp
  have prefixLive : readerState.liveWords = state.liveWords := by
    cases sign : literal.2 <;> simp [readerState, pairFinished, pairPrepared, sign, State.put, State.advance, State.liveWords]
  have prefixStored : RowStored row base positiveCursor negativeCursor touchedCursor readerState.heap := by
    rw [prefixHeap]
    exact rowStored_after_input_store stored header cursor.bound (word width pointer) headerBefore
  have prefixPosition := pairFinished_position state sourceEntry header pointer negativeTarget literal
    cursor.bound position sourceCapacity
  have prefixLabel := pairFinished_label state sourceEntry header pointer negativeTarget literal cursor.bound
  have prefixZero : readerState.reg 2 = word width 0 :=
    (prefixFrame.1 2 (by decide) (by decide) (by decide) (by decide)).trans zero
  have prefixTrue : readerState.reg 5 = MarkStorage.encode width true :=
    (prefixFrame.1 5 (by decide) (by decide) (by decide) (by decide)).trans trueHeld
  have prefixDecrement : readerState.reg 6 = word width (2 ^ width - 1) :=
    (prefixFrame.1 6 (by decide) (by decide) (by decide) (by decide)).trans decrement
  have prefixRunning : readerState.halted = false := prefixFrame.2.2.2.1.trans running
  obtain ⟨final, recordTrace, finalStored, finalControl, finalPosition, finalLive, finalSize, finalFrame, finalAbove, cost⟩ :=
    dynamic_record_frames destination (if literal.2 then sourceEntry + 10 else negativeTarget) base literal
      readPresent suffixPresent writePresent clause row correct readerState positiveCursor negativeCursor touchedCursor
      prefixStored prefixPosition prefixZero prefixTrue prefixDecrement prefixLabel prefixRunning
      recordCapacity (by simpa only [prefixSize] using heapFits)
  refine ⟨final, ?_, finalStored, finalControl, finalPosition, finalLive.trans prefixLive,
    finalSize.trans prefixSize, ?_, ?_, ?_, by omega⟩
  · simpa only [prefixLive, Nat.max_self] using prefixTrace.append recordTrace
  · simpa only [prefixHeap] using finalFrame
  · have prefixAbove : AboveCells (base + 5 * n + 4) state.heap readerState.heap := by
      rw [prefixHeap]
      exact source_cursor_above_cells state.heap base header cursor.bound headerBefore (word width pointer)
    exact prefixAbove.trans finalAbove
  · have prefixCursor : CursorStored pointer header readerState.heap := by
      cases sign : literal.2 <;>
        simpa [readerState, pairFinished, sign, State.advance] using pairPrepared_cursor state header pointer literal cursor.bound
    exact CursorStored.of_low_frame prefixCursor headerBefore finalSize finalFrame


theorem row_iteration_frames (destination : Program width 8) (entry base cursorHeader startHeader start exit : Nat)
    (clause : CNF.Clause (Fin n)) (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (row : Row n) (state : Controller.Cost.State width 8) (positiveCursor negativeCursor touchedCursor k : Nat)
    (invariant : Controller.Horn.RowScan.Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor (k + 1) state)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ next : Controller.Cost.State width 8, ∃ ticks : Nat,
      Execution destination state next ticks state.liveWords ∧
      Controller.Horn.RowScan.Invariant clause (row.record (clause[k]'(by have := invariant.indexBound; omega)))
        start cursorHeader startHeader base
        (positiveNext row (clause[k]'(by have := invariant.indexBound; omega)) positiveCursor)
        (negativeNext row (clause[k]'(by have := invariant.indexBound; omega)) negativeCursor)
        (touchedNext row (clause[k]'(by have := invariant.indexBound; omega)) touchedCursor) k next ∧
      next.pc = word width entry ∧ next.liveWords = state.liveWords ∧ next.heap.size = state.heap.size ∧ ticks ≤ 42 ∧ Controller.Horn.SourceDirectory.LowFrame base cursorHeader state.heap next.heap ∧
      AboveCells (base + 5 * n + 4) state.heap next.heap := by
  have bound : k < clause.length := by have := invariant.indexBound; omega
  let literal := clause[k]'bound
  let tested := testFinished state cursorHeader startHeader (start + 2 * (k + 1)) start exit
  have different : start + 2 * (k + 1) ≠ start := by omega
  have pointerFits : start + 2 * (k + 1) < 2 ^ width := by
    have := invariant.source.fits
    have := invariant.indexBound
    omega
  have startFits : start < 2 ^ width := by have := invariant.source.fits; omega
  have testTrace := test_execution destination entry cursorHeader startHeader (start + 2 * (k + 1)) start exit
    (row_test_at destination entry n base cursorHeader startHeader exit present) state invariant.cursor invariant.first
    position invariant.running (by omega) heapFits pointerFits startFits
  have testedInvariant := invariant.after_test (start + 2 * (k + 1)) exit
  have testedFrame := testFinished_frame state cursorHeader startHeader (start + 2 * (k + 1)) start exit
  have testedHeap : tested.heap = state.heap := testedFrame.2.1
  have testedSize : tested.heap.size = state.heap.size := by rw [testedHeap]
  have testedLive : tested.liveWords = state.liveWords := by
    simp [tested, testFinished, testPrepared, different, Controller.Cost.State.put, Controller.Cost.State.advance, Controller.Cost.State.liveWords]
  have testedPosition : tested.pc = word width (entry + 6) := by
    simpa [tested, different] using testFinished_position state cursorHeader startHeader
      (start + 2 * (k + 1)) start exit entry position (by omega)
  have cursor : CursorStored (start + 2 * k + 2) cursorHeader tested.heap := by
    simpa [tested, Nat.mul_add, Nat.add_assoc] using testedInvariant.cursor
  have pair : PairStored literal (start + 2 * k) tested.heap := testedInvariant.source.entry ⟨k, bound⟩
  have readPresent : ReadMarksAt destination (if literal.2 then entry + 6 + 10 else entry + 46) base literal.2 := by
    cases polarity : literal.2
    · simpa [polarity] using row_negative_read_at destination entry n base cursorHeader startHeader exit present
    · simpa [polarity, Nat.add_assoc] using row_positive_read_at destination entry n base cursorHeader startHeader exit present
  have suffixPresent : SuffixDispatch.SuffixAt destination
      ((if literal.2 then entry + 6 + 10 else entry + 46) + 1) (rowLayout n base) literal := by
    cases polarity : literal.2
    · simpa [polarity, Nat.add_assoc] using row_negative_suffix_at destination entry base cursorHeader startHeader exit literal polarity present
    · simpa [polarity, Nat.add_assoc] using row_positive_suffix_at destination entry base cursorHeader startHeader exit literal polarity present
  have writePresent : WriteMarkAt destination
      ((if literal.2 then entry + 6 + 10 else entry + 46) + 25) base literal.2 := by
    cases polarity : literal.2
    · simpa [polarity, Nat.add_assoc] using row_negative_write_at destination entry n base cursorHeader startHeader exit present
    · simpa [polarity, Nat.add_assoc] using row_positive_write_at destination entry n base cursorHeader startHeader exit present
  obtain ⟨recorded, recordTrace, recordStored, recordControl, recordPosition, recordLive, recordSize,
    recordFrame, recordAbove, inputAfterCursor, cost⟩ :=
    physical_record_frames destination (entry + 6) cursorHeader (start + 2 * k) (entry + 46) base literal
      (row_pair_at destination entry n base cursorHeader startHeader exit present) readPresent suffixPresent writePresent
      (clause.drop (k + 1)) row testedInvariant.correct tested positiveCursor negativeCursor touchedCursor
      testedInvariant.rowStored cursor pair separate.cursorBefore testedPosition testedInvariant.zero
      testedInvariant.trueHeld testedInvariant.decrement testedInvariant.running (by omega)
      (by cases polarity : literal.2 <;> simp [polarity, Nat.add_assoc] <;> omega)
      (by simpa only [testedSize] using heapFits)
  have returnPosition : recorded.pc = word width (entry + if literal.2 then 45 else 76) := by
    cases polarity : literal.2 <;> simpa [polarity, Nat.add_assoc] using recordPosition
  let next : Controller.Cost.State width 8 := { recorded.advance with pc := word width entry }
  have returnTrace := return_execution destination entry recorded
    (row_return_fetch destination entry n base cursorHeader startHeader exit present literal.2 recorded returnPosition capacity)
    recordControl.zero recordControl.running
  have updatedSource := testedInvariant.source.after_store cursorHeader cursor.bound (word width (start + 2 * k)) separate.cursorOutside
  have preservedSource := updatedSource.of_low_frame separate.sourceBefore
    (by simpa using recordSize) recordFrame
  have updatedFirst := CursorStored.after_store testedInvariant.first cursorHeader cursor.bound (word width (start + 2 * k)) separate.headersDifferent
  have preservedFirst := CursorStored.of_low_frame updatedFirst separate.firstBefore (by simpa using recordSize) recordFrame
  have retained : Controller.Horn.SourceDirectory.LowFrame base cursorHeader state.heap recorded.heap := by
    refine ⟨by have equal := recordSize.trans testedSize; omega, ?_⟩
    intro index valid below different
    have held := recordFrame index below
    have unchanged := Array.getElem?_set_ne (v := word width (start + 2 * k)) cursor.bound (Ne.symm different)
    have same : tested.heap[index]? = state.heap[index]? := by rw [testedHeap]
    exact (held.trans unchanged).trans same
  have nextInvariant : Controller.Horn.RowScan.Invariant clause (row.record literal) start cursorHeader startHeader base
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
      (touchedNext row literal touchedCursor) k next := by
    refine ⟨by omega, preservedSource, inputAfterCursor, preservedFirst, recordStored,
      correct_record_drop clause row k bound invariant.correct,
      recordControl.zero, recordControl.trueHeld, recordControl.decrement, recordControl.running⟩
  have allTrace := (testTrace.append recordTrace).append returnTrace
  refine ⟨next, 6 + (10 + dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2) + 1,
    ?_, nextInvariant, rfl, ?_, ?_, by omega, retained, ?_⟩
  · simpa only [testedLive, recordLive, Nat.max_self] using allTrace
  · have : next.liveWords = recorded.liveWords := rfl
    exact this.trans (recordLive.trans testedLive)
  · exact recordSize.trans testedSize



  · intro index above
    exact (recordAbove index above).trans (by rw [testedHeap])


theorem row_loop_frames (destination : Program width 8) (entry base cursorHeader startHeader start exit : Nat)
    (clause : CNF.Clause (Fin n)) (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (remaining : Nat) (row : Row n) (state : Controller.Cost.State width 8)
    (positiveCursor negativeCursor touchedCursor : Nat)
    (invariant : Controller.Horn.RowScan.Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor remaining state)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8, ∃ result : Row n, ∃ positive negative touched ticks : Nat,
      Execution destination state final ticks state.liveWords ∧
      Controller.Horn.RowScan.Invariant clause result start cursorHeader startHeader base positive negative touched 0 final ∧
      final.pc = word width exit ∧ final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧
      ticks ≤ 42 * remaining + 6 ∧ Controller.Horn.SourceDirectory.LowFrame base cursorHeader state.heap final.heap ∧
      AboveCells (base + 5 * n + 4) state.heap final.heap := by
  induction remaining generalizing row state positiveCursor negativeCursor touchedCursor with
  | zero =>
    let final := testFinished state cursorHeader startHeader start start exit
    have startFits : start < 2 ^ width := by have := invariant.source.fits; omega
    have cursor : CursorStored start cursorHeader state.heap := by simpa using invariant.cursor
    have trace := test_execution destination entry cursorHeader startHeader start start exit
      (row_test_at destination entry n base cursorHeader startHeader exit present) state cursor invariant.first
      position invariant.running (by omega) heapFits startFits startFits
    have finalInvariant := invariant.after_test start exit
    have finalPosition : final.pc = word width exit := by simp [final, testFinished]
    have finalLive : final.liveWords = state.liveWords := by
      simp [final, testFinished, testPrepared, Controller.Cost.State.put, Controller.Cost.State.advance, Controller.Cost.State.liveWords]
    have finalSize : final.heap.size = state.heap.size := by
      simp [final, testFinished, testPrepared, Controller.Cost.State.put, Controller.Cost.State.advance]
    exact ⟨final, row, positiveCursor, negativeCursor, touchedCursor, 6,
      trace, finalInvariant, finalPosition, finalLive, finalSize, by omega,
      by simpa [final, testFinished, testPrepared, Controller.Cost.State.put, Controller.Cost.State.advance] using Controller.Horn.SourceDirectory.LowFrame.refl base cursorHeader state.heap,
      by intro index above; simp [final, testFinished, testPrepared, State.put, State.advance]⟩
  | succ remaining ih =>
    obtain ⟨middle, used, firstTrace, middleInvariant, middlePosition, middleLive, middleSize, usedBound, middleFrame, middleAbove⟩ :=
      row_iteration_frames destination entry base cursorHeader startHeader start exit clause present separate
        row state positiveCursor negativeCursor touchedCursor remaining invariant position capacity heapFits
    have bound : remaining < clause.length := by have := invariant.indexBound; omega
    let literal := clause[remaining]'bound
    obtain ⟨final, result, positive, negative, touched, ticks, restTrace, finalInvariant,
      finalPosition, finalLive, finalSize, ticksBound, finalFrame, finalAbove⟩ :=
      ih (row.record literal) middle (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor)
        middleInvariant middlePosition (by simpa only [middleSize] using heapFits)
    refine ⟨final, result, positive, negative, touched, used + ticks, ?_, finalInvariant,
      finalPosition, finalLive.trans middleLive, finalSize.trans middleSize, by omega, middleFrame.trans finalFrame, middleAbove.trans finalAbove⟩
    simpa only [middleLive, Nat.max_self] using firstTrace.append restTrace



theorem normalize_row_frames (program : Program width 8)
    (entry base inputHeader firstHeader recordHeader start pcur ncur tcur : Nat)
    (clause : Controller.CNF.Clause (Fin n))
    (scanAt : RowAt program entry n base inputHeader firstHeader (entry + 77))
    (copyAt : Controller.Horn.JoinedRuleCopy.CodeAt program (entry + 77) base recordHeader n)
    (setupAt : Controller.Horn.ResetPointer.SetupAt program (entry + 119) (base + 2 * n + 2) base)
    (loopAt : Controller.Horn.ResetPointer.CodeAt program (entry + 122) (base + 5 * n + 4))
    (headersAt : Controller.Horn.ResetReuse.HeaderAt program (entry + 133) n base)
    (separate : Separation clause start inputHeader firstHeader base)
    (state : Controller.Cost.State width 8) (initialRow : Row n)
    (invariant : Controller.Horn.RowScan.Invariant clause initialRow start inputHeader firstHeader base
      pcur ncur tcur clause.length state)
    (dual : Controller.Horn.DualHornClause clause)
    (recordCursor : CursorStored state.heap.size recordHeader state.heap)
    (recordBelow : recordHeader < base)
    (differentInput : recordHeader ≠ inputHeader)
    (differentFirst : recordHeader ≠ firstHeader)
    (recordOutside : recordHeader < start ∨ start + 2 * clause.length ≤ recordHeader)
    (position : state.pc = word width entry) (capacity : entry + 144 < 2 ^ width)
    (heapFits : state.heap.size + 3 + clause.length < 2 ^ width)
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction) :
    ∃ final : Controller.Cost.State width 8, ∃ normalized : Row n, ∃ ticks : Nat,
      Execution program state final ticks (state.liveWords + 3 + (Controller.Horn.Worklist.compileClause clause).positives.length) ∧
      ticks ≤ 61 * clause.length + 54 ∧ normalized.Correct clause ∧
      Controller.Horn.RuleCopy.Stored (Controller.Horn.Worklist.compileClause clause) state.heap.size final.heap ∧
      CursorStored final.heap.size recordHeader final.heap ∧
      RowStored (Row.empty (Marks.clear normalized.touched normalized.marks)) base
        (base + 3 * n + 4) (base + 4 * n + 4) (base + 5 * n + 4) final.heap ∧
      (Row.empty (Marks.clear normalized.touched normalized.marks)).Correct [] ∧
      SourceStored clause start final.heap ∧ CursorStored start inputHeader final.heap ∧
      CursorStored start firstHeader final.heap ∧
      final.heap.size = state.heap.size + 3 + (Controller.Horn.Worklist.compileClause clause).positives.length ∧
      final.pc = word width (entry + 144) ∧ final.reg 2 = word width 0 ∧
      final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.halted = false ∧
      (∀ index, index < state.heap.size →
        ((index < base ∧ index ≠ inputHeader ∧ index ≠ recordHeader) ∨ base + 5 * n + 4 ≤ index) →
        final.heap[index]? = state.heap[index]?) ∧
      final.stack = state.stack ∧ final.output = state.output := by
  obtain ⟨scanned, normalized, positive, negative, touched, scanTicks, scanTrace,
    scannedInvariant, scannedPosition, scannedLive, scannedSize, scanBound, scanLow, scanAbove⟩ :=
    row_loop_frames program entry base inputHeader firstHeader start (entry + 77)
      clause scanAt separate clause.length initialRow state pcur ncur tcur invariant
      position (by omega) (by omega)
  have scannedCursor := scanLow.cursor recordCursor recordBelow differentInput
  have correct : normalized.Correct clause := by simpa using scannedInvariant.correct
  have cursor : CursorStored scanned.heap.size recordHeader scanned.heap := by
    simpa only [scannedSize] using scannedCursor
  have supported := Controller.Horn.JoinedNormalizeRow.supported_of_correct correct dual
  have fit : scanned.heap.size + 3 + normalized.positive.length < 2 ^ width := by
    have := Controller.Horn.JoinedNormalizeRow.positive_length_le correct
    rw [scannedSize]
    omega
  obtain ⟨final, reuseTrace, record, finalRecordCursor, emptyStored, clean, size,
    frame, pc, zero, one, decrement, running, stack, output⟩ :=
    Controller.Horn.JoinedRuleFrame.copy_and_reuse program (entry + 77) base recordHeader
      positive negative touched copyAt
      (by simpa [Nat.add_assoc] using setupAt)
      (by simpa [Nat.add_assoc] using loopAt)
      (by simpa [Nat.add_assoc] using headersAt)
      scanned normalized clause correct scannedInvariant.rowStored supported cursor recordBelow
      scannedPosition scannedInvariant.zero
      (by simpa [Controller.Horn.MarkStorage.encode] using scannedInvariant.trueHeld)
      scannedInvariant.decrement scannedInvariant.running (by omega) fit
  have semantic : normalized.rule = Controller.Horn.Worklist.compileClause clause := Row.rule_eq_compileClause correct
  have growing : scanned.heap.size ≤ final.heap.size := by omega
  have inputCursor : CursorStored start inputHeader scanned.heap := by simpa using scannedInvariant.cursor
  have inputHeld : final.heap[inputHeader]? = scanned.heap[inputHeader]? :=
    frame inputHeader inputCursor.bound (Or.inl separate.cursorBefore) (Ne.symm differentInput)
  have firstHeld : final.heap[firstHeader]? = scanned.heap[firstHeader]? :=
    frame firstHeader scannedInvariant.first.bound (Or.inl separate.firstBefore) (Ne.symm differentFirst)
  have source : SourceStored clause start final.heap :=
    Controller.Horn.JoinedNormalizeRow.source_of_option_frame scannedInvariant.source growing (by
      intro index lower upper
      apply frame index (by have := scannedInvariant.source.fits; omega)
        (Or.inl (by have := separate.sourceBefore; omega))
      rcases recordOutside with below | above <;> omega)
  refine ⟨final, normalized,
    scanTicks + ((if normalized.tautology then 20 else 8 * normalized.positive.length + 31) +
      11 * normalized.touched.length + 17), ?_, ?_, correct, ?_, finalRecordCursor,
    emptyStored, clean, source, Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame inputCursor growing inputHeld,
    Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame scannedInvariant.first growing firstHeld, ?_, ?_, zero, one, decrement, running, ?_, ?_, ?_⟩
  · have trace := scanTrace.append reuseTrace
    have peakBound : state.liveWords ≤ scanned.liveWords + 3 + normalized.rule.positives.length := by
      rw [scannedLive]
      omega
    simp only [Nat.max_eq_right peakBound] at trace
    simpa only [scannedLive, semantic] using trace
  · have bound := Controller.Horn.JoinedNormalizeRow.row_cost_bound correct scanBound
    simpa only [Nat.add_assoc] using bound
  · simpa only [semantic, scannedSize] using record
  · simpa only [semantic, scannedSize] using size
  · simpa [Nat.add_assoc] using pc


  · intro index valid region
    have oldValid : index < scanned.heap.size := by simpa only [scannedSize] using valid
    rcases region with low | high
    · have copied := frame index oldValid (Or.inl low.1) low.2.2
      exact copied.trans (scanLow.2 index valid low.1 low.2.1)
    · have headerDifferent : index ≠ recordHeader := by omega
      exact (frame index oldValid (Or.inr (by omega)) headerDifferent).trans (scanAbove index high)
  · have caller := caller_execution neutral (scanTrace.append reuseTrace)
    exact caller.1
  · have caller := caller_execution neutral (scanTrace.append reuseTrace)
    exact caller.2



/-- Actual heap growth and cell preservation transport a complete old rule,
including its tag, valid zero head and counted body. -/
theorem stored_rule_frame {rule : Controller.Horn.Worklist.Rule (Fin n)} {offset : Nat}
    {before after : Array (Word width)}
    (stored : Controller.Horn.RuleCopy.Stored rule offset before)
    (growing : before.size ≤ after.size)
    (held : ∀ index, offset ≤ index → index < offset + 3 + rule.positives.length →
      after[index]? = before[index]?) : Controller.Horn.RuleCopy.Stored rule offset after := by
  have fits := stored.fits
  have value : ∀ (index : Nat) (lower : offset ≤ index) (upper : index < offset + 3 + rule.positives.length),
      after[index]'(by omega) = before[index]'(by omega) := by
    intro index lower upper
    have beforeBound : index < before.size := by omega
    have afterBound : index < after.size := by omega
    simpa only [Array.getElem?_eq_getElem beforeBound,
      Array.getElem?_eq_getElem afterBound, Option.some.injEq] using held index lower upper
  refine ⟨by omega, stored.countFits, ?_, ?_, ?_, ?_⟩
  · exact (value offset (by omega) (by omega)).trans stored.tagValue
  · exact (value (offset + 1) (by omega) (by omega)).trans stored.headValue
  · exact (value (offset + 2) (by omega) (by omega)).trans stored.countValue
  · refine ⟨by have := stored.body.fits; omega, ?_⟩
    intro index
    exact (value (offset + 3 + index.val) (by omega) (by have := index.isLt; omega)).trans
      (stored.body.entry index)

/-- The next allocation starts at the physical end of the preceding record.
Inert tautologies contribute three headers and zero body cells. -/
theorem recordOffset_succ (clauses : List (Controller.CNF.Clause (Fin n)))
    (start index : Nat) (bound : index < clauses.length) :
    recordOffset clauses start (index + 1) = recordOffset clauses start index +
      3 + (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by
  simp only [recordOffset, List.take_succ_eq_append_getElem bound, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.add_assoc]

/-- Every allocated record begins after the allocation region's actual start. -/
theorem recordOffset_above (clauses : List (Controller.CNF.Clause (Fin n)))
    (start index : Nat) : start ≤ recordOffset clauses start index := by
  unfold recordOffset
  omega

/-- Preserve earlier records and add the freshly allocated physical source-row
record. No rule list is loaded or supplied independently of the source clauses. -/
theorem packed_records_append {clauses : List (Controller.CNF.Clause (Fin n))}
    {start index scratchEnd : Nat} {before after : Array (Word width)}
    (packed : PackedRecords clauses start index before) (bound : index < clauses.length)
    (above : scratchEnd ≤ start) (frame : HighFrame scratchEnd before after)
    (newRecord : Controller.Horn.RuleCopy.Stored
      (Controller.Horn.Worklist.compileClause clauses[index]) before.size after)
    (endpoint : after.size = before.size + 3 +
      (Controller.Horn.Worklist.compileClause clauses[index]).positives.length) :
    PackedRecords clauses start (index + 1) after := by
  refine ⟨by omega, ?_, ?_⟩
  · rw [endpoint, packed.endpoint, recordOffset_succ clauses start index bound]
  · intro position
    by_cases earlier : position.val < index
    · have old := packed.entry ⟨position.val, earlier⟩
      apply stored_rule_frame old frame.1
      intro cell lower upper
      have offsetAbove := recordOffset_above clauses start position.val
      change recordOffset clauses start position.val ≤ cell at lower
      have oldFits : recordOffset clauses start position.val + 3 +
          (Controller.Horn.Worklist.compileClause clauses[position.val]).positives.length ≤ before.size := old.fits
      change cell < recordOffset clauses start position.val + 3 +
        (Controller.Horn.Worklist.compileClause clauses[position.val]).positives.length at upper
      exact frame.2 cell (by omega) (by omega)
    · have finalIndex : position.val = index := by have := position.isLt; omega
      simpa only [finalIndex, packed.endpoint] using newRecord

/-- Directory setup preserves reusable scratch because all three physically
written control headers precede the scratch base. -/
theorem prepared_scratch (state : Controller.Cost.State width 8)
    (pointer rowStart rowEnd directoryHeader firstHeader inputHeader base pcur ncur tcur : Nat)
    (row : Row n) (stored : RowStored row base pcur ncur tcur state.heap)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size)
    (directoryBelow : directoryHeader < base) (firstBelow : firstHeader < base)
    (inputBelow : inputHeader < base) :
    RowStored row base pcur ncur tcur
      (Controller.Horn.ClauseEntry.prepared state pointer rowStart rowEnd
        directoryHeader firstHeader inputHeader directoryBound firstBound inputBound).heap := by
  have first := rowStored_after_input_store stored directoryHeader directoryBound
    (word width (pointer + 2)) directoryBelow
  have second := rowStored_after_input_store first firstHeader (by simpa using firstBound)
    (word width rowStart) firstBelow
  have third := rowStored_after_input_store second inputHeader (by simpa using inputBound)
    (word width rowEnd) inputBelow
  simpa [Controller.Horn.ClauseEntry.prepared, State.advance, State.put] using third



/-- The immutable directory and every original literal occurrence are retained
by the actual frame between control headers and scratch. -/
theorem directory_frame {clauses : List (Controller.CNF.Clause (Fin n))}
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    {before after : Array (Word width)}
    (stored : Controller.Horn.SourceDirectory.Stored clauses layout.directory layout.source before)
    (growing : before.size ≤ after.size)
    (held : ∀ index, layout.directory ≤ index → index < layout.base →
      after[index]? = before[index]?) :
    Controller.Horn.SourceDirectory.Stored clauses layout.directory layout.source after := by
  refine ⟨stored.fits.trans growing, ?_, ?_⟩
  · intro index
    obtain ⟨first, last⟩ := stored.entry index
    have directoryEnd := layout.directoryBefore
    have sourceEnd := layout.sourceBefore
    have sourceAbove : layout.source ≤ sourceOffset clauses layout.source clauses.length := by
      unfold sourceOffset
      omega
    refine ⟨Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame first growing
      (held _ (by omega) (by have := index.isLt; omega)),
      Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame last growing
      (held _ (by omega) (by have := index.isLt; omega))⟩
  · intro index
    have old := stored.literals index
    have sourceAbove : layout.source ≤ sourceOffset clauses layout.source index.val := by
      unfold sourceOffset
      omega
    have boundary := Controller.Horn.NormalizeCNF.sourceOffset_succ clauses layout.source index.val index.isLt
    have endpoint := Controller.Horn.NormalizeCNF.sourceOffset_le_end clauses layout.source (index.val + 1)
    have sourceEnd := layout.sourceBefore
    have directoryEnd := layout.directoryBefore
    apply Controller.Horn.JoinedNormalizeRow.source_of_option_frame old growing
    intro cell lower upper
    exact held cell (by omega) (by omega)

/-- Header preparation preserves all allocated records because its writes
precede scratch and the physical allocation region. -/
theorem prepared_record_frame (state : Controller.Cost.State width 8)
    (pointer rowStart rowEnd directoryHeader firstHeader inputHeader base : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size)
    (directoryBelow : directoryHeader < base) (firstBelow : firstHeader < base)
    (inputBelow : inputHeader < base) :
    HighFrame (base + 5 * n + 4) state.heap
      (Controller.Horn.ClauseEntry.prepared state pointer rowStart rowEnd
        directoryHeader firstHeader inputHeader directoryBound firstBound inputBound).heap := by
  refine ⟨?_, ?_⟩
  · rw [Controller.Horn.NormalizeCNF.prepared_size]
  · intro index above valid
    exact Controller.Horn.ClauseEntry.prepared_frame state pointer rowStart rowEnd
      directoryHeader firstHeader inputHeader directoryBound firstBound inputBound index
      (by omega) (by omega) (by omega)



/-- The directory preparation writes exactly three headers and advances the
program counter through ten instructions. -/
theorem prepared_position (state : Controller.Cost.State width 8)
    (entry pointer rowStart rowEnd directoryHeader firstHeader inputHeader : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size)
    (position : state.pc = word width (entry + 6)) (capacity : entry + 16 < 2 ^ width) :
    (Controller.Horn.ClauseEntry.prepared state pointer rowStart rowEnd
      directoryHeader firstHeader inputHeader directoryBound firstBound inputBound).pc =
      word width (entry + 16) := by
  simp [Controller.Horn.ClauseEntry.prepared, State.advance, State.put, position,
    word, Nat.mod_add_mod, Nat.mod_mod, Nat.add_assoc]

/-- Entry writes preserve a physically stored unaffected cursor. -/
theorem prepared_cursor {width : Nat} (state : Controller.Cost.State width 8)
    (pointer rowStart rowEnd directoryHeader firstHeader inputHeader storedHeader storedPointer : Nat)
    (directoryBound : directoryHeader < state.heap.size)
    (firstBound : firstHeader < state.heap.size) (inputBound : inputHeader < state.heap.size)
    (stored : CursorStored storedPointer storedHeader state.heap)
    (notDirectory : directoryHeader ≠ storedHeader) (notFirst : firstHeader ≠ storedHeader)
    (notInput : inputHeader ≠ storedHeader) :
    CursorStored storedPointer storedHeader
      (Controller.Horn.ClauseEntry.prepared state pointer rowStart rowEnd
        directoryHeader firstHeader inputHeader directoryBound firstBound inputBound).heap := by
  apply Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame stored
  · rw [Controller.Horn.NormalizeCNF.prepared_size]
  · exact Controller.Horn.ClauseEntry.prepared_frame state pointer rowStart rowEnd
      directoryHeader firstHeader inputHeader directoryBound firstBound inputBound storedHeader
      notDirectory notFirst notInput


theorem entry_row_execution (program : Program width 8) (entry exit : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (index : Nat) (state : Controller.Cost.State width 8)
    (present : Controller.Horn.ClauseEntry.At program entry layout.directoryHeader layout.endHeader
      layout.inputHeader layout.firstHeader exit)
    (input : Controller.Horn.ClauseEntry.Input clauses layout index state)
    (nonempty : index < clauses.length)
    (position : state.pc = word width entry) (capacity : entry + 16 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (row : Row n) (pcur ncur tcur : Nat)
    (scratch : RowStored row layout.base pcur ncur tcur state.heap) :
    ∃ entered : Controller.Cost.State width 8,
      Execution program state entered 16 state.liveWords ∧
      RowInput clauses[index] (sourceOffset clauses layout.source index)
        layout.inputHeader layout.firstHeader entered.heap ∧
      RowStored row layout.base pcur ncur tcur entered.heap ∧
      entered.pc = word width (entry + 16) ∧ entered.heap.size = state.heap.size ∧
      entered.reg 2 = word width 0 ∧ entered.reg 5 = word width 1 ∧
      entered.reg 6 = word width (2 ^ width - 1) ∧ entered.halted = false ∧
      CursorStored (layout.directory + 2 * (index + 1)) layout.directoryHeader entered.heap ∧
      (∀ cell, layout.directoryHeader ≠ cell → layout.firstHeader ≠ cell → layout.inputHeader ≠ cell →
        entered.heap[cell]? = state.heap[cell]?) := by
  let pointer := layout.directory + 2 * index
  let endpoint := layout.directory + 2 * clauses.length
  let tested := Controller.Horn.RowScan.testFinished state layout.directoryHeader layout.endHeader pointer endpoint exit
  have directoryFits := input.represented.fits
  have different : pointer ≠ endpoint := by dsimp [pointer, endpoint]; omega
  obtain ⟨testTrace, testPC, testHeap⟩ := Controller.Horn.ClauseEntry.directory_test_execution
    program entry layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader exit
    clauses layout.directory index present state input.cursor input.endpoint input.indexBound directoryFits
    position input.running capacity heapFits
  have testedPC : tested.pc = word width (entry + 6) := by
    simpa [tested, pointer, endpoint, show index ≠ clauses.length by omega] using testPC
  have testedHeap : tested.heap = state.heap := testHeap
  have frame := Controller.Horn.RowScan.testFinished_frame state layout.directoryHeader layout.endHeader pointer endpoint exit
  have testedLive : tested.liveWords = state.liveWords := by
    change (Controller.Horn.RowScan.testFinished state layout.directoryHeader layout.endHeader pointer endpoint exit).liveWords = state.liveWords
    simp only [State.liveWords, frame.2.1, frame.2.2.1, frame.2.2.2.1]
  have heldPointer : tested.reg 0 = word width pointer := by
    simp [tested, Controller.Horn.RowScan.testFinished, Controller.Horn.RowScan.testPrepared,
      different, State.advance, State.put]
  have testedOne : tested.reg 5 = word width 1 := (frame.1 5 (by decide) (by decide) (by decide)).trans input.one
  have testedRunning : tested.halted = false := frame.2.2.2.2.trans input.running
  obtain ⟨first, last⟩ := input.represented.entry ⟨index, nonempty⟩
  have firstTested : Controller.Horn.SourceScan.CursorStored (sourceOffset clauses layout.source index)
      pointer tested.heap := by simpa only [testedHeap] using first
  have lastTested : Controller.Horn.SourceScan.CursorStored (sourceOffset clauses layout.source (index + 1))
      (pointer + 1) tested.heap := by simpa only [testedHeap, pointer, Nat.add_assoc] using last
  have directoryBound : layout.directoryHeader < tested.heap.size := by
    rw [testedHeap]
    exact input.cursor.bound
  have firstBelow : layout.firstHeader < layout.directory := layout.headersBefore layout.firstHeader (by simp)
  have inputBelow : layout.inputHeader < layout.directory := layout.headersBefore layout.inputHeader (by simp)
  have firstBound : layout.firstHeader < tested.heap.size := by rw [testedHeap]; omega
  have inputBound : layout.inputHeader < tested.heap.size := by rw [testedHeap]; omega
  have pointerFits : pointer + 2 < 2 ^ width := by dsimp [pointer]; omega
  let entered := Controller.Horn.ClauseEntry.prepared tested pointer
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound
  have setupTrace := Controller.Horn.ClauseEntry.setup_execution program entry
    layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader exit pointer
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    present tested firstTested lastTested directoryBound firstBound inputBound heldPointer testedOne
    testedPC testedRunning capacity (by simpa only [testedHeap] using heapFits) pointerFits
  have represented : Controller.Horn.SourceDirectory.Stored clauses layout.directory layout.source tested.heap := by
    simpa only [testedHeap] using input.represented
  have rowInput := Controller.Horn.NormalizeCNF.prepared_row_input clauses layout index nonempty tested
    represented directoryBound firstBound inputBound
  have sourceAbove : layout.source ≤ sourceOffset clauses layout.source clauses.length := by
    unfold sourceOffset
    omega
  have headerBelow : ∀ header ∈ [layout.directoryHeader, layout.firstHeader, layout.inputHeader], header < layout.base := by
    intro header member
    have h := layout.headersBefore header (by
      simp only [List.mem_cons, List.mem_singleton] at member ⊢
      tauto)
    have := layout.directoryBefore
    have := layout.sourceBefore
    omega
  have testedScratch : RowStored row layout.base pcur ncur tcur tested.heap := by
    simpa only [testedHeap] using scratch
  have scratchAfter := prepared_scratch tested pointer
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    layout.directoryHeader layout.firstHeader layout.inputHeader layout.base pcur ncur tcur row
    testedScratch directoryBound firstBound inputBound
    (headerBelow _ (by simp)) (headerBelow _ (by simp)) (headerBelow _ (by simp))
  have tail1 : [layout.inputHeader, layout.firstHeader, layout.directoryHeader, layout.endHeader].Nodup :=
    (List.nodup_cons.mp layout.headersDistinct).2
  have tail2 : [layout.firstHeader, layout.directoryHeader, layout.endHeader].Nodup :=
    (List.nodup_cons.mp tail1).2
  have inputNot := (List.nodup_cons.mp tail1).1
  have firstNot := (List.nodup_cons.mp tail2).1
  have directoryFirst : layout.directoryHeader ≠ layout.firstHeader := by
    intro equal
    exact firstNot (by simp [equal])
  have directoryInput : layout.directoryHeader ≠ layout.inputHeader := by
    intro equal
    exact inputNot (by simp [equal])
  have firstInput : layout.firstHeader ≠ layout.inputHeader := by
    intro equal
    exact inputNot (by simp [equal])
  have newCursors := Controller.Horn.NormalizeCNF.prepared_cursors tested pointer
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound
    directoryFirst directoryInput firstInput
  have common := Controller.Horn.ClauseEntry.prepared_common tested pointer
    (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
    layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound
  refine ⟨entered, ?_, rowInput, scratchAfter, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [testedLive, Nat.max_self, Nat.reduceAdd] using testTrace.append setupTrace
  · exact prepared_position tested entry pointer
      (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
      layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound
      testedPC capacity
  · rw [Controller.Horn.NormalizeCNF.prepared_size, testedHeap]
  · exact (common 2 (by decide) (by decide) (by decide) (by decide)).trans
      ((frame.1 2 (by decide) (by decide) (by decide)).trans input.zero)
  · exact (common 5 (by decide) (by decide) (by decide) (by decide)).trans testedOne
  · exact (common 6 (by decide) (by decide) (by decide) (by decide)).trans
      ((frame.1 6 (by decide) (by decide) (by decide)).trans input.decrement)
  · exact testedRunning
  · simpa only [pointer, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using newCursors.1
  · intro cell notDirectory notFirst notInput
    have held := Controller.Horn.ClauseEntry.prepared_frame tested pointer
      (sourceOffset clauses layout.source index) (sourceOffset clauses layout.source (index + 1))
      layout.directoryHeader layout.firstHeader layout.inputHeader directoryBound firstBound inputBound cell
      notDirectory notFirst notInput
    exact held.trans (by rw [testedHeap])



/-- An entry setup changes no record cell and allocates no words. -/
theorem packed_records_frame {clauses : List (Controller.CNF.Clause (Fin n))}
    {start count scratchEnd : Nat} {before after : Array (Word width)}
    (packed : PackedRecords clauses start count before) (above : scratchEnd ≤ start)
    (frame : HighFrame scratchEnd before after) (size : after.size = before.size) :
    PackedRecords clauses start count after := by
  refine ⟨packed.countBound, size.trans packed.endpoint, ?_⟩
  intro index
  have old := packed.entry index
  apply stored_rule_frame old frame.1
  intro cell lower upper
  have offsetAbove := recordOffset_above clauses start index.val
  exact frame.2 cell (by omega) (by have := old.fits; omega)

/-- One complete outer transition visits one physical directory entry,
normalizes its original source row and returns to the same shared loop. -/
theorem cnf_iteration (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : CodeAt program entry clauses layout)
    (recordStart index : Nat) (marks : Marks n) (state : Controller.Cost.State width 8)
    (invariant : Invariant clauses layout recordStart index marks state)
    (nonempty : index < clauses.length)
    (dual : Controller.Horn.DualHornClause clauses[index])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (heapFits : state.heap.size + 3 + clauses[index].length < 2 ^ width)
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction) :
    ∃ next : Controller.Cost.State width 8, ∃ nextMarks : Marks n, ∃ ticks : Nat,
      Execution program state next ticks
        (state.liveWords + 3 + (Controller.Horn.Worklist.compileClause clauses[index]).positives.length) ∧
      Invariant clauses layout recordStart (index + 1) nextMarks next ∧
      next.pc = word width entry ∧
      ticks ≤ 61 * clauses[index].length + 71 := by
  have headers := layout.headersDistinct
  have recordInput : layout.recordHeader ≠ layout.inputHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have recordFirst : layout.recordHeader ≠ layout.firstHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have recordDirectory : layout.recordHeader ≠ layout.directoryHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have recordEnd : layout.recordHeader ≠ layout.endHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have directoryInput : layout.directoryHeader ≠ layout.inputHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have endDirectory : layout.endHeader ≠ layout.directoryHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have endFirst : layout.endHeader ≠ layout.firstHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have endInput : layout.endHeader ≠ layout.inputHeader := by
    have h := headers; simp only [List.nodup_cons, List.mem_cons, List.mem_singleton] at h; tauto
  have sourceAbove : layout.source ≤ sourceOffset clauses layout.source clauses.length := by
    unfold sourceOffset; omega
  have beforeBase : ∀ header ∈ [layout.recordHeader, layout.inputHeader, layout.firstHeader,
      layout.directoryHeader, layout.endHeader], header < layout.base := by
    intro header member
    have h := layout.headersBefore header member
    have := layout.directoryBefore
    have := layout.sourceBefore
    omega
  obtain ⟨entered, entryTrace, rowInput, scratch, entryPosition, entrySize,
    entryZero, entryOne, entryDecrement, entryRunning, directoryCursor, entryFrame⟩ :=
    entry_row_execution program entry (entry + 161) clauses layout index state present.directory
      invariant.input nonempty position (by omega) (by omega) (Row.empty marks)
      (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4) invariant.scratch
  have entryCaller := caller_execution neutral entryTrace
  have entryLive : entered.liveWords = state.liveWords := by
    simp only [State.liveWords, entrySize, entryCaller.1, entryCaller.2]
  have enteredRecords := packed_records_frame invariant.records invariant.recordsAbove
    (show HighFrame (layout.base + 5 * n + 4) state.heap entered.heap from
      ⟨by omega, by
        intro cell above valid
        exact entryFrame cell
          (by have h := beforeBase layout.directoryHeader (by simp); omega)
          (by have h := beforeBase layout.firstHeader (by simp); omega)
          (by have h := beforeBase layout.inputHeader (by simp); omega)⟩) entrySize
  have enteredRecordCursor : CursorStored entered.heap.size layout.recordHeader entered.heap := by
    rw [entrySize]
    apply Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame invariant.recordCursor (by omega)
    exact entryFrame _ (Ne.symm recordDirectory) (Ne.symm recordFirst) (Ne.symm recordInput)
  have enteredDirectory : Stored clauses layout.directory layout.source entered.heap :=
    directory_frame layout invariant.input.represented (by omega) (by
    intro cell lower upper
    exact entryFrame cell
      (by have := layout.headersBefore layout.directoryHeader (by simp); omega)
      (by have := layout.headersBefore layout.firstHeader (by simp); omega)
      (by have := layout.headersBefore layout.inputHeader (by simp); omega))
  have enteredEndpoint := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame invariant.input.endpoint
    (by omega) (entryFrame _ (Ne.symm endDirectory) (Ne.symm endFirst) (Ne.symm endInput))
  have sourceBoundary := Controller.Horn.NormalizeCNF.sourceOffset_succ clauses layout.source index nonempty
  have sourceEnd := Controller.Horn.NormalizeCNF.sourceOffset_le_end clauses layout.source (index + 1)
  have separation : Separation clauses[index] (sourceOffset clauses layout.source index)
      layout.inputHeader layout.firstHeader layout.base := by
    refine ⟨?_, beforeBase _ (by simp), beforeBase _ (by simp), rowInput.separateHeaders,
      rowInput.cursorOutside⟩
    have := layout.sourceBefore
    omega
  have scanInvariant : Controller.Horn.RowScan.Invariant clauses[index] (Row.empty marks)
      (sourceOffset clauses layout.source index) layout.inputHeader layout.firstHeader layout.base
      (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4)
      clauses[index].length entered := by
    refine ⟨le_rfl, rowInput.source, rowInput.cursor, rowInput.first, scratch, ?_,
      entryZero, ?_, entryDecrement, entryRunning⟩
    · simpa only [List.drop_length] using invariant.clean
    · simpa [Controller.Horn.MarkStorage.encode] using entryOne
  obtain ⟨finished, normalized, used, rowTrace, rowCost, correct, record, recordCursor,
    emptyScratch, clean, source, inputCursor, firstCursor, size, rowPosition,
    zero, one, decrement, running, rowFrame, stack, output⟩ :=
    normalize_row_frames program (entry + 16) layout.base layout.inputHeader layout.firstHeader
      layout.recordHeader (sourceOffset clauses layout.source index)
      (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4)
      clauses[index] present.row
      (by simpa only [Nat.add_assoc] using present.copy)
      (by simpa only [Nat.add_assoc] using present.setup)
      (by simpa only [Nat.add_assoc] using present.reset)
      (by simpa only [Nat.add_assoc] using present.headers)
      separation entered (Row.empty marks) scanInvariant dual enteredRecordCursor
      (beforeBase _ (by simp)) recordInput recordFirst
      (Or.inl (by
        have := layout.headersBefore layout.recordHeader (by simp)
        have := layout.directoryBefore
        unfold sourceOffset
        omega))
      entryPosition (by omega) (by simpa only [entrySize] using heapFits) neutral
  have growing : entered.heap.size ≤ finished.heap.size := by omega
  have recordsNext := packed_records_append enteredRecords nonempty invariant.recordsAbove
    (show HighFrame (layout.base + 5 * n + 4) entered.heap finished.heap from
      ⟨growing, fun cell above valid => rowFrame cell valid (Or.inr above)⟩) record size
  have immutable := directory_frame layout enteredDirectory growing (by
    intro cell lower upper
    apply rowFrame cell
    · have sourceSize := enteredDirectory.fits
      have scratchFits := RowStored.scratch_fits (Row.empty marks) layout.base
        (layout.base + 3 * n + 4) (layout.base + 4 * n + 4) (layout.base + 5 * n + 4) entered.heap scratch
      omega
    · refine Or.inl ⟨upper, ?_, ?_⟩
      · have before := layout.headersBefore layout.inputHeader (by simp); omega
      · have before := layout.headersBefore layout.recordHeader (by simp); omega)
  have nextDirectory := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame directoryCursor growing
    (rowFrame _ directoryCursor.bound (Or.inl ⟨beforeBase _ (by simp), directoryInput, Ne.symm recordDirectory⟩))
  have nextEndpoint := Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame enteredEndpoint growing
    (rowFrame _ enteredEndpoint.bound (Or.inl ⟨beforeBase _ (by simp), endInput, Ne.symm recordEnd⟩))
  have returnFetch : program[finished.pc.val]? = some (.branchZero 2 (word width entry)) := by
    have pcValue : finished.pc.val = entry + 160 := by
      rw [rowPosition]
      simp only [word, Nat.add_assoc, Nat.mod_eq_of_lt (show entry + 16 + 144 < 2 ^ width by omega)]
    simpa only [pcValue] using present.returnBranch
  let next : Controller.Cost.State width 8 := { finished.advance with pc := word width entry }
  have returnTrace := return_execution program entry finished returnFetch zero running
  have nextInput : Controller.Horn.ClauseEntry.Input clauses layout (index + 1) next :=
    ⟨immutable, by omega, nextDirectory, nextEndpoint, zero, one, decrement, running⟩
  have nextInvariant : Invariant clauses layout recordStart (index + 1)
      (Marks.clear normalized.touched normalized.marks) next :=
    ⟨nextInput, recordsNext, recordCursor, invariant.recordsAbove, emptyScratch, clean⟩
  have finishedLive : finished.liveWords = entered.liveWords + 3 +
      (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by
    simp only [State.liveWords, size, stack, output]
    omega
  refine ⟨next, Marks.clear normalized.touched normalized.marks, 16 + used + 1,
    ?_, nextInvariant, rfl, by omega⟩
  have whole := (entryTrace.append rowTrace).append returnTrace
  have peak : state.liveWords ≤ state.liveWords + 3 +
      (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by omega
  simpa only [entryLive, finishedLive, Nat.max_eq_right peak, Nat.max_self] using whole



def literalSuffix (clauses : List (Controller.CNF.Clause (Fin n))) (index : Nat) : Nat :=
  ((clauses.drop index).map List.length).sum

def wordSuffix (clauses : List (Controller.CNF.Clause (Fin n))) (index : Nat) : Nat :=
  ((clauses.drop index).map fun clause => 3 + (Controller.Horn.Worklist.compileClause clause).positives.length).sum

theorem suffix_step (clauses : List (Controller.CNF.Clause (Fin n))) (index : Nat)
    (bound : index < clauses.length) :
    literalSuffix clauses index = clauses[index].length + literalSuffix clauses (index + 1) ∧
    wordSuffix clauses index = 3 + (Controller.Horn.Worklist.compileClause clauses[index]).positives.length +
      wordSuffix clauses (index + 1) := by
  constructor <;>
    simp only [literalSuffix, wordSuffix, List.drop_eq_getElem_cons bound, List.map_cons, List.sum_cons]

theorem compiled_body_le (clause : Controller.CNF.Clause (Fin n)) :
    (Controller.Horn.Worklist.compileClause clause).positives.length ≤ clause.length := by
  have dedup := (List.dedup_sublist
    ((clause.filter fun literal => decide (literal.2 = true)).map Prod.fst)).length_le
  have filtered : (clause.filter fun literal => decide (literal.2 = true)).length ≤ clause.length :=
    List.Sublist.length_le List.filter_sublist
  have signed : (Controller.Horn.Worklist.signedLabels clause true).length ≤ clause.length := by
    simpa only [Controller.Horn.Worklist.signedLabels, List.length_map] using dedup.trans (by simpa using filtered)
  unfold Controller.Horn.Worklist.compileClause
  split
  · simp [Controller.Horn.Worklist.Rule.positives]
  · cases Controller.Horn.Worklist.signedLabels clause false <;> exact signed

/-- The complete shared physical loop is bounded by the original source
incidences. Its decreasing suffix index is a proof invariant; runtime tests
only the stored directory pointers. -/
theorem normalize_cnf_execution (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : CodeAt program entry clauses layout) (recordStart index remaining : Nat)
    (marks : Marks n) (state : Controller.Cost.State width 8)
    (invariant : Invariant clauses layout recordStart index marks state)
    (suffix : index + remaining = clauses.length)
    (dual : ∀ i : Fin clauses.length, Controller.Horn.DualHornClause clauses[i.val])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (room : state.heap.size + 3 * remaining + literalSuffix clauses index < 2 ^ width)
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction) :
    ∃ final : Controller.Cost.State width 8, ∃ finalMarks : Marks n, ∃ ticks : Nat,
      Execution program state final ticks (state.liveWords + wordSuffix clauses index) ∧
      Invariant clauses layout recordStart clauses.length finalMarks final ∧
      final.pc = word width (entry + 161) ∧
      ticks ≤ 61 * literalSuffix clauses index + 71 * remaining + 6 := by
  induction remaining generalizing index marks state with
  | zero =>
    have complete : index = clauses.length := by omega
    let final := testFinished state layout.directoryHeader layout.endHeader
      (layout.directory + 2 * clauses.length) (layout.directory + 2 * clauses.length) (entry + 161)
    have trace := Controller.Horn.ClauseEntry.directory_test_execution program entry layout.directoryHeader
      layout.endHeader layout.inputHeader layout.firstHeader (entry + 161) clauses layout.directory
      index present.directory state invariant.input.cursor invariant.input.endpoint invariant.input.indexBound
      invariant.input.represented.fits position invariant.input.running (by omega) (by omega)
    have frame := testFinished_frame state layout.directoryHeader layout.endHeader
      (layout.directory + 2 * clauses.length) (layout.directory + 2 * clauses.length) (entry + 161)
    have finalHeap : final.heap = state.heap := frame.2.1
    have finalInput : Controller.Horn.ClauseEntry.Input clauses layout clauses.length final := by
      refine ⟨?_, le_rfl, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · simpa only [finalHeap] using invariant.input.represented
      · simpa only [complete, finalHeap] using invariant.input.cursor
      · simpa only [finalHeap] using invariant.input.endpoint
      · exact (frame.1 2 (by decide) (by decide) (by decide)).trans invariant.input.zero
      · exact (frame.1 5 (by decide) (by decide) (by decide)).trans invariant.input.one
      · exact (frame.1 6 (by decide) (by decide) (by decide)).trans invariant.input.decrement
      · exact frame.2.2.2.2.trans invariant.input.running
    have finalInvariant : Invariant clauses layout recordStart clauses.length marks final := by
      refine ⟨finalInput, ?_, ?_, invariant.recordsAbove, ?_, invariant.clean⟩
      · simpa only [complete, finalHeap] using invariant.records
      · simpa only [finalHeap] using invariant.recordCursor
      · simpa only [finalHeap] using invariant.scratch
    refine ⟨final, marks, 6, ?_, finalInvariant, ?_, ?_⟩
    · simpa only [complete, wordSuffix, List.drop_length, List.map_nil, List.sum_nil, Nat.add_zero] using trace.1
    · simp [final, testFinished]
    · omega
  | succ remaining ih =>
    have nonempty : index < clauses.length := by omega
    have steps := suffix_step clauses index nonempty
    obtain ⟨middle, middleMarks, used, firstTrace, middleInvariant, middlePosition, usedBound⟩ :=
      cnf_iteration program entry clauses layout present recordStart index marks state invariant nonempty
        (dual ⟨index, nonempty⟩) position capacity (by omega) neutral
    have oldEndpoint := invariant.records.endpoint
    have newEndpoint := middleInvariant.records.endpoint
    have offsetStep := recordOffset_succ clauses recordStart index nonempty
    have bodyBound := compiled_body_le clauses[index]
    have size : middle.heap.size = state.heap.size + 3 +
        (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by omega
    have caller := caller_execution neutral firstTrace
    have live : middle.liveWords = state.liveWords + 3 +
        (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by
      simp only [State.liveWords, size, caller.1, caller.2]
      omega
    have remainingRoom : middle.heap.size + 3 * remaining + literalSuffix clauses (index + 1) < 2 ^ width := by
      omega
    obtain ⟨final, finalMarks, ticks, restTrace, finalInvariant, finalPosition, ticksBound⟩ :=
      ih (index + 1) middleMarks middle middleInvariant (by omega) dual middlePosition remainingRoom
    have peak : max (state.liveWords + 3 +
        (Controller.Horn.Worklist.compileClause clauses[index]).positives.length)
        (middle.liveWords + wordSuffix clauses (index + 1)) = state.liveWords + wordSuffix clauses index := by
      rw [live, steps.2]
      omega
    refine ⟨final, finalMarks, used + ticks, ?_, finalInvariant, finalPosition, by omega⟩
    simpa only [peak] using firstTrace.append restTrace



/-- Storage charges each source row's three real header words and at most one
body word per original physical literal occurrence. -/
theorem wordSuffix_bound (clauses : List (Controller.CNF.Clause (Fin n))) (index : Nat) :
    wordSuffix clauses index ≤ 3 * (clauses.drop index).length + literalSuffix clauses index := by
  have all : ∀ rows : List (Controller.CNF.Clause (Fin n)),
      (rows.map fun clause => 3 + (Controller.Horn.Worklist.compileClause clause).positives.length).sum ≤
      3 * rows.length + (rows.map List.length).sum := by
    intro rows
    induction rows with
    | nil => simp
    | cons clause tail ih =>
      have body := compiled_body_le clause
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  exact all (clauses.drop index)

/-- Full-source consumer starts with physically empty record storage and the
actual allocation cursor already represented by the invariant. The source is
never replaced by a precomputed normalized rule list. -/
theorem normalize_all_execution (program : Program width 8) (entry : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : CodeAt program entry clauses layout) (recordStart : Nat)
    (marks : Marks n) (state : Controller.Cost.State width 8)
    (invariant : Invariant clauses layout recordStart 0 marks state)
    (dual : ∀ i : Fin clauses.length, Controller.Horn.DualHornClause clauses[i.val])
    (position : state.pc = word width entry) (capacity : entry + 161 < 2 ^ width)
    (room : state.heap.size + 3 * clauses.length + (clauses.map List.length).sum < 2 ^ width)
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction) :
    ∃ final : Controller.Cost.State width 8, ∃ finalMarks : Marks n, ∃ ticks peak : Nat,
      Execution program state final ticks peak ∧
      Invariant clauses layout recordStart clauses.length finalMarks final ∧
      final.pc = word width (entry + 161) ∧
      ticks ≤ 61 * (clauses.map List.length).sum + 71 * clauses.length + 6 ∧
      programWords program + peak ≤ programWords program + state.liveWords +
        3 * clauses.length + (clauses.map List.length).sum := by
  obtain ⟨final, finalMarks, ticks, trace, complete, finalPosition, cost⟩ :=
    normalize_cnf_execution program entry clauses layout present recordStart 0 clauses.length marks state
      invariant (by omega) dual position capacity
      (by simpa only [literalSuffix, List.drop_zero] using room) neutral
  have storage := wordSuffix_bound clauses 0
  refine ⟨final, finalMarks, ticks, state.liveWords + wordSuffix clauses 0,
    trace, complete, finalPosition, ?_, ?_⟩
  · simpa only [literalSuffix, List.drop_zero] using cost
  · simp only [literalSuffix, List.drop_zero] at storage
    omega


end Controller.Horn.NormalizeLoop
