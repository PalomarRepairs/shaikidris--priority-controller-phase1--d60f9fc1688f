module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.JoinedNormalizeRow

@[expose] public section

/-!
# Physical clause directory and shared normalizer frames

Each directory entry stores source start and end pointers. The source words
retain every occurrence. The proof index denotes a directory suffix, while the
machine reads and compares physically stored cursor and endpoint words.
-/
namespace Controller.Horn.SourceDirectory

open Controller.Cost Controller.Horn.SourceScan Controller.Horn.RowScan
open Controller.Horn.Worklist.IndexedNormalize Controller.Horn.LiteralDispatch
open Controller.Horn.JoinedLiteral Controller.Horn.MarkStorage
open Controller.Horn.JoinedNormalizeRow

/-- Two words are stored for every source occurrence. -/
def sourceOffset (clauses : List (Controller.CNF.Clause (Fin n))) (start index : Nat) : Nat :=
  start + 2 * ((clauses.take index).map List.length).sum

/-- A directory row stores source boundaries, rather than a literal count. -/
structure Stored (clauses : List (Controller.CNF.Clause (Fin n)))
    (directory source : Nat) (heap : Array (Word width)) : Prop where
  fits : directory + 2 * clauses.length ≤ heap.size
  entry : ∀ index : Fin clauses.length,
    CursorStored (sourceOffset clauses source index.val) (directory + 2 * index.val) heap ∧
    CursorStored (sourceOffset clauses source (index.val + 1)) (directory + 2 * index.val + 1) heap
  literals : ∀ index : Fin clauses.length,
    SourceStored clauses[index.val] (sourceOffset clauses source index.val) heap

/-- Physical headers are separate cells, outside the immutable source and
directory. Scratch starts after both immutable input regions. -/
structure Layout (clauses : List (Controller.CNF.Clause (Fin n))) where
  directory : Nat
  source : Nat
  base : Nat
  recordHeader : Nat
  inputHeader : Nat
  firstHeader : Nat
  directoryHeader : Nat
  endHeader : Nat
  directoryBefore : directory + 2 * clauses.length ≤ source
  sourceBefore : sourceOffset clauses source clauses.length ≤ base
  headersBefore : ∀ header ∈ [recordHeader, inputHeader, firstHeader, directoryHeader, endHeader], header < directory
  headersDistinct : [recordHeader, inputHeader, firstHeader, directoryHeader, endHeader].Nodup

/-- All old low heap words survive except the one physical source-cursor cell
which the pair reader updates. Allocation may increase the heap length. -/
def LowFrame (base changed : Nat) (before after : Array (Word width)) : Prop :=
  before.size ≤ after.size ∧ ∀ index, index < before.size → index < base → index ≠ changed →
    after[index]? = before[index]?

theorem LowFrame.refl (base changed : Nat) (heap : Array (Word width)) :
    LowFrame base changed heap heap := ⟨le_rfl, fun _ _ _ _ => rfl⟩

theorem LowFrame.trans {base changed : Nat} {first middle last : Array (Word width)}
    (left : LowFrame base changed first middle) (right : LowFrame base changed middle last) :
    LowFrame base changed first last := by
  refine ⟨left.1.trans right.1, ?_⟩
  intro index valid below different
  have middleValid : index < middle.size := lt_of_lt_of_le valid left.1
  exact (right.2 index middleValid below different).trans (left.2 index valid below different)

/-- A low immutable header is retained by the universal option-index frame. -/
theorem LowFrame.cursor {base changed header pointer : Nat} {before after : Array (Word width)}
    (frame : LowFrame base changed before after) (stored : CursorStored pointer header before)
    (below : header < base) (different : header ≠ changed) : CursorStored pointer header after :=
  Controller.Horn.JoinedNormalizeRow.cursor_of_option_frame stored frame.1
    (frame.2 header stored.bound below different)


/-- Source normalization has no instruction which mutates caller lists. -/
def CallerNeutral : Instruction width registers → Prop
  | .push _ | .pop _ | .emit _ => False
  | _ => True

theorem caller_step {instruction : Instruction width registers}
    {before after : State width registers}
    (neutral : CallerNeutral instruction) (transition : step instruction before = some after) :
    after.stack = before.stack ∧ after.output = before.output := by
  by_cases halted : before.halted = true
  · simp [step, halted] at transition
  have running : before.halted = false := Bool.eq_false_iff.mpr halted
  cases instruction
  case push src => exact False.elim neutral
  case pop dst => exact False.elim neutral
  case emit src => exact False.elim neutral
  case load dst address =>
    by_cases valid : (before.reg address).val < before.heap.size
    · simp only [step, running, Bool.false_eq_true, ite_false, dite_eq_left valid] at transition
      cases transition
      exact ⟨rfl, rfl⟩
    · simp [step, running, valid] at transition
  case store address src =>
    by_cases valid : (before.reg address).val < before.heap.size
    · simp only [step, running, Bool.false_eq_true, ite_false, dite_eq_left valid] at transition
      cases transition
      exact ⟨rfl, rfl⟩
    · simp [step, running, valid] at transition
  case allocate src =>
    by_cases room : before.heap.size < 2 ^ width
    · simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_left room] at transition
      cases transition
      exact ⟨rfl, rfl⟩
    · simp [step, running, room] at transition
  case release =>
    by_cases empty : before.heap.isEmpty = true
    · simp [step, running, empty] at transition
    · simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_right empty] at transition
      cases transition
      exact ⟨rfl, rfl⟩
  case branchZero src target =>
    by_cases zero : (before.reg src).val = 0
    · simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_left zero] at transition
      cases transition
      exact ⟨rfl, rfl⟩
    · simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_right zero] at transition
      cases transition
      exact ⟨rfl, rfl⟩
  all_goals
    simp only [step, running, Bool.false_eq_true, ite_false] at transition
    all_goals cases transition
    all_goals exact ⟨rfl, rfl⟩

/-- The instruction premise is discharged from the emitted normalizer code.
Caller preservation follows from each fetched step of the actual trace. -/
theorem caller_execution {program : Program width registers} {before after : State width registers}
    {ticks peak : Nat}
    (neutral : ∀ (position : Nat) (instruction : Instruction width registers), program[position]? = some instruction → CallerNeutral instruction)
    (trace : Execution program before after ticks peak) :
    after.stack = before.stack ∧ after.output = before.output := by
  induction trace with
  | refl state => exact ⟨rfl, rfl⟩
  | @cons state middle final count bound transition rest ih =>
    have first : middle.stack = state.stack ∧ middle.output = state.output := by
      unfold programStep at transition
      cases fetch : program[state.pc.val]? with
      | none => simp [fetch] at transition
      | some instruction =>
        have actual : step instruction state = some middle := by simpa [fetch] using transition
        exact caller_step (neutral state.pc.val instruction fetch) actual
    exact ⟨ih.1.trans first.1, ih.2.trans first.2⟩

theorem row_iteration_low_frame (destination : Program width 8) (entry base cursorHeader startHeader start exit : Nat)
    (clause : CNF.Clause (Fin n)) (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (row : Row n) (state : Controller.Cost.State width 8) (positiveCursor negativeCursor touchedCursor k : Nat)
    (invariant : Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor (k + 1) state)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ next : Controller.Cost.State width 8, ∃ ticks : Nat,
      Execution destination state next ticks state.liveWords ∧
      Invariant clause (row.record (clause[k]'(by have := invariant.indexBound; omega)))
        start cursorHeader startHeader base
        (positiveNext row (clause[k]'(by have := invariant.indexBound; omega)) positiveCursor)
        (negativeNext row (clause[k]'(by have := invariant.indexBound; omega)) negativeCursor)
        (touchedNext row (clause[k]'(by have := invariant.indexBound; omega)) touchedCursor) k next ∧
      next.pc = word width entry ∧ next.liveWords = state.liveWords ∧ next.heap.size = state.heap.size ∧ ticks ≤ 42 ∧ LowFrame base cursorHeader state.heap next.heap := by
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
    recordFrame, inputAfterCursor, cost⟩ :=
    physical_record_execution destination (entry + 6) cursorHeader (start + 2 * k) (entry + 46) base literal
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
  have retained : LowFrame base cursorHeader state.heap recorded.heap := by
    refine ⟨by have equal := recordSize.trans testedSize; omega, ?_⟩
    intro index valid below different
    have held := recordFrame index below
    have unchanged := Array.getElem?_set_ne (v := word width (start + 2 * k)) cursor.bound (Ne.symm different)
    have same : tested.heap[index]? = state.heap[index]? := by rw [testedHeap]
    exact (held.trans unchanged).trans same
  have nextInvariant : Invariant clause (row.record literal) start cursorHeader startHeader base
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
      (touchedNext row literal touchedCursor) k next := by
    refine ⟨by omega, preservedSource, inputAfterCursor, preservedFirst, recordStored,
      correct_record_drop clause row k bound invariant.correct,
      recordControl.zero, recordControl.trueHeld, recordControl.decrement, recordControl.running⟩
  have allTrace := (testTrace.append recordTrace).append returnTrace
  refine ⟨next, 6 + (10 + dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2) + 1,
    ?_, nextInvariant, rfl, ?_, ?_, by omega, retained⟩
  · simpa only [testedLive, recordLive, Nat.max_self] using allTrace
  · have : next.liveWords = recorded.liveWords := rfl
    exact this.trans (recordLive.trans testedLive)
  · exact recordSize.trans testedSize


theorem row_loop_low_frame (destination : Program width 8) (entry base cursorHeader startHeader start exit : Nat)
    (clause : CNF.Clause (Fin n)) (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (remaining : Nat) (row : Row n) (state : Controller.Cost.State width 8)
    (positiveCursor negativeCursor touchedCursor : Nat)
    (invariant : Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor remaining state)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8, ∃ result : Row n, ∃ positive negative touched ticks : Nat,
      Execution destination state final ticks state.liveWords ∧
      Invariant clause result start cursorHeader startHeader base positive negative touched 0 final ∧
      final.pc = word width exit ∧ final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧
      ticks ≤ 42 * remaining + 6 ∧ LowFrame base cursorHeader state.heap final.heap := by
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
      by simpa [final, testFinished, testPrepared, Controller.Cost.State.put, Controller.Cost.State.advance] using LowFrame.refl base cursorHeader state.heap⟩
  | succ remaining ih =>
    obtain ⟨middle, used, firstTrace, middleInvariant, middlePosition, middleLive, middleSize, usedBound, middleFrame⟩ :=
      row_iteration_low_frame destination entry base cursorHeader startHeader start exit clause present separate
        row state positiveCursor negativeCursor touchedCursor remaining invariant position capacity heapFits
    have bound : remaining < clause.length := by have := invariant.indexBound; omega
    let literal := clause[remaining]'bound
    obtain ⟨final, result, positive, negative, touched, ticks, restTrace, finalInvariant,
      finalPosition, finalLive, finalSize, ticksBound, finalFrame⟩ :=
      ih (row.record literal) middle (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor)
        middleInvariant middlePosition (by simpa only [middleSize] using heapFits)
    refine ⟨final, result, positive, negative, touched, used + ticks, ?_, finalInvariant,
      finalPosition, finalLive.trans middleLive, finalSize.trans middleSize, by omega, middleFrame.trans finalFrame⟩
    simpa only [middleLive, Nat.max_self] using firstTrace.append restTrace


theorem row_and_reuse_frames (program : Program width 8)
    (entry base inputHeader firstHeader recordHeader start pcur ncur tcur : Nat)
    (clause : Controller.CNF.Clause (Fin n))
    (neutral : ∀ (position : Nat) (instruction : Instruction width 8), program[position]? = some instruction → CallerNeutral instruction)
    (scanAt : RowAt program entry n base inputHeader firstHeader (entry + 77))
    (copyAt : Controller.Horn.JoinedRuleCopy.CodeAt program (entry + 77) base recordHeader n)
    (setupAt : Controller.Horn.ResetPointer.SetupAt program (entry + 119) (base + 2 * n + 2) base)
    (loopAt : Controller.Horn.ResetPointer.CodeAt program (entry + 122) (base + 5 * n + 4))
    (headersAt : Controller.Horn.ResetReuse.HeaderAt program (entry + 133) n base)
    (separate : Separation clause start inputHeader firstHeader base)
    (state : Controller.Cost.State width 8) (initialRow : Row n)
    (invariant : Invariant clause initialRow start inputHeader firstHeader base
      pcur ncur tcur clause.length state)
    (dual : Controller.Horn.DualHornClause clause)
    (recordCursor : CursorStored state.heap.size recordHeader state.heap)
    (recordBelow : recordHeader < base)
    (differentInput : recordHeader ≠ inputHeader)
    (differentFirst : recordHeader ≠ firstHeader)
    (recordOutside : recordHeader < start ∨ start + 2 * clause.length ≤ recordHeader)
    (position : state.pc = word width entry) (capacity : entry + 144 < 2 ^ width)
    (heapFits : state.heap.size + 3 + clause.length < 2 ^ width) :
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
      final.halted = false ∧ final.stack = state.stack ∧ final.output = state.output ∧
      (∀ index, index < state.heap.size → index < base → index ≠ inputHeader → index ≠ recordHeader →
        final.heap[index]? = state.heap[index]?) := by
  obtain ⟨scanned, normalized, positive, negative, touched, scanTicks, scanTrace,
    scannedInvariant, scannedPosition, scannedLive, scannedSize, scanBound, scanFrame⟩ :=
    row_loop_low_frame program entry base inputHeader firstHeader start (entry + 77)
      clause scanAt separate clause.length initialRow state pcur ncur tcur invariant
      position (by omega) (by omega)
  have correct : normalized.Correct clause := by simpa using scannedInvariant.correct
  have cursor : CursorStored scanned.heap.size recordHeader scanned.heap := by
    simpa only [scannedSize] using scanFrame.cursor recordCursor recordBelow differentInput
  have supported := supported_of_correct correct dual
  have fit : scanned.heap.size + 3 + normalized.positive.length < 2 ^ width := by
    have := positive_length_le correct
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
    source_of_option_frame scannedInvariant.source growing (by
      intro index lower upper
      apply frame index (by have := scannedInvariant.source.fits; omega)
        (Or.inl (by have := separate.sourceBefore; omega))
      rcases recordOutside with below | above <;> omega)
  have allTrace := scanTrace.append reuseTrace
  have caller := caller_execution neutral allTrace
  refine ⟨final, normalized,
    scanTicks + ((if normalized.tautology then 20 else 8 * normalized.positive.length + 31) +
      11 * normalized.touched.length + 17), ?_, ?_, correct, ?_, finalRecordCursor,
    emptyStored, clean, source, cursor_of_option_frame inputCursor growing inputHeld,
    cursor_of_option_frame scannedInvariant.first growing firstHeld, ?_, ?_, zero, one, decrement, running, caller.1, caller.2, ?_⟩
  · have trace := scanTrace.append reuseTrace
    have peakBound : state.liveWords ≤ scanned.liveWords + 3 + normalized.rule.positives.length := by
      rw [scannedLive]
      omega
    simp only [Nat.max_eq_right peakBound] at trace
    simpa only [scannedLive, semantic] using trace
  · have bound := row_cost_bound correct scanBound
    simpa only [Nat.add_assoc] using bound
  · simpa only [semantic, scannedSize] using record
  · simpa only [semantic, scannedSize] using size
  · simpa [Nat.add_assoc] using pc
  · intro index valid below differentInput differentRecord
    have scannedValid : index < scanned.heap.size := by rw [scannedSize]; exact valid
    exact (frame index scannedValid (Or.inl below) differentRecord).trans
      (scanFrame.2 index valid below differentInput)

end Controller.Horn.SourceDirectory
