module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.JoinedRuleFrame

@[expose] public section

/-!
# Physical source row normalization and record construction

A separate persistent record cursor is preserved through the actual backwards
source scan. It is stored below scratch and distinct from the input cursor,
so source occurrences, rule allocation and clean scratch reuse share one program.
-/
namespace Controller.Horn.JoinedNormalizeRow

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize
open Controller.Horn.RowScan Controller.Horn.SourceScan Controller.Horn.LiteralDispatch
open Controller.Horn.MarkStorage Controller.Horn.JoinedLiteral

theorem row_iteration_record_cursor (destination : Program width 8) (entry base cursorHeader startHeader start exit : Nat)
    (clause : CNF.Clause (Fin n)) (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (row : Row n) (state : Controller.Cost.State width 8) (positiveCursor negativeCursor touchedCursor k : Nat)
    (invariant : Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor (k + 1) state)
    (recordHeader recordStart : Nat)
    (recordCursor : CursorStored recordStart recordHeader state.heap)
    (recordBelow : recordHeader < base) (differentCursor : recordHeader ≠ cursorHeader)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ next : Controller.Cost.State width 8, ∃ ticks : Nat,
      Execution destination state next ticks state.liveWords ∧
      Invariant clause (row.record (clause[k]'(by have := invariant.indexBound; omega)))
        start cursorHeader startHeader base
        (positiveNext row (clause[k]'(by have := invariant.indexBound; omega)) positiveCursor)
        (negativeNext row (clause[k]'(by have := invariant.indexBound; omega)) negativeCursor)
        (touchedNext row (clause[k]'(by have := invariant.indexBound; omega)) touchedCursor) k next ∧
      next.pc = word width entry ∧ next.liveWords = state.liveWords ∧ next.heap.size = state.heap.size ∧ ticks ≤ 42 ∧ CursorStored recordStart recordHeader next.heap := by
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
  have testedRecord : CursorStored recordStart recordHeader tested.heap := by rw [testedHeap]; exact recordCursor
  have updatedRecord := CursorStored.after_store testedRecord cursorHeader cursor.bound
    (word width (start + 2 * k)) (Ne.symm differentCursor)
  have preservedRecord := CursorStored.of_low_frame updatedRecord recordBelow
    (by simpa using recordSize) recordFrame
  have nextInvariant : Invariant clause (row.record literal) start cursorHeader startHeader base
      (positiveNext row literal positiveCursor) (negativeNext row literal negativeCursor)
      (touchedNext row literal touchedCursor) k next := by
    refine ⟨by omega, preservedSource, inputAfterCursor, preservedFirst, recordStored,
      correct_record_drop clause row k bound invariant.correct,
      recordControl.zero, recordControl.trueHeld, recordControl.decrement, recordControl.running⟩
  have allTrace := (testTrace.append recordTrace).append returnTrace
  refine ⟨next, 6 + (10 + dynamicTicks (row.marks.read literal) (row.marks.read (CNF.negate literal)) literal.2) + 1,
    ?_, nextInvariant, rfl, ?_, ?_, by omega, preservedRecord⟩
  · simpa only [testedLive, recordLive, Nat.max_self] using allTrace
  · have : next.liveWords = recorded.liveWords := rfl
    exact this.trans (recordLive.trans testedLive)
  · exact recordSize.trans testedSize


theorem row_loop_record_cursor (destination : Program width 8) (entry base cursorHeader startHeader start exit : Nat)
    (clause : CNF.Clause (Fin n)) (present : RowAt destination entry n base cursorHeader startHeader exit)
    (separate : Separation clause start cursorHeader startHeader base)
    (remaining : Nat) (row : Row n) (state : Controller.Cost.State width 8)
    (positiveCursor negativeCursor touchedCursor : Nat)
    (invariant : Invariant clause row start cursorHeader startHeader base
      positiveCursor negativeCursor touchedCursor remaining state)
    (recordHeader recordStart : Nat)
    (recordCursor : CursorStored recordStart recordHeader state.heap)
    (recordBelow : recordHeader < base) (differentCursor : recordHeader ≠ cursorHeader)
    (position : state.pc = word width entry) (capacity : entry + 77 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8, ∃ result : Row n, ∃ positive negative touched ticks : Nat,
      Execution destination state final ticks state.liveWords ∧
      Invariant clause result start cursorHeader startHeader base positive negative touched 0 final ∧
      final.pc = word width exit ∧ final.liveWords = state.liveWords ∧ final.heap.size = state.heap.size ∧
      ticks ≤ 42 * remaining + 6 ∧ CursorStored recordStart recordHeader final.heap := by
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
      by simpa [final, testFinished, testPrepared, Controller.Cost.State.put, Controller.Cost.State.advance] using recordCursor⟩
  | succ remaining ih =>
    obtain ⟨middle, used, firstTrace, middleInvariant, middlePosition, middleLive, middleSize, usedBound, middleRecord⟩ :=
      row_iteration_record_cursor destination entry base cursorHeader startHeader start exit clause present separate
        row state positiveCursor negativeCursor touchedCursor remaining invariant recordHeader recordStart recordCursor recordBelow differentCursor position capacity heapFits
    have bound : remaining < clause.length := by have := invariant.indexBound; omega
    let literal := clause[remaining]'bound
    obtain ⟨final, result, positive, negative, touched, ticks, restTrace, finalInvariant,
      finalPosition, finalLive, finalSize, ticksBound, finalRecord⟩ :=
      ih (row.record literal) middle (positiveNext row literal positiveCursor)
        (negativeNext row literal negativeCursor) (touchedNext row literal touchedCursor)
        middleInvariant middleRecord middlePosition (by simpa only [middleSize] using heapFits)
    refine ⟨final, result, positive, negative, touched, used + ticks, ?_, finalInvariant,
      finalPosition, finalLive.trans middleLive, finalSize.trans middleSize, by omega, finalRecord⟩
    simpa only [middleLive, Nat.max_self] using firstTrace.append restTrace


theorem positive_length_le {clause : Controller.CNF.Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) : row.positive.length ≤ clause.length := by
  rw [correct.positive]
  have dedup := (List.dedup_sublist
    ((clause.filter fun literal => decide (literal.2 = true)).map Prod.fst)).length_le
  have filtered : (clause.filter fun literal => decide (literal.2 = true)).length ≤ clause.length :=
    List.Sublist.length_le List.filter_sublist
  have shortened : ((clause.filter fun literal => decide (literal.2 = true)).map Prod.fst).dedup.length ≤
      (clause.filter fun literal => decide (literal.2 = true)).length := by
    simpa only [List.length_map] using dedup
  exact shortened.trans filtered

/-- The supported-row premise is derived from the source dual-Horn clause,
including tautologies and duplicate occurrences of a single negative head. -/
theorem supported_of_correct {clause : Controller.CNF.Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) (dual : Controller.Horn.DualHornClause clause) :
    Controller.Horn.RuleDispatch.Supported row := by
  rcases dual with tautology | unique
  · exact Or.inl (correct.tautology.trans ((Controller.Horn.Worklist.tautologyCheck_eq_true clause).mpr tautology))
  · apply Or.inr
    rw [correct.negative]
    cases labels : Controller.Horn.Worklist.signedLabels clause false with
    | nil => simp
    | cons head tail =>
      have nodup := Controller.Horn.Worklist.signedLabels_nodup clause false
      rw [labels] at nodup
      have headMember : (head, false) ∈ clause :=
        (Controller.Horn.Worklist.mem_signedLabels clause false head).mp (by rw [labels]; simp)
      have tailEmpty : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro label member
        have labelMember : (label, false) ∈ clause :=
          (Controller.Horn.Worklist.mem_signedLabels clause false label).mp (by rw [labels]; simp [member])
        have equal := unique (head, false) headMember (label, false) labelMember rfl rfl
        change head = label at equal
        have notHead : head ∉ tail := (List.nodup_cons.mp nodup).1
        rw [← equal] at member
        exact notHead member
      simp [tailEmpty]

/-- Each physical source occurrence is charged once by the scan and at most
once by each bounded-size positive/touched refinement. -/
theorem row_cost_bound {clause : Controller.CNF.Clause (Fin n)} {row : Row n} {ticks : Nat}
    (correct : row.Correct clause) (scanBound : ticks ≤ 42 * clause.length + 6) :
    ticks + (if row.tautology then 20 else 8 * row.positive.length + 31) +
      11 * row.touched.length + 17 ≤ 61 * clause.length + 54 := by
  have positive := positive_length_le correct
  have touched := Row.touched_length_le correct
  cases row.tautology <;> simp <;> omega


/-- Option-index frames transport a physically stored cursor across allocation. -/
theorem cursor_of_option_frame {before after : Array (Word width)} {pointer header : Nat}
    (stored : CursorStored pointer header before) (size : before.size ≤ after.size)
    (held : after[header]? = before[header]?) : CursorStored pointer header after := by
  have bound : header < after.size := by have := stored.bound; omega
  refine ⟨bound, ?_⟩
  have value : after[header]'bound = before[header]'stored.bound := by
    simpa only [Array.getElem?_eq_getElem bound,
      Array.getElem?_eq_getElem stored.bound, Option.some.injEq] using held
  exact value.trans stored.value

/-- All original literal words survive copy and reset; no source occurrence is
replaced by its deduplicated semantic label. -/
theorem source_of_option_frame {before after : Array (Word width)}
    {clause : Controller.CNF.Clause (Fin n)} {start : Nat}
    (stored : SourceStored clause start before) (size : before.size ≤ after.size)
    (held : ∀ index, start ≤ index → index < start + 2 * clause.length →
      after[index]? = before[index]?) : SourceStored clause start after := by
  refine ⟨by have := stored.fits; omega, ?_⟩
  intro index
  have old := stored.entry index
  have first : start + 2 * index.val < before.size := by have := old.fits; omega
  have second : start + 2 * index.val + 1 < before.size := by have := old.fits; omega
  have firstAfter : start + 2 * index.val < after.size := by omega
  have secondAfter : start + 2 * index.val + 1 < after.size := by omega
  have firstValue : after[start + 2 * index.val]'firstAfter = before[start + 2 * index.val]'first := by
    have eq := held (start + 2 * index.val) (by omega) (by have := index.isLt; omega)
    simpa only [Array.getElem?_eq_getElem firstAfter,
      Array.getElem?_eq_getElem first, Option.some.injEq] using eq
  have secondValue : after[start + 2 * index.val + 1]'secondAfter = before[start + 2 * index.val + 1]'second := by
    have eq := held (start + 2 * index.val + 1) (by omega) (by have := index.isLt; omega)
    simpa only [Array.getElem?_eq_getElem secondAfter,
      Array.getElem?_eq_getElem second, Option.some.injEq] using eq
  exact ⟨by have := old.fits; omega, firstValue.trans old.label, secondValue.trans old.polarity⟩

/-- One complete fetched row block: physical backwards source traversal,
dual-Horn record construction, touched-label reset and clean header reuse.
The source cursor advances to the source start, while the independent rule
cursor advances over the newly allocated record. -/
theorem normalize_row_and_reuse (program : Program width 8)
    (entry base inputHeader firstHeader recordHeader start pcur ncur tcur : Nat)
    (clause : Controller.CNF.Clause (Fin n))
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
      final.halted = false := by
  obtain ⟨scanned, normalized, positive, negative, touched, scanTicks, scanTrace,
    scannedInvariant, scannedPosition, scannedLive, scannedSize, scanBound, scannedCursor⟩ :=
    row_loop_record_cursor program entry base inputHeader firstHeader start (entry + 77)
      clause scanAt separate clause.length initialRow state pcur ncur tcur invariant
      recordHeader state.heap.size recordCursor recordBelow differentInput position (by omega) (by omega)
  have correct : normalized.Correct clause := by simpa using scannedInvariant.correct
  have cursor : CursorStored scanned.heap.size recordHeader scanned.heap := by
    simpa only [scannedSize] using scannedCursor
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
  refine ⟨final, normalized,
    scanTicks + ((if normalized.tautology then 20 else 8 * normalized.positive.length + 31) +
      11 * normalized.touched.length + 17), ?_, ?_, correct, ?_, finalRecordCursor,
    emptyStored, clean, source, cursor_of_option_frame inputCursor growing inputHeld,
    cursor_of_option_frame scannedInvariant.first growing firstHeld, ?_, ?_, zero, one, decrement, running⟩
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

end Controller.Horn.JoinedNormalizeRow

