module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexScanWhole

@[expose] public section

/-! The original-record outer scan carries the fixed physical end header
through each fetched setup, body and return. -/
namespace Controller.Horn.IndexScanOuter
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.IndexScanLoop
open Controller.Horn.IndexScanRefinement Controller.Horn.IndexScanWhole
variable {width n : Nat}

theorem setup_row_header (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (rowBound : rowIndex < clauses.length)
    (physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed state.heap)
    (processedEq : processed = (IndexScan.occurrences (clauses.take rowIndex) recordStart).length)
    (headerBound : base + 2 * n < state.heap.size)
    (rowHeld : state.reg 1 = word width (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex))
    (allocationHeld : state.reg 7 = word width state.heap.size)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (position : state.pc = word width (entry + 6)) (running : state.halted = false)
    (positiveBase : 0 < base)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex 0 processed final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap := by
  let row := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex
  let rule := Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)
  let final := IndexScan.rowFinished state entry base row rule.positives.length headerBound
  have stored := physical.records ⟨rowIndex, rowBound⟩
  have trace := IndexScan.row_setup_execution program entry base recordStart row rule state present
    stored headerBound rowHeld one position running capacity room
  have finalSize : final.heap.size = state.heap.size := by
    change (state.heap.set (base + 2 * n) (word width (row + 3 + rule.positives.length)) headerBound).size = state.heap.size
    simp
  have finalHeader : Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap := by
    refine ⟨by rw [finalSize]; exact header.bound, ?_⟩
    change (state.heap.set (base + 2 * n) (word width (row + 3 + rule.positives.length))
      headerBound)[0]'(by simpa only [Array.size_set] using header.bound) = word width recordEnd
    exact (Array.getElem_set_ne headerBound header.bound (by omega)).trans header.value
  refine ⟨final, trace, ?_, finalSize, rfl, rfl, finalHeader⟩
  refine ⟨rowBound, by omega, by simpa using processedEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · exact header_index clauses recordStart recordEnd base processed (row + 3 + rule.positives.length)
      state.heap physical headerBound
  · rfl
  · exact rowHeld
  · change state.reg 7 = word width (state.heap.set (base + 2 * n)
      (word width (row + 3 + rule.positives.length)) headerBound).size
    simpa only [Array.size_set] using allocationHeld
  · exact zero
  · exact one
  · refine ⟨by rw [finalSize]; exact headerBound, ?_⟩
    change (state.heap.set (base + 2 * n) (word width (row + 3 + rule.positives.length))
      headerBound)[base + 2 * n]'(by simpa only [Array.size_set] using headerBound) = _
    simp [row, rule]

theorem terminal_row_header (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (complete : consumed = (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      RowDone clauses recordStart recordEnd base entry rowIndex processed 0 state final ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap := by
  let limit := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex + 3 + consumed
  have source : state.reg 0 = word width limit := invariant.sourceHeld
  have endpoint : Controller.Horn.SourceScan.CursorStored limit (base + 2 * n) state.heap := by
    simpa only [limit, complete] using invariant.endpoint
  have fits : limit < 2 ^ width := by
    have stored := (invariant.physical.records ⟨rowIndex, invariant.rowBound⟩).fits
    simp only [Fin.val_mk] at stored
    dsimp [limit]
    omega
  let tested := IndexScan.testFinished state (base + 2 * n) limit limit (entry + 30)
  have first := IndexScan.test_execution program (entry + 14) (base + 2 * n) limit limit (entry + 30)
    0 state (body_test_at program entry base recordStart present) invariant.position invariant.running
    endpoint.bound endpoint.value source (by decide) (by decide) (by omega) (by have := endpoint.bound; omega) fits fits
  have testedPosition : tested.pc = word width (entry + 30) := by
    simpa [tested] using IndexScan.test_position state (entry + 14) (base + 2 * n) limit limit
      (entry + 30) invariant.position (by omega) fits fits
  have testedRunning : tested.halted = false := by simpa [tested] using invariant.running
  have testedZero : tested.reg 2 = word width 0 :=
    (test_reg state _ _ _ _ 2 (by decide) (by decide)).trans invariant.zero
  let final := rowExitFinished tested entry
  have second := row_exit_execution program entry base recordStart present tested testedPosition testedRunning capacity
  have frame := row_exit_frame tested entry
  have heap : final.heap = state.heap := frame.2.2.2.2.2.1.trans (test_heap state _ _ _ _)
  have finalHeader : Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap := by
    simpa only [heap] using header
  refine ⟨final, by simpa [tested, test_live] using first.append second, ?_, finalHeader⟩
  refine ⟨?_, row_exit_position tested entry testedZero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heap]; exact invariant.physical
  · rw [frame.1, test_reg state _ _ _ _ 0 (by decide) (by decide), source]
    have next := Controller.Horn.NormalizeLoop.recordOffset_succ clauses recordStart rowIndex invariant.rowBound
    simpa [limit, complete] using congrArg (word width) next.symm
  · rw [frame.2.2.1, test_reg state _ _ _ _ 7 (by decide) (by decide), heap]
    exact invariant.allocationHeld
  · exact frame.2.2.2.1.trans (test_reg state _ _ _ _ 2 (by decide) (by decide))
  · exact frame.2.2.2.2.1.trans (test_reg state _ _ _ _ 5 (by decide) (by decide))
  · simp [heap]
  · exact frame.2.2.2.2.2.2.1.trans (test_stack state _ _ _ _)
  · exact frame.2.2.2.2.2.2.2.1.trans (test_output state _ _ _ _)
  · exact frame.2.2.2.2.2.2.2.2.trans testedRunning

theorem indexed_row_suffix_header (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed count : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (complete : consumed + count =
      (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (positiveBase : 0 < base)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 * count < 2 ^ width) :
    ∃ final, Execution program state final (16 * count + 6) (state.liveWords + 2 * count) ∧
      RowDone clauses recordStart recordEnd base entry rowIndex (processed + count) count state final ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap := by
  obtain ⟨middle, first, next, growth, stack, output, middleHeader⟩ := indexed_body_prefix_header program clauses
    recordStart recordEnd base entry rowIndex present capacity positiveBase count consumed processed state invariant header (by omega) room
  obtain ⟨final, second, result, finalHeader⟩ := terminal_row_header program clauses recordStart recordEnd base entry rowIndex
    (consumed + count) (processed + count) middle present next complete middleHeader capacity (by omega)
  have middleLive : middle.liveWords = state.liveWords + 2 * count := by
    unfold State.liveWords
    rw [growth, stack, output]
    omega
  refine ⟨final, ?_, ?_, finalHeader⟩
  · have trace := first.append second
    rw [middleLive, Nat.max_self] at trace
    exact trace
  · refine ⟨result.physical, result.position, result.rowHeld, result.allocationHeld,
      result.zero.trans (next.zero.trans invariant.zero.symm),
      result.one.trans (next.one.trans invariant.one.symm), ?_,
      result.stack.trans stack, result.output.trans output, result.running⟩
    have := result.growth
    omega

structure OuterInvariant (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex processed : Nat) (state : State width 8) : Prop where
  rowBound : rowIndex ≤ clauses.length
  processedEq : processed = (IndexScan.occurrences (clauses.take rowIndex) recordStart).length
  physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed state.heap
  header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap
  rowHeld : state.reg 1 = word width (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex)
  allocationHeld : state.reg 7 = word width state.heap.size
  zero : state.reg 2 = word width 0
  one : state.reg 5 = word width 1
  position : state.pc = word width (entry + 2)
  running : state.halted = false

/-- One original row costs its fetched outer test, physical count setup,
recursive incidence body, terminal test and row-return branch. -/
theorem outer_row (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : OuterInvariant clauses recordStart recordEnd base entry rowIndex processed state)
    (rowBound : rowIndex < clauses.length) (positiveBase : 0 < base)
    (capacity : entry + 32 < 2 ^ width)
    (room : state.heap.size + 2 *
      (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length < 2 ^ width) :
    let count := (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length
    ∃ final, Execution program state final (16 * count + 18) (state.liveWords + 2 * count) ∧
      OuterInvariant clauses recordStart recordEnd base entry (rowIndex + 1) (processed + count) final ∧
      final.heap.size = state.heap.size + 2 * count ∧ final.stack = state.stack ∧ final.output = state.output := by
  dsimp only
  let row := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex
  let count := (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length
  have ending : recordEnd ≤ state.heap.size := by have := invariant.physical.endpoint; omega
  have rowBefore : row < recordEnd := by
    rw [invariant.physical.originalEnd]
    exact recordOffset_before_end clauses recordStart rowIndex rowBound
  have fits : recordEnd < 2 ^ width := by omega
  let tested := IndexScan.testFinished state 0 row recordEnd (entry + 32)
  have first := IndexScan.test_execution program (entry + 2) 0 row recordEnd (entry + 32) 1 state
    (outer_test_at program entry base recordStart present) invariant.position invariant.running
    invariant.header.bound invariant.header.value invariant.rowHeld (by decide) (by decide)
    (by omega) (by omega) (by omega) fits
  have testedPosition : tested.pc = word width (entry + 6) := by
    simpa [tested, Nat.ne_of_lt rowBefore] using IndexScan.test_position state (entry + 2) 0 row recordEnd
      (entry + 32) invariant.position (by omega) (by omega) fits
  have testedPhysical : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed tested.heap := by
    simpa [tested] using invariant.physical
  have testedHeader : Controller.Horn.SourceScan.CursorStored recordEnd 0 tested.heap := by
    simpa [tested] using invariant.header
  have headerBound : base + 2 * n < tested.heap.size := by
    have := invariant.physical.separation
    have := Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart clauses.length
    have := invariant.physical.originalEnd
    simp only [tested, test_heap]
    omega
  obtain ⟨middle, second, body, growth, stack, output, middleHeader⟩ := setup_row_header program clauses
    recordStart recordEnd base entry rowIndex processed tested present rowBound testedPhysical invariant.processedEq
    headerBound ((test_reg state _ _ _ _ 1 (by decide) (by decide)).trans invariant.rowHeld)
    (by simpa [tested] using (test_reg state _ _ _ _ 7 (by decide) (by decide)).trans invariant.allocationHeld)
    ((test_reg state _ _ _ _ 2 (by decide) (by decide)).trans invariant.zero)
    ((test_reg state _ _ _ _ 5 (by decide) (by decide)).trans invariant.one)
    testedPosition (by simpa [tested] using invariant.running) positiveBase testedHeader capacity
    (by simpa [tested] using (show state.heap.size < 2 ^ width by omega))
  obtain ⟨final, third, result, finalHeader⟩ := indexed_row_suffix_header program clauses
    recordStart recordEnd base entry rowIndex 0 processed count middle present body (by simp [count])
    positiveBase middleHeader capacity (by rw [growth]; simpa [tested] using room)
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [growth, stack, output]
    simp [tested]
  refine ⟨final, ?_, ?_, ?_, result.stack.trans (stack.trans (test_stack state _ _ _ _)),
    result.output.trans (output.trans (test_output state _ _ _ _))⟩
  · have trace := (first.append second).append third
    rw [middleLive] at trace
    convert trace using 1 <;> simp [tested, test_live] <;> omega
  · refine ⟨by omega, ?_, result.physical, finalHeader, result.rowHeld, result.allocationHeld,
      result.zero.trans body.zero, result.one.trans body.one, result.position, result.running⟩
    have next := prefix_occurrences_succ clauses recordStart rowIndex rowBound
    rw [next]
    rw [invariant.processedEq]
  · have := result.growth
    simpa [tested] using this.trans (congrArg (fun size => size + 2 * count) growth)

theorem prefix_length_le (clauses : List (Controller.CNF.Clause (Fin n))) (start index : Nat) :
    (IndexScan.occurrences (clauses.take index) start).length ≤ (IndexScan.occurrences clauses start).length := by
  have partition := congrArg List.length (occurrences_split clauses start index)
  simp only [List.length_append] at partition
  omega

structure ScanDone (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry count : Nat) (before after : State width 8) : Prop where
  physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base
    (IndexScan.occurrences clauses recordStart).length after.heap
  header : Controller.Horn.SourceScan.CursorStored recordEnd 0 after.heap
  position : after.pc = word width (entry + 32)
  allocationHeld : after.reg 7 = word width after.heap.size
  zero : after.reg 2 = before.reg 2
  one : after.reg 5 = before.reg 5
  growth : after.heap.size = before.heap.size + 2 * count
  stack : after.stack = before.stack
  output : after.output = before.output
  running : after.halted = false

/-- All remaining original rows execute in succession. The only incidence count
is a ghost specification of the links actually produced by the fixed program. -/
theorem outer_suffix (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (positiveBase : 0 < base) (capacity : entry + 32 < 2 ^ width)
    (rows rowIndex processed : Nat) (state : State width 8)
    (invariant : OuterInvariant clauses recordStart recordEnd base entry rowIndex processed state)
    (complete : rowIndex + rows = clauses.length)
    (room : state.heap.size + 2 * ((IndexScan.occurrences clauses recordStart).length - processed) < 2 ^ width) :
    ∃ final, Execution program state final
      (16 * ((IndexScan.occurrences clauses recordStart).length - processed) + 18 * rows + 4)
      (state.liveWords + 2 * ((IndexScan.occurrences clauses recordStart).length - processed)) ∧
      ScanDone clauses recordStart recordEnd base entry
        ((IndexScan.occurrences clauses recordStart).length - processed) state final := by
  induction rows generalizing rowIndex processed state with
  | zero =>
      have lastRow : rowIndex = clauses.length := by omega
      have allProcessed : processed = (IndexScan.occurrences clauses recordStart).length := by
        simpa only [lastRow, List.take_length] using invariant.processedEq
      have rowEnd : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex = recordEnd := by
        rw [lastRow, ← invariant.physical.originalEnd]
      let final := IndexScan.testFinished state 0 recordEnd recordEnd (entry + 32)
      have fits : recordEnd < 2 ^ width := by have := invariant.physical.endpoint; omega
      have trace := IndexScan.test_execution program (entry + 2) 0 recordEnd recordEnd (entry + 32) 1 state
        (outer_test_at program entry base recordStart present) invariant.position invariant.running
        invariant.header.bound invariant.header.value (by simpa only [rowEnd] using invariant.rowHeld)
        (by decide) (by decide) (by omega) (by omega) fits fits
      refine ⟨final, by simpa [allProcessed] using trace, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [final, allProcessed] using invariant.physical
      · simpa [final] using invariant.header
      · simpa [final] using IndexScan.test_position state (entry + 2) 0 recordEnd recordEnd (entry + 32)
          invariant.position (by omega) fits fits
      · simpa [final] using (test_reg state _ _ _ _ 7 (by decide) (by decide)).trans invariant.allocationHeld
      · exact test_reg state _ _ _ _ 2 (by decide) (by decide)
      · exact test_reg state _ _ _ _ 5 (by decide) (by decide)
      · simp [final, allProcessed]
      · simp [final]
      · simp [final]
      · simpa [final] using invariant.running
  | succ rows ih =>
      have rowBound : rowIndex < clauses.length := by omega
      let count := (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length
      have nextPrefix := prefix_occurrences_succ clauses recordStart rowIndex rowBound
      have prefixBound := prefix_length_le clauses recordStart (rowIndex + 1)
      have incidenceRoom : state.heap.size + 2 * count < 2 ^ width := by
        have := invariant.processedEq
        dsimp [count]
        omega
      obtain ⟨middle, first, next, growth, stack, output⟩ := outer_row program clauses
        recordStart recordEnd base entry rowIndex processed state present invariant rowBound positiveBase capacity incidenceRoom
      have physicalBound : processed + count ≤ (IndexScan.occurrences clauses recordStart).length := next.physical.prefixBound
      obtain ⟨final, tail, result⟩ := ih (rowIndex + 1) (processed + count) middle next (by omega) (by omega)
      have middleLive : middle.liveWords = state.liveWords + 2 * count := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_⟩
      · have trace := first.append tail
        rw [middleLive] at trace
        convert trace using 1 <;> omega
      · refine ⟨result.physical, result.header, result.position, result.allocationHeld,
          result.zero.trans (next.zero.trans invariant.zero.symm),
          result.one.trans (next.one.trans invariant.one.symm), ?_,
          result.stack.trans stack, result.output.trans output, result.running⟩
        have := result.growth
        omega

/-- The complete relocated 32-instruction scan begins with its fetched two
startup instructions and ends with the final physical row-end comparison. -/
theorem all_rows (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base 0 state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (positiveBase : 0 < base) (position : state.pc = word width entry)
    (running : state.halted = false) (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (capacity : entry + 32 < 2 ^ width)
    (room : state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length < 2 ^ width) :
    ∃ final, Execution program state final
      (16 * (IndexScan.occurrences clauses recordStart).length + 18 * clauses.length + 6)
      (state.liveWords + 2 * (IndexScan.occurrences clauses recordStart).length) ∧
      ScanDone clauses recordStart recordEnd base entry (IndexScan.occurrences clauses recordStart).length state final := by
  have heapEnd : state.heap.size = recordEnd := by simpa using physical.endpoint
  have initialHeader : Controller.Horn.SourceScan.CursorStored state.heap.size 0 state.heap := by
    simpa only [heapEnd] using header
  have first := IndexScan.startup_execution program entry base recordStart state present initialHeader
    position running zero capacity (by omega)
  let middle := IndexScan.started state recordStart
  have frame := IndexScan.started_frame state recordStart
  have middleInvariant : OuterInvariant clauses recordStart recordEnd base entry 0 0 middle := by
    refine ⟨by omega, by simp [IndexScan.occurrences], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [middle, frame.1] using physical
    · simpa only [middle, frame.1] using header
    · simpa [Controller.Horn.NormalizeLoop.recordOffset] using frame.2.2.2.1
    · simpa only [middle, frame.1] using frame.2.2.2.2.1
    · exact (frame.2.2.2.2.2 2 (by decide) (by decide)).trans zero
    · exact (frame.2.2.2.2.2 5 (by decide) (by decide)).trans one
    · simp [middle, IndexScan.started, State.advance, State.put, position,
        show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega),
        show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
    · simpa [middle, IndexScan.started, State.advance, State.put] using running
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [frame.1, frame.2.1, frame.2.2.1]
  obtain ⟨final, tail, result⟩ := outer_suffix program clauses recordStart recordEnd base entry present
    positiveBase capacity clauses.length 0 0 middle middleInvariant (by omega) (by simpa [middle, frame.1] using room)
  refine ⟨final, ?_, result.physical, result.header, result.position, result.allocationHeld,
    result.zero.trans (frame.2.2.2.2.2 2 (by decide) (by decide)),
    result.one.trans (frame.2.2.2.2.2 5 (by decide) (by decide)), ?_,
    result.stack.trans frame.2.1, result.output.trans frame.2.2.1, result.running⟩
  · have trace := first.append tail
    rw [middleLive] at trace
    convert trace using 1 <;> simp only [Nat.sub_zero] <;> omega
  · simpa only [Nat.sub_zero, middle, frame.1] using result.growth

end Controller.Horn.IndexScanOuter
