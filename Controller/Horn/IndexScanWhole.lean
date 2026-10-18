module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexScanRefinement

@[expose] public section

/-! Composition of the fetched body with its physical endpoint test and row
return. All index specifications refer to the original immutable source rows. -/
namespace Controller.Horn.IndexScanWhole
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.IndexScanLoop
open Controller.Horn.IndexScanRefinement
variable {width n : Nat}

/-- Packed original records grow strictly by their three headers and retained
body length, so the outer cursor cannot equal the final end prematurely. -/
theorem recordOffset_mono (clauses : List (Controller.CNF.Clause (Fin n)))
    (start lower upper : Nat) (ordered : lower ≤ upper) (bound : upper ≤ clauses.length) :
    Controller.Horn.NormalizeLoop.recordOffset clauses start lower ≤
      Controller.Horn.NormalizeLoop.recordOffset clauses start upper := by
  induction upper generalizing lower with
  | zero =>
      have lowerZero : lower = 0 := by omega
      subst lower
      exact Nat.le_refl _
  | succ upper ih =>
      by_cases equal : lower = upper + 1
      · subst lower; exact Nat.le_refl _
      · have previous := ih lower (by omega) (by omega)
        rw [Controller.Horn.NormalizeLoop.recordOffset_succ clauses start upper (by omega)]
        omega

theorem recordOffset_before_end (clauses : List (Controller.CNF.Clause (Fin n)))
    (start index : Nat) (bound : index < clauses.length) :
    Controller.Horn.NormalizeLoop.recordOffset clauses start index <
      Controller.Horn.NormalizeLoop.recordOffset clauses start clauses.length := by
  have next := recordOffset_mono clauses start (index + 1) clauses.length (by omega) (by omega)
  rw [Controller.Horn.NormalizeLoop.recordOffset_succ clauses start index bound] at next
  omega

/-- Saving the fetched row endpoint modifies only the dedicated scratch header;
all original records, bucket heads and previously allocated links survive. -/
theorem header_index (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base processed value : Nat) (heap : Array (Word width))
    (index : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed heap)
    (bound : base + 2 * n < heap.size) :
    IndexScan.PhysicalIndex clauses recordStart recordEnd base processed
      (heap.set (base + 2 * n) (word width value) bound) := by
  have ending : recordStart ≤ recordEnd := by
    rw [index.originalEnd]
    exact Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart clauses.length
  have frame (position : Nat) (above : recordStart ≤ position) :
      (heap.set (base + 2 * n) (word width value) bound)[position]? = heap[position]? := by
    have different : position ≠ base + 2 * n := by have := index.separation; omega
    simp [Array.getElem?_set, Ne.symm different]
  refine ⟨index.prefixBound, by simpa using index.endpoint, ?_, ?_, ?_,
    index.originalEnd, index.separation, index.positiveEnd⟩
  · intro label
    have different : headAddress base label ≠ base + 2 * n := by
      have := label.isLt; unfold headAddress; omega
    simpa [Array.getElem?_set, Ne.symm different] using index.headValues label
  · intro item
    apply node_frame _ _ _ heap _ (index.nodes item) (by simp)
    intro position above inside
    exact frame position (by omega)
  · intro row
    apply IndexScan.record_frame _ _ heap _ (index.records row) (by simp)
    intro position above inside
    exact frame position (by
      have := Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart row.val
      omega)

/-- The fetched setup reads the count from the current original physical row
and stores its endpoint before constructing the body cursor invariant. -/
theorem setup_row (program : Program width 8)
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
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex 0 processed final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  let row := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex
  let rule := Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)
  let final := IndexScan.rowFinished state entry base row rule.positives.length headerBound
  have stored := physical.records ⟨rowIndex, rowBound⟩
  have trace := IndexScan.row_setup_execution program entry base recordStart row rule state present
    stored headerBound rowHeld one position running capacity room
  have finalSize : final.heap.size = state.heap.size := by
    change (state.heap.set (base + 2 * n) (word width (row + 3 + rule.positives.length)) headerBound).size = state.heap.size
    simp
  refine ⟨final, trace, ?_, finalSize, rfl, rfl⟩
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

structure RowDone (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex processed count : Nat)
    (before after : State width 8) : Prop where
  physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed after.heap
  position : after.pc = word width (entry + 2)
  rowHeld : after.reg 1 = word width (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart (rowIndex + 1))
  allocationHeld : after.reg 7 = word width after.heap.size
  zero : after.reg 2 = before.reg 2
  one : after.reg 5 = before.reg 5
  growth : after.heap.size = before.heap.size + 2 * count
  stack : after.stack = before.stack
  output : after.output = before.output
  running : after.halted = false

/-- The terminal comparison and actual two-instruction row return preserve the
full original-source physical index and move to the next packed record. -/
theorem terminal_row (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (complete : consumed = (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      RowDone clauses recordStart recordEnd base entry rowIndex processed 0 state final := by
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
  refine ⟨final, by simpa [tested, test_live] using first.append second, ?_⟩
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

/-- The entire remaining physical row body, including its terminal test and
return, carries the original occurrence index through actual recursive steps. -/
theorem indexed_row_suffix (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed count : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (complete : consumed + count =
      (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 * count < 2 ^ width) :
    ∃ final, Execution program state final (16 * count + 6) (state.liveWords + 2 * count) ∧
      RowDone clauses recordStart recordEnd base entry rowIndex (processed + count) count state final := by
  obtain ⟨middle, first, next, growth, stack, output⟩ := indexed_body_prefix program clauses
    recordStart recordEnd base entry rowIndex present capacity count consumed processed state invariant (by omega) room
  obtain ⟨final, second, result⟩ := terminal_row program clauses recordStart recordEnd base entry rowIndex
    (consumed + count) (processed + count) middle present next complete capacity (by omega)
  have middleLive : middle.liveWords = state.liveWords + 2 * count := by
    unfold State.liveWords
    rw [growth, stack, output]
    omega
  refine ⟨final, ?_, result.physical, result.position, result.rowHeld, result.allocationHeld,
    result.zero.trans (next.zero.trans invariant.zero.symm),
    result.one.trans (next.one.trans invariant.one.symm), ?_,
    result.stack.trans stack, result.output.trans output, result.running⟩
  · have trace := first.append second
    rw [middleLive, Nat.max_self] at trace
    exact trace
  · have := result.growth
    omega

/-- The concrete cold serializer reserves all five headers before scratch. -/
theorem cold_base_positive (clauses : List (Controller.CNF.Clause (Fin n))) :
    0 < (Controller.Horn.SourceSerialize.layout clauses).base := by
  simp [Controller.Horn.SourceSerialize.layout, Controller.Horn.SourceSerialize.base,
    Controller.Horn.SourceSerialize.source]

/-- The fixed original record-end header is carried through every actual
insertion, rather than restored or supplied again at the next outer test. -/
theorem indexed_body_step_header (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (remaining : consumed < (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (positiveBase : 0 < base)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width) :
    ∃ final, Execution program state final 16 (state.liveWords + 2) ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex (consumed + 1) (processed + 1) final ∧
      final.heap.size = state.heap.size + 2 ∧ final.stack = state.stack ∧ final.output = state.output ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap := by
  let rule := Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))
  let row := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex
  let pointer := row + 3 + consumed
  let limit := row + 3 + rule.positives.length
  let label : Fin n := rule.positives[consumed]
  let previous := IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take processed) label
  have buckets := buckets_of_index clauses recordStart recordEnd base processed state.heap invariant.physical (by omega)
  have headBound := buckets.bound label
  have stored := invariant.physical.records ⟨rowIndex, invariant.rowBound⟩
  obtain ⟨bodyBound, source⟩ := row_source clauses recordStart recordEnd base entry rowIndex consumed processed state
    invariant remaining
  have head : state.heap[headAddress base label]'headBound = word width previous := by
    have cell := invariant.physical.headValues label
    rw [Array.getElem?_eq_getElem headBound] at cell
    exact Option.some.inj cell
  have previousBound : previous < state.heap.size := by
    have bound := IndexScan.heads_bound recordEnd invariant.physical.positiveEnd ((IndexScan.occurrences clauses recordStart).take processed)
      label
    rw [List.length_take_of_le invariant.physical.prefixBound, ← invariant.physical.endpoint] at bound
    exact bound
  have rowBound : row < state.heap.size := by have fits := stored.fits; simp only [Fin.val_mk] at fits; dsimp [row]; omega
  let final := bodyFinished state entry base pointer limit row previous label headBound
  have trace := body_execution program entry base recordStart pointer limit row previous state label present
    invariant.position invariant.running invariant.endpoint.bound invariant.endpoint.value bodyBound headBound source head
    previousBound rowBound invariant.sourceHeld invariant.rowHeld invariant.allocationHeld invariant.zero invariant.one
    (by dsimp [pointer, limit, rule]; omega) (by have fits := stored.fits; simp only [Fin.val_mk] at fits; dsimp [limit, row, rule]; omega)
    capacity room
  have frame := body_frame state entry base pointer limit row previous label headBound
  have heap := body_heap state entry base pointer limit row previous label headBound
  have fetched := occurrence_at_row clauses recordStart rowIndex consumed invariant.rowBound remaining
  rw [← invariant.processedEq] at fetched
  obtain ⟨available, original⟩ := List.getElem?_eq_some_iff.mp fetched
  have nextIndex := index_after clauses recordStart recordEnd base processed row state label
    invariant.physical available original room
  have finalHeader : Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap := by
    refine ⟨by rw [frame.1]; have := header.bound; omega, ?_⟩
    have different : 0 ≠ headAddress base label := by unfold headAddress; omega
    have cell := IndexBuild.incidence_old_frame state base row previous label headBound
      0 header.bound (Ne.symm different)
    have finalCell : final.heap[0]? = state.heap[0]? := by simpa only [final, heap] using cell
    rw [Array.getElem?_eq_getElem (by have := header.bound; rw [frame.1]; omega),
      Array.getElem?_eq_getElem header.bound] at finalCell
    exact (Option.some.inj finalCell).trans header.value
  refine ⟨final, trace, ?_, frame.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1, finalHeader⟩
  refine ⟨invariant.rowBound, by omega, by have := invariant.processedEq; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show final.heap = IndexBuild.linkedHeap state base label row previous headBound from heap]
    exact nextIndex
  · simpa [final, pointer, row, Nat.add_assoc] using frame.2.1
  · exact frame.2.2.2.1.trans invariant.rowHeld
  · rw [show final.heap.size = state.heap.size + 2 from frame.1]
    exact frame.2.2.1
  · exact frame.2.2.2.2.1.trans invariant.zero
  · exact frame.2.2.2.2.2.1.trans invariant.one
  · rw [show final.heap = IndexBuild.linkedHeap state base label row previous headBound from heap]
    exact endpoint_frame state base row previous limit label headBound invariant.endpoint
  · exact body_position state entry base pointer limit row previous label headBound invariant.zero
  · exact frame.2.2.2.2.2.2.2.2

theorem indexed_body_prefix_header (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (capacity : entry + 32 < 2 ^ width)
    (positiveBase : 0 < base)
    (count consumed processed : Nat) (state : State width 8)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (remaining : consumed + count ≤ (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (room : state.heap.size + 2 * count < 2 ^ width) :
    ∃ final, Execution program state final (16 * count) (state.liveWords + 2 * count) ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex (consumed + count) (processed + count) final ∧
      final.heap.size = state.heap.size + 2 * count ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap := by
  induction count generalizing consumed processed state with
  | zero =>
      exact ⟨state, by simpa using Execution.refl state, by simpa using invariant,
        by simp, rfl, rfl, header⟩
  | succ count ih =>
      obtain ⟨middle, first, next, growth, stack, output, nextHeader⟩ := indexed_body_step_header program clauses
        recordStart recordEnd base entry rowIndex consumed processed state present invariant
        (by omega) positiveBase header capacity (by omega)
      obtain ⟨final, tail, result, totalGrowth, finalStack, finalOutput, finalHeader⟩ :=
        ih (consumed + 1) (processed + 1) middle next nextHeader (by omega) (by omega)
      have middleLive : middle.liveWords = state.liveWords + 2 := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_, by omega, finalStack.trans stack, finalOutput.trans output, finalHeader⟩
      · have trace := first.append tail
        rw [middleLive] at trace
        convert trace using 1 <;> omega
      · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using result

end Controller.Horn.IndexScanWhole
