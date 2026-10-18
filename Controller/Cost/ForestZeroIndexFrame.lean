module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexScanOuter
public import Controller.Cost.ForestZeroBackendFrame

@[expose] public section

/-! Actual incidence indexing preserves a protected query caller prefix while
allocating linked records and updating the source-relative bucket header. -/
namespace Controller.Cost.ForestZeroIndexFrame
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.IndexBuild
open Controller.Cost.ForestZeroBackendFrame

theorem incidence_execution (prefixSize : Nat) (program : Program width 8) (entry base bodyCursor rowAddress previous : Nat)
    (state : State width 8) (label : Fin n)
    (present : At program entry base)
    (bodyBound : bodyCursor < state.heap.size)
    (headBound : headAddress base label < state.heap.size)
    (source : state.heap[bodyCursor]'bodyBound = word width label.val)
    (head : state.heap[headAddress base label]'headBound = word width previous)
    (previousBound : previous < state.heap.size) (rowBound : rowAddress < state.heap.size)
    (sourceHeld : state.reg 0 = word width bodyCursor)
    (rowHeld : state.reg 1 = word width rowAddress)
    (pointerHeld : state.reg 7 = word width state.heap.size)
    (one : state.reg 5 = word width 1)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 11 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ base) :
    Execution program state (finished state entry base bodyCursor rowAddress previous label headBound)
      11 (state.liveWords + 2) ∧
      PrefixFrame prefixSize state.heap
        (finished state entry base bodyCursor rowAddress previous label headBound).heap := by
  refine ⟨Controller.Horn.IndexBuild.incidence_execution program entry base bodyCursor rowAddress
    previous state label present bodyBound headBound source head previousBound rowBound sourceHeld
    rowHeld pointerHeld one position running capacity room, ?_⟩
  refine ⟨prefixBound, ?_, ?_⟩
  · rw [Controller.Horn.IndexBuild.finished_size]
    omega
  · intro index below
    exact Controller.Horn.IndexBuild.incidence_old_frame state base rowAddress previous label
      headBound index (by omega) (by unfold headAddress; omega)

open Controller.Horn
open Controller.Horn.IndexScanLoop Controller.Horn.IndexScanRefinement

theorem body_step (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (remaining : consumed < (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ base) :
    ∃ final, Execution program state final 16 (state.liveWords + 2) ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex (consumed + 1) (processed + 1) final ∧
      final.heap.size = state.heap.size + 2 ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
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
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    refine ⟨prefixBound, by rw [show final.heap.size = state.heap.size + 2 from frame.1]; omega, ?_⟩
    intro index below
    rw [show final.heap = IndexBuild.linkedHeap state base label row previous headBound from heap]
    exact IndexBuild.incidence_old_frame state base row previous label headBound index
      (by omega) (by unfold headAddress; omega)
  refine ⟨final, trace, ?_, frame.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1, retained⟩
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


theorem body_prefix (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (capacity : entry + 32 < 2 ^ width)
    (count consumed processed : Nat) (state : State width 8)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (remaining : consumed + count ≤ (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (room : state.heap.size + 2 * count < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ base) :
    ∃ final, Execution program state final (16 * count) (state.liveWords + 2 * count) ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex (consumed + count) (processed + count) final ∧
      final.heap.size = state.heap.size + 2 * count ∧
      final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
  induction count generalizing consumed processed state with
  | zero =>
      exact ⟨state, by simpa using Execution.refl state, by simpa using invariant,
        by simp, rfl, rfl, ForestZeroBackendFrame.refl state.heap prefixBound⟩
  | succ count ih =>
      obtain ⟨middle, first, next, growth, stack, output, firstPrefix⟩ := body_step prefixSize program clauses
        recordStart recordEnd base entry rowIndex consumed processed state present invariant
        (by omega) capacity (by omega) prefixBound prefixBase
      obtain ⟨final, tail, result, totalGrowth, finalStack, finalOutput, tailPrefix⟩ :=
        ih (consumed + 1) (processed + 1) middle next (by omega) (by omega) firstPrefix.2.1
      have middleLive : middle.liveWords = state.liveWords + 2 := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_, by omega, finalStack.trans stack, finalOutput.trans output, ForestZeroBackendFrame.trans firstPrefix tailPrefix⟩
      · have trace := first.append tail
        rw [middleLive] at trace
        convert trace using 1 <;> omega
      · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using result

open Controller.Horn.IndexScanWhole

theorem row_setup (prefixSize : Nat) (program : Program width 8)
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
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ base) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex 0 processed final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
  let row := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex
  let rule := Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)
  let final := IndexScan.rowFinished state entry base row rule.positives.length headerBound
  have stored := physical.records ⟨rowIndex, rowBound⟩
  have trace := IndexScan.row_setup_execution program entry base recordStart row rule state present
    stored headerBound rowHeld one position running capacity room
  have finalSize : final.heap.size = state.heap.size := by
    change (state.heap.set (base + 2 * n) (word width (row + 3 + rule.positives.length)) headerBound).size = state.heap.size
    simp
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    change PrefixFrame prefixSize state.heap (state.heap.set (base + 2 * n)
      (word width (row + 3 + rule.positives.length)) headerBound)
    exact ForestZeroBackendFrame.store state.heap _ _ headerBound (by omega) prefixBound
  refine ⟨final, trace, ?_, finalSize, rfl, rfl, retained⟩
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

theorem row_terminal (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (complete : consumed = (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ base) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      RowDone clauses recordStart recordEnd base entry rowIndex processed 0 state final ∧ PrefixFrame prefixSize state.heap final.heap := by
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
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    rw [heap]
    exact ForestZeroBackendFrame.refl state.heap prefixBound
  refine ⟨final, by simpa [tested, test_live] using first.append second, ?_, retained⟩
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


theorem row_suffix (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed count : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (complete : consumed + count =
      (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 * count < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBase : prefixSize ≤ base) :
    ∃ final, Execution program state final (16 * count + 6) (state.liveWords + 2 * count) ∧
      RowDone clauses recordStart recordEnd base entry rowIndex (processed + count) count state final ∧ PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨middle, first, next, growth, stack, output, firstPrefix⟩ := body_prefix prefixSize program clauses
    recordStart recordEnd base entry rowIndex present capacity count consumed processed state invariant (by omega) room prefixBound prefixBase
  obtain ⟨final, second, result, secondPrefix⟩ := row_terminal prefixSize program clauses recordStart recordEnd base entry rowIndex
    (consumed + count) (processed + count) middle present next complete capacity (by omega) firstPrefix.2.1 prefixBase
  have middleLive : middle.liveWords = state.liveWords + 2 * count := by
    unfold State.liveWords
    rw [growth, stack, output]
    omega
  refine ⟨final, ?_, ⟨result.physical, result.position, result.rowHeld, result.allocationHeld,
    result.zero.trans (next.zero.trans invariant.zero.symm),
    result.one.trans (next.one.trans invariant.one.symm), ?_,
    result.stack.trans stack, result.output.trans output, result.running⟩,
    ForestZeroBackendFrame.trans firstPrefix secondPrefix⟩
  · have trace := first.append second
    rw [middleLive, Nat.max_self] at trace
    exact trace
  · have := result.growth
    omega



open Controller.Horn.IndexScanOuter

theorem header_frame {prefixSize value address : Nat} {before after : Array (Word width)}
    (frame : PrefixFrame prefixSize before after) (inside : address < prefixSize)
    (stored : Controller.Horn.SourceScan.CursorStored value address before) :
    Controller.Horn.SourceScan.CursorStored value address after := by
  refine ⟨by have := frame.2.1; omega, ?_⟩
  have cell := frame.2.2 address inside
  rw [Array.getElem?_eq_getElem stored.bound,
    Array.getElem?_eq_getElem (show address < after.size by have := frame.2.1; omega)] at cell
  exact (Option.some.inj cell).trans stored.value

theorem outer_row (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : OuterInvariant clauses recordStart recordEnd base entry rowIndex processed state)
    (rowBound : rowIndex < clauses.length) (positiveBase : 0 < base)
    (capacity : entry + 32 < 2 ^ width)
    (room : state.heap.size + 2 *
      (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBase : prefixSize ≤ base)
    (nonzeroPrefix : 0 < prefixSize) :
    let count := (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length
    ∃ final, Execution program state final (16 * count + 18) (state.liveWords + 2 * count) ∧
      OuterInvariant clauses recordStart recordEnd base entry (rowIndex + 1) (processed + count) final ∧
      final.heap.size = state.heap.size + 2 * count ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
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
  obtain ⟨middle, second, body, growth, stack, output, middlePrefix⟩ := row_setup prefixSize program clauses
    recordStart recordEnd base entry rowIndex processed tested present rowBound testedPhysical invariant.processedEq
    headerBound ((test_reg state _ _ _ _ 1 (by decide) (by decide)).trans invariant.rowHeld)
    (by simpa [tested] using (test_reg state _ _ _ _ 7 (by decide) (by decide)).trans invariant.allocationHeld)
    ((test_reg state _ _ _ _ 2 (by decide) (by decide)).trans invariant.zero)
    ((test_reg state _ _ _ _ 5 (by decide) (by decide)).trans invariant.one)
    testedPosition (by simpa [tested] using invariant.running) capacity
    (by simpa [tested] using (show state.heap.size < 2 ^ width by omega))
    (by simpa [tested] using prefixBound) prefixBase
  obtain ⟨final, third, result, finalPrefix⟩ := row_suffix prefixSize program clauses
    recordStart recordEnd base entry rowIndex 0 processed count middle present body (by simp [count])
    capacity (by rw [growth]; simpa [tested] using room) middlePrefix.2.1 prefixBase
  have middleHeader := header_frame middlePrefix nonzeroPrefix testedHeader
  have finalHeader := header_frame finalPrefix nonzeroPrefix middleHeader
  have firstPrefix : PrefixFrame prefixSize state.heap tested.heap := by
    simpa [tested] using ForestZeroBackendFrame.refl state.heap prefixBound
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [growth, stack, output]
    simp [tested]
  refine ⟨final, ?_, ?_, ?_, result.stack.trans (stack.trans (test_stack state _ _ _ _)),
    result.output.trans (output.trans (test_output state _ _ _ _)),
    ForestZeroBackendFrame.trans firstPrefix (ForestZeroBackendFrame.trans middlePrefix finalPrefix)⟩
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

theorem outer_suffix (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (positiveBase : 0 < base) (capacity : entry + 32 < 2 ^ width)
    (rows rowIndex processed : Nat) (state : State width 8)
    (invariant : OuterInvariant clauses recordStart recordEnd base entry rowIndex processed state)
    (complete : rowIndex + rows = clauses.length)
    (room : state.heap.size + 2 * ((IndexScan.occurrences clauses recordStart).length - processed) < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBase : prefixSize ≤ base)
    (nonzeroPrefix : 0 < prefixSize) :
    ∃ final, Execution program state final
      (16 * ((IndexScan.occurrences clauses recordStart).length - processed) + 18 * rows + 4)
      (state.liveWords + 2 * ((IndexScan.occurrences clauses recordStart).length - processed)) ∧
      ScanDone clauses recordStart recordEnd base entry
        ((IndexScan.occurrences clauses recordStart).length - processed) state final ∧ PrefixFrame prefixSize state.heap final.heap := by
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
      refine ⟨final, by simpa [allProcessed] using trace, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simpa [final] using ForestZeroBackendFrame.refl state.heap prefixBound
  | succ rows ih =>
      have rowBound : rowIndex < clauses.length := by omega
      let count := (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length
      have nextPrefix := prefix_occurrences_succ clauses recordStart rowIndex rowBound
      have occurrenceBound := prefix_length_le clauses recordStart (rowIndex + 1)
      have incidenceRoom : state.heap.size + 2 * count < 2 ^ width := by
        have := invariant.processedEq
        dsimp [count]
        omega
      obtain ⟨middle, first, next, growth, stack, output, firstPrefix⟩ := outer_row prefixSize program clauses
        recordStart recordEnd base entry rowIndex processed state present invariant rowBound positiveBase capacity incidenceRoom prefixBound prefixBase nonzeroPrefix
      have physicalBound : processed + count ≤ (IndexScan.occurrences clauses recordStart).length := next.physical.prefixBound
      obtain ⟨final, tail, result, tailPrefix⟩ := ih (rowIndex + 1) (processed + count) middle next (by omega) (by omega) firstPrefix.2.1
      have middleLive : middle.liveWords = state.liveWords + 2 * count := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_, ForestZeroBackendFrame.trans firstPrefix tailPrefix⟩
      · have trace := first.append tail
        rw [middleLive] at trace
        convert trace using 1 <;> omega
      · refine ⟨result.physical, result.header, result.position, result.allocationHeld,
          result.zero.trans (next.zero.trans invariant.zero.symm),
          result.one.trans (next.one.trans invariant.one.symm), ?_,
          result.stack.trans stack, result.output.trans output, result.running⟩
        have := result.growth
        omega


theorem all_rows (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base 0 state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (positiveBase : 0 < base) (position : state.pc = word width entry)
    (running : state.halted = false) (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (capacity : entry + 32 < 2 ^ width)
    (room : state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBase : prefixSize ≤ base)
    (nonzeroPrefix : 0 < prefixSize) :
    ∃ final, Execution program state final
      (16 * (IndexScan.occurrences clauses recordStart).length + 18 * clauses.length + 6)
      (state.liveWords + 2 * (IndexScan.occurrences clauses recordStart).length) ∧
      ScanDone clauses recordStart recordEnd base entry (IndexScan.occurrences clauses recordStart).length state final ∧ PrefixFrame prefixSize state.heap final.heap := by
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
  obtain ⟨final, tail, result, tailPrefix⟩ := outer_suffix prefixSize program clauses recordStart recordEnd base entry present
    positiveBase capacity clauses.length 0 0 middle middleInvariant (by omega) (by simpa [middle, frame.1] using room)
    (by simpa [middle, frame.1] using prefixBound) prefixBase nonzeroPrefix
  have firstPrefix : PrefixFrame prefixSize state.heap middle.heap := by
    simpa only [middle, frame.1] using ForestZeroBackendFrame.refl state.heap prefixBound
  refine ⟨final, ?_, ⟨result.physical, result.header, result.position, result.allocationHeld,
    result.zero.trans (frame.2.2.2.2.2 2 (by decide) (by decide)),
    result.one.trans (frame.2.2.2.2.2 5 (by decide) (by decide)), ?_,
    result.stack.trans frame.2.1, result.output.trans frame.2.2.1, result.running⟩,
    ForestZeroBackendFrame.trans firstPrefix tailPrefix⟩
  · have trace := first.append tail
    rw [middleLive] at trace
    convert trace using 1 <;> simp only [Nat.sub_zero] <;> omega
  · simpa only [Nat.sub_zero, middle, frame.1] using result.growth


end Controller.Cost.ForestZeroIndexFrame
