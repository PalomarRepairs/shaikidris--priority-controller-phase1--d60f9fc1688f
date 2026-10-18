module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroHeaderCaller
public import Controller.Cost.ForestZeroAnswerReclaim

@[expose] public section

/-! Index writes change even bucket-head cells and the separate cursor header.
These frames protect odd FIFO mark cells on the same concrete index operations,
allowing empty-FIFO initialization to survive incidence construction. -/
set_option autoImplicit false
namespace Controller.Cost.ForestZeroIndexMarks
open Controller.Cost Controller.Horn Controller.Horn.WorklistStorage
variable {width n : Nat}

def MarkFrame (base : Nat) (before after : Array (Word width)) : Prop :=
  before.size ≤ after.size ∧ ∀ label : Fin n,
    after[offAddress base label]? = before[offAddress base label]?

theorem refl (base : Nat) (heap : Array (Word width)) : MarkFrame (n := n) base heap heap :=
  ⟨Nat.le_refl _, fun _ => rfl⟩

theorem trans {base : Nat} {before middle after : Array (Word width)}
    (first : MarkFrame (n := n) base before middle) (second : MarkFrame (n := n) base middle after) :
    MarkFrame (n := n) base before after :=
  ⟨Nat.le_trans first.1 second.1, fun label => (second.2 label).trans (first.2 label)⟩

theorem head_ne_off (base : Nat) (head mark : Fin n) :
    headAddress base head ≠ offAddress base mark := by
  unfold headAddress offAddress
  omega

theorem header_ne_off (base : Nat) (mark : Fin n) :
    base + 2 * n ≠ offAddress base mark := by
  have bound := mark.isLt
  unfold offAddress
  omega

theorem linked_marks (state : State width 8) (base row previous : Nat) (label : Fin n)
    (headBound : headAddress base label < state.heap.size)
    (markFits : base + 2 * n ≤ state.heap.size) :
    MarkFrame (n := n) base state.heap (IndexBuild.linkedHeap state base label row previous headBound) := by
  refine ⟨by simp only [IndexBuild.linkedHeap, Array.size_set, Array.size_push]; omega, ?_⟩
  intro mark
  exact IndexBuild.incidence_old_frame state base row previous label headBound
    (offAddress base mark) (by have := mark.isLt; unfold offAddress; omega)
    (head_ne_off base label mark)

theorem cursor_marks (state : State width 8) (base value : Nat)
    (headerBound : base + 2 * n < state.heap.size) :
    MarkFrame (n := n) base state.heap
      (state.heap.set (base + 2 * n) (word width value) headerBound) := by
  refine ⟨by simp, ?_⟩
  intro mark
  exact Array.getElem?_set_ne headerBound (header_ne_off base mark)

theorem empty_fifo_retained {base : Nat} {before after : Array (Word width)}
    (frame : MarkFrame (n := n) base before after)
    (stored : WorklistMark.Stored ([] : List (Fin n)) base before) :
    WorklistMark.Stored ([] : List (Fin n)) base after := by
  have growth := frame.1
  refine ⟨by simp, by have := stored.fits; omega, ?_, ?_⟩
  · intro label
    have oldBound : offAddress base label < before.size := by
      have := stored.fits; have := label.isLt; unfold offAddress; omega
    have newBound : offAddress base label < after.size := by omega
    have equal := frame.2 label
    rw [Array.getElem?_eq_getElem newBound, Array.getElem?_eq_getElem oldBound] at equal
    exact (Option.some.inj equal).trans (stored.flags label)
  · refine ⟨?_, ?_⟩
    · have := stored.queue.fits; simp only [List.length_nil] at *; omega
    · intro index; exact Fin.elim0 index

/-- The actual eleven-instruction incidence execution preserves all FIFO marks. -/
theorem incidence_execution (program : Program width 8) (entry base bodyCursor rowAddress previous : Nat)
    (state : State width 8) (label : Fin n)
    (present : IndexBuild.At program entry base)
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
    (markFits : base + 2 * n ≤ state.heap.size) :
    Execution program state (IndexBuild.finished state entry base bodyCursor rowAddress previous label headBound)
      11 (state.liveWords + 2) ∧
    MarkFrame (n := n) base state.heap
      (IndexBuild.finished state entry base bodyCursor rowAddress previous label headBound).heap := by
  refine ⟨IndexBuild.incidence_execution program entry base bodyCursor rowAddress previous state label present
    bodyBound headBound source head previousBound rowBound sourceHeld rowHeld pointerHeld one position running capacity room, ?_⟩
  exact linked_marks state base rowAddress previous label headBound markFits

/-- The actual row-cursor store is separate from every odd mark address. -/
theorem row_setup_execution (program : Program width 8) (entry base recordStart offset : Nat)
    (rule : Worklist.Rule (Fin n)) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (stored : RuleCopy.Stored rule offset state.heap)
    (headerBound : base + 2 * n < state.heap.size)
    (rowHeld : state.reg 1 = word width offset) (one : state.reg 5 = word width 1)
    (position : state.pc = word width (entry + 6)) (running : state.halted = false)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    Execution program state (IndexScan.rowFinished state entry base offset rule.positives.length headerBound)
      8 state.liveWords ∧
    MarkFrame (n := n) base state.heap
      (IndexScan.rowFinished state entry base offset rule.positives.length headerBound).heap := by
  exact ⟨IndexScan.row_setup_execution program entry base recordStart offset rule state present stored
    headerBound rowHeld one position running capacity room,
    cursor_marks state base (offset + 3 + rule.positives.length) headerBound⟩


open Controller.Cost.ForestZeroBackendFrame
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
      final.heap.size = state.heap.size + 2 ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap ∧ MarkFrame (n := n) base state.heap final.heap := by
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
  have markFits : base + 2 * n ≤ state.heap.size := by
    have separation := invariant.physical.separation
    have ending := invariant.physical.endpoint
    have original := invariant.physical.originalEnd
    have above := NormalizeLoop.recordOffset_above clauses recordStart clauses.length
    omega
  have marked : MarkFrame (n := n) base state.heap final.heap := by
    rw [show final.heap = IndexBuild.linkedHeap state base label row previous headBound from heap]
    exact linked_marks state base row previous label headBound markFits
  refine ⟨final, trace, ?_, frame.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1, retained, marked⟩
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
      final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap ∧ MarkFrame (n := n) base state.heap final.heap := by
  induction count generalizing consumed processed state with
  | zero =>
      exact ⟨state, by simpa using Execution.refl state, by simpa using invariant,
        by simp, rfl, rfl, ForestZeroBackendFrame.refl state.heap prefixBound, refl base state.heap⟩
  | succ count ih =>
      obtain ⟨middle, first, next, growth, stack, output, firstPrefix, firstMark⟩ := body_step prefixSize program clauses
        recordStart recordEnd base entry rowIndex consumed processed state present invariant
        (by omega) capacity (by omega) prefixBound prefixBase
      obtain ⟨final, tail, result, totalGrowth, finalStack, finalOutput, tailPrefix, tailMark⟩ :=
        ih (consumed + 1) (processed + 1) middle next (by omega) (by omega) firstPrefix.2.1
      have middleLive : middle.liveWords = state.liveWords + 2 := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_, by omega, finalStack.trans stack, finalOutput.trans output, ForestZeroBackendFrame.trans firstPrefix tailPrefix, trans firstMark tailMark⟩
      · have trace := first.append tail
        rw [middleLive] at trace
        convert trace using 1 <;> omega
      · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using result


open Controller.Horn.IndexScanWhole Controller.Horn.IndexScanOuter
open Controller.Cost.ForestZeroIndexFrame (RowDone header_frame)

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
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap ∧ MarkFrame (n := n) base state.heap final.heap := by
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
  have marked : MarkFrame (n := n) base state.heap final.heap :=
    cursor_marks state base (row + 3 + rule.positives.length) headerBound
  refine ⟨final, trace, ?_, finalSize, rfl, rfl, retained, marked⟩
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
      ForestZeroIndexFrame.RowDone clauses recordStart recordEnd base entry rowIndex processed 0 state final ∧ PrefixFrame prefixSize state.heap final.heap ∧ MarkFrame (n := n) base state.heap final.heap := by
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
  have marked : MarkFrame (n := n) base state.heap final.heap := by
    rw [heap]
    exact refl base state.heap
  refine ⟨final, by simpa [tested, test_live] using first.append second, ?_, retained, marked⟩
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
      ForestZeroIndexFrame.RowDone clauses recordStart recordEnd base entry rowIndex (processed + count) count state final ∧ PrefixFrame prefixSize state.heap final.heap ∧ MarkFrame (n := n) base state.heap final.heap := by
  obtain ⟨middle, first, next, growth, stack, output, firstPrefix, firstMark⟩ := body_prefix prefixSize program clauses
    recordStart recordEnd base entry rowIndex present capacity count consumed processed state invariant (by omega) room prefixBound prefixBase
  obtain ⟨final, second, result, secondPrefix, secondMark⟩ := row_terminal prefixSize program clauses recordStart recordEnd base entry rowIndex
    (consumed + count) (processed + count) middle present next complete capacity (by omega) firstPrefix.2.1 prefixBase
  have middleLive : middle.liveWords = state.liveWords + 2 * count := by
    unfold State.liveWords
    rw [growth, stack, output]
    omega
  refine ⟨final, ?_, ⟨result.physical, result.position, result.rowHeld, result.allocationHeld,
    result.zero.trans (next.zero.trans invariant.zero.symm),
    result.one.trans (next.one.trans invariant.one.symm), ?_,
    result.stack.trans stack, result.output.trans output, result.running⟩,
    ForestZeroBackendFrame.trans firstPrefix secondPrefix, trans firstMark secondMark⟩
  · have trace := first.append second
    rw [middleLive, Nat.max_self] at trace
    exact trace
  · have := result.growth
    omega



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
      final.heap.size = state.heap.size + 2 * count ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap ∧ MarkFrame (n := n) base state.heap final.heap := by
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
  obtain ⟨middle, second, body, growth, stack, output, middlePrefix, middleMark⟩ := row_setup prefixSize program clauses
    recordStart recordEnd base entry rowIndex processed tested present rowBound testedPhysical invariant.processedEq
    headerBound ((test_reg state _ _ _ _ 1 (by decide) (by decide)).trans invariant.rowHeld)
    (by simpa [tested] using (test_reg state _ _ _ _ 7 (by decide) (by decide)).trans invariant.allocationHeld)
    ((test_reg state _ _ _ _ 2 (by decide) (by decide)).trans invariant.zero)
    ((test_reg state _ _ _ _ 5 (by decide) (by decide)).trans invariant.one)
    testedPosition (by simpa [tested] using invariant.running) capacity
    (by simpa [tested] using (show state.heap.size < 2 ^ width by omega))
    (by simpa [tested] using prefixBound) prefixBase
  obtain ⟨final, third, result, finalPrefix, finalMark⟩ := row_suffix prefixSize program clauses
    recordStart recordEnd base entry rowIndex 0 processed count middle present body (by simp [count])
    capacity (by rw [growth]; simpa [tested] using room) middlePrefix.2.1 prefixBase
  have middleHeader := header_frame middlePrefix nonzeroPrefix testedHeader
  have finalHeader := header_frame finalPrefix nonzeroPrefix middleHeader
  have firstPrefix : PrefixFrame prefixSize state.heap tested.heap := by
    simpa [tested] using ForestZeroBackendFrame.refl state.heap prefixBound
  have firstMark : MarkFrame (n := n) base state.heap tested.heap := by
    simpa [tested] using refl (n := n) base state.heap
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [growth, stack, output]
    simp [tested]
  refine ⟨final, ?_, ?_, ?_, result.stack.trans (stack.trans (test_stack state _ _ _ _)),
    result.output.trans (output.trans (test_output state _ _ _ _)),
    ForestZeroBackendFrame.trans firstPrefix (ForestZeroBackendFrame.trans middlePrefix finalPrefix), trans firstMark (trans middleMark finalMark)⟩
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
        ((IndexScan.occurrences clauses recordStart).length - processed) state final ∧ PrefixFrame prefixSize state.heap final.heap ∧ MarkFrame (n := n) base state.heap final.heap := by
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
      · refine ⟨?_, ?_⟩
        · simpa [final] using ForestZeroBackendFrame.refl state.heap prefixBound
        · simpa [final] using refl (n := n) base state.heap
  | succ rows ih =>
      have rowBound : rowIndex < clauses.length := by omega
      let count := (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length
      have nextPrefix := prefix_occurrences_succ clauses recordStart rowIndex rowBound
      have occurrenceBound := prefix_length_le clauses recordStart (rowIndex + 1)
      have incidenceRoom : state.heap.size + 2 * count < 2 ^ width := by
        have := invariant.processedEq
        dsimp [count]
        omega
      obtain ⟨middle, first, next, growth, stack, output, firstPrefix, firstMark⟩ := outer_row prefixSize program clauses
        recordStart recordEnd base entry rowIndex processed state present invariant rowBound positiveBase capacity incidenceRoom prefixBound prefixBase nonzeroPrefix
      have physicalBound : processed + count ≤ (IndexScan.occurrences clauses recordStart).length := next.physical.prefixBound
      obtain ⟨final, tail, result, tailPrefix, tailMark⟩ := ih (rowIndex + 1) (processed + count) middle next (by omega) (by omega) firstPrefix.2.1
      have middleLive : middle.liveWords = state.liveWords + 2 * count := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_, ForestZeroBackendFrame.trans firstPrefix tailPrefix, trans firstMark tailMark⟩
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
      ScanDone clauses recordStart recordEnd base entry (IndexScan.occurrences clauses recordStart).length state final ∧ PrefixFrame prefixSize state.heap final.heap ∧ MarkFrame (n := n) base state.heap final.heap := by
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
  obtain ⟨final, tail, result, tailPrefix, tailMark⟩ := outer_suffix prefixSize program clauses recordStart recordEnd base entry present
    positiveBase capacity clauses.length 0 0 middle middleInvariant (by omega) (by simpa [middle, frame.1] using room)
    (by simpa [middle, frame.1] using prefixBound) prefixBase nonzeroPrefix
  have firstPrefix : PrefixFrame prefixSize state.heap middle.heap := by
    simpa only [middle, frame.1] using ForestZeroBackendFrame.refl state.heap prefixBound
  have firstMark : MarkFrame (n := n) base state.heap middle.heap := by
    simpa only [middle, frame.1] using refl (n := n) base state.heap
  refine ⟨final, ?_, ⟨result.physical, result.header, result.position, result.allocationHeld,
    result.zero.trans (frame.2.2.2.2.2 2 (by decide) (by decide)),
    result.one.trans (frame.2.2.2.2.2 5 (by decide) (by decide)), ?_,
    result.stack.trans frame.2.1, result.output.trans frame.2.2.1, result.running⟩,
    ForestZeroBackendFrame.trans firstPrefix tailPrefix, trans firstMark tailMark⟩
  · have trace := first.append tail
    rw [middleLive] at trace
    convert trace using 1 <;> simp only [Nat.sub_zero] <;> omega
  · simpa only [Nat.sub_zero, middle, frame.1] using result.growth



/-- The caller-header substitution is at address zero, outside every mark. -/
theorem zero_store_marks (heap : Array (Word width)) (base : Nat) (value : Word width)
    (valid : 0 < heap.size) (positiveBase : 0 < base) :
    MarkFrame (n := n) base heap (heap.set 0 value valid) := by
  refine ⟨by simp, ?_⟩
  intro mark
  exact Array.getElem?_set_ne valid (by unfold offAddress; omega)

open Controller.Cost.ForestZeroHeaderBridge

theorem wrapped_index_execution (prefixSize : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (entry recordHeader recordStart recordEnd base : Nat) (state : State width 8)
    (savePresent : SaveAt program entry recordHeader)
    (indexPresent : Controller.Horn.IndexScan.At (n := n) program (entry + 7) base recordStart)
    (restorePresent : RestoreAt program (entry + 39))
    (physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base 0 state.heap)
    (queryHeader : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (positiveBase : 0 < base) (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBase : prefixSize ≤ base) (nonzeroPrefix : 0 < prefixSize)
    (fifo : WorklistMark.Stored ([] : List (Fin n)) base state.heap)
    (capacity : entry + 42 < 2 ^ width)
    (room : state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length < 2 ^ width) :
    ∃ final, Execution program state final
      (16 * (IndexScan.occurrences clauses recordStart).length + 18 * clauses.length + 16)
      (state.liveWords + 2 * (IndexScan.occurrences clauses recordStart).length + 1) ∧
      IndexScan.PhysicalIndex clauses recordStart recordEnd base
        (IndexScan.occurrences clauses recordStart).length final.heap ∧
      PrefixFrame prefixSize state.heap final.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧
      final.heap.size = state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length ∧
      final.reg 7 = word width final.heap.size ∧ final.reg 2 = word width 0 ∧
      final.reg 5 = word width 1 ∧ final.pc = word width (entry + 42) ∧ final.halted = false ∧ MarkFrame (n := n) base state.heap final.heap ∧
      WorklistMark.Stored ([] : List (Fin n)) base final.heap := by
  have bound : 0 < state.heap.size := by omega
  obtain ⟨saved, first, savedHeap, savedStack, savedOutput, savedPosition, savedRunning, savedRegs⟩ :=
    save_execution program entry recordHeader recordEnd state savePresent position running bound queryHeader
      (by omega) (by omega)
  have savedSize : saved.heap.size = state.heap.size := by rw [savedHeap]; simp
  have savedPhysical : IndexScan.PhysicalIndex clauses recordStart recordEnd base 0 saved.heap := by
    rw [savedHeap]
    exact source_header_index clauses recordStart recordEnd base 0 (word width recordEnd) state.heap physical positiveBase bound
  have savedHeader : Controller.Horn.SourceScan.CursorStored recordEnd 0 saved.heap := by
    refine ⟨by omega, ?_⟩
    have cell : saved.heap[0]? = some (word width recordEnd) := by simp [savedHeap]
    rw [Array.getElem?_eq_getElem (show 0 < saved.heap.size by omega)] at cell
    exact Option.some.inj cell
  obtain ⟨indexed, second, result, indexedPrefix, indexedMark⟩ := all_rows prefixSize program clauses
    recordStart recordEnd base (entry + 7) saved indexPresent savedPhysical savedHeader positiveBase savedPosition savedRunning
    ((savedRegs 2 (by decide) (by decide)).trans zero)
    ((savedRegs 5 (by decide) (by decide)).trans one)
    (by omega) (by rw [savedSize]; exact room) (by omega) prefixBase nonzeroPrefix
  have indexedBound : 0 < indexed.heap.size := by have := result.growth; omega
  have finalTrace := restore_execution program (entry + 39) indexed (state.heap[0]'bound) state.stack
    restorePresent (by simpa [Nat.add_assoc] using result.position) result.running
    (result.stack.trans savedStack) indexedBound (by omega)
  let final := restored indexed (state.heap[0]'bound) state.stack indexedBound
  have originalPrefix : PrefixFrame prefixSize state.heap final.heap := by
    apply restore_prefix prefixSize state.heap (word width recordEnd) (state.heap[0]'bound) bound
      indexed state.stack indexedBound rfl
    simpa only [savedHeap] using indexedPrefix
  have savedLive : saved.liveWords = state.liveWords + 1 := by
    unfold State.liveWords
    rw [savedSize, savedStack, savedOutput]
    simp
    omega
  have indexedLive : indexed.liveWords = saved.liveWords +
      2 * (IndexScan.occurrences clauses recordStart).length := by
    unfold State.liveWords
    rw [result.growth, result.stack, result.output]
    omega
  have finalSize : final.heap.size = indexed.heap.size := by simp [final, restored]
  have finalRegister (register : Fin 8) (not3 : register ≠ 3) (not4 : register ≠ 4) :
      final.reg register = indexed.reg register := by
    simp [final, restored, addressed, popped, State.advance, State.put, not3, not4]
  have savedMark : MarkFrame (n := n) base state.heap saved.heap := by
    rw [savedHeap]
    exact zero_store_marks state.heap base (word width recordEnd) bound positiveBase
  have finalMark : MarkFrame (n := n) base indexed.heap final.heap := by
    change MarkFrame (n := n) base indexed.heap
      (indexed.heap.set 0 (state.heap[0]'bound) indexedBound)
    exact zero_store_marks indexed.heap base (state.heap[0]'bound) indexedBound positiveBase
  have wholeMark := trans savedMark (trans indexedMark finalMark)
  refine ⟨final, ?_, ?_, originalPrefix, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    wholeMark, empty_fifo_retained wholeMark fifo⟩
  · have trace := (first.append second).append finalTrace
    rw [savedLive, indexedLive, savedLive] at trace
    convert trace using 1 <;> omega
  · exact source_header_index clauses recordStart recordEnd base
      (IndexScan.occurrences clauses recordStart).length (state.heap[0]'bound) indexed.heap
      result.physical positiveBase indexedBound
  · exact result.output.trans savedOutput
  · rw [finalSize, result.growth, savedSize]
  · rw [finalRegister 7 (by decide) (by decide), finalSize]
    exact result.allocationHeld
  · exact (finalRegister 2 (by decide) (by decide)).trans
      (result.zero.trans ((savedRegs 2 (by decide) (by decide)).trans zero))
  · exact (finalRegister 5 (by decide) (by decide)).trans
      (result.one.trans ((savedRegs 5 (by decide) (by decide)).trans one))
  · have pc39 : indexed.pc.val = entry + 39 := by
      rw [result.position]
      change ((entry + 7 + 32) % 2 ^ width) = entry + 39
      rw [Nat.mod_eq_of_lt (by omega)]
    simp [final, restored, addressed, popped, State.advance, State.put, word, pc39,
      Nat.add_assoc, Nat.mod_eq_of_lt (show entry + 40 < 2 ^ width by omega),
      Nat.mod_eq_of_lt (show entry + 41 < 2 ^ width by omega)]
  · simpa [final, restored, addressed, popped, State.advance, State.put] using result.running


open Controller.Horn.WorklistMark Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistOutcome Controller.Horn.WorklistPropagation
open Controller.Horn.WorklistPropagationStep Controller.Horn.WorklistFIFORun Controller.Horn.WorklistSeed

/-- Actual incidence indexing preserves the initialized FIFO and source header,
then runs captured seeded decision, answer emission and physical reclamation. -/
theorem indexed_captured_execution (keep : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      0 state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + 48 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size + 2 * (IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width) (setupCapacity : entry + 58 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (protectedPrefix : Nat) (protectedBound : protectedPrefix ≤ state.heap.size)
    (protectedBase : protectedPrefix ≤ base) (protectedPositive : 0 < protectedPrefix)
    (keepProtected : keep ≤ protectedPrefix) (headerProtected : recordHeader < protectedPrefix)
    (positiveBase : 0 < base)
    (indexSaveAt : SaveAt program entry recordHeader)
    (indexAt : IndexScan.At (n := n) program (entry + 7) base recordStart)
    (indexRestoreAt : RestoreAt program (entry + 39))
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch fifoDone bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry : Nat) (successAt : ForestZeroAnswer.At program fifoDone 1 cleanupEntry)
    (conflictAt : ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 4 < 2 ^ width)
    (conflictCapacity : conflict + 4 < 2 ^ width) (returnCapacity : cleanupEntry < 2 ^ width)
    (returnPc : Nat) (rest : List (Word width))
    (savedKeep : state.stack = word width keep :: rest)
    (captureAt : ∀ phase : Fin 6, program[entry + 42 + phase.val]? =
      (ForestZeroReclaim.captureCode width)[phase.val]?)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) :
    ∃ answer : Bool, ∃ finalQueue final ticks,
      ticks ≤ 54 * formula.clauses.toList.length +
        48 * (IndexScan.occurrences formula.clauses.toList recordStart).length + 26 * n + 54 +
        4 * (state.heap.size + 2 * (IndexScan.occurrences formula.clauses.toList recordStart).length - keep) ∧
      Execution program state final ticks
        (state.liveWords + 2 * (IndexScan.occurrences formula.clauses.toList recordStart).length + 1) ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = word width (if answer then 1 else 0) :: state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → Controller.CNF.Satisfies (offAssignment finalQueue) formula) := by
  obtain ⟨indexed, indexRun, indexPhysical, indexFrame, indexStack, indexOutput,
    indexSize, indexCursor, indexZero, indexOne, indexPC, indexRunning, indexMarks, indexFIFO⟩ :=
    wrapped_index_execution protectedPrefix program formula.clauses.toList entry recordHeader
      recordStart recordEnd base state indexSaveAt indexAt indexRestoreAt physical header
      position running zero one positiveBase protectedBound protectedBase protectedPositive
      fifo (by omega) room
  have indexHeader := ForestZeroIndexFrame.header_frame indexFrame headerProtected header
  have indexRoom : indexed.heap.size < 2 ^ width := by rw [indexSize]; exact room
  have indexKeep : keep ≤ indexed.heap.size := by rw [indexSize]; omega
  obtain ⟨answer, queue, final, ticks, bound, run, finalSize, finalStack, finalOutput,
    finalPC, finalRunning, frame, answerIff, model⟩ :=
    ForestZeroAnswerReclaim.captured_initialized_execution keep formula dual
      recordHeader recordStart recordEnd base (entry + 42) scan seedDone conflict indexed program
      indexPhysical indexHeader indexFIFO separated
      (by intro phase; rw [show entry + 42 + 6 = entry + 48 by omega]; exact setupAt phase) scanAt indexPC indexRunning indexZero indexOne
      indexRoom (by omega) scanCapacity indexKeep prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity
      advanceCapacity bucketCapacity readyCapacity cleanupEntry successAt conflictAt
      successCapacity conflictCapacity returnCapacity returnPc rest
      (indexStack.trans savedKeep) indexCursor captureAt cleanupSetup cleanupLoop cleanupCapacity
  have indexLive : indexed.liveWords = state.liveWords +
      2 * (IndexScan.occurrences formula.clauses.toList recordStart).length := by
    unfold State.liveWords
    rw [indexSize, indexStack, indexOutput]
    omega
  have retained : PrefixFrame keep state.heap indexed.heap :=
    ⟨prefixBound, indexKeep, fun address below => indexFrame.2.2 address (by omega)⟩
  refine ⟨answer, queue, final,
    (16 * (IndexScan.occurrences formula.clauses.toList recordStart).length +
      18 * formula.clauses.toList.length + 16) + ticks, ?_, ?_, finalSize, finalStack,
    ?_, finalPC, finalRunning, ForestZeroBackendFrame.trans retained frame, answerIff, model⟩
  · rw [indexSize] at bound
    omega
  · simpa only [indexLive, Nat.add_assoc, Nat.max_self] using indexRun.append run
  · simpa only [indexOutput] using finalOutput

/-- Clean scratch left by the physical normalizer is the empty FIFO. Its
zero flag cells are reused directly; no additional channel scan is required. -/
theorem normalized_empty_fifo (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses) (recordStart index : Nat)
    (marks : Controller.Horn.Worklist.IndexedNormalize.Marks n) (state : State width 8)
    (normalized : Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart index marks state) :
    WorklistMark.Stored ([] : List (Fin n)) layout.base state.heap := by
  have scratchFits := normalized.scratch.touched.buffer.fits
  refine ⟨List.nodup_nil, by omega, ?_, ?_⟩
  · intro label
    have zeroCell := (WorklistStorage.scratch_zero normalized label).2
    rw [Array.getElem?_eq_getElem (show offAddress layout.base label < state.heap.size by
      have := label.isLt; unfold offAddress; omega)] at zeroCell
    simpa only [List.not_mem_nil, ite_false] using Option.some.inj zeroCell
  · refine ⟨by simp only [List.length_nil, Nat.add_zero, WorklistMark.queueStart]; omega, ?_⟩
    intro position
    exact Fin.elim0 position

/-- All index/seed input records follow from the completed normalizer state. -/
theorem normalized_inputs (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses) (recordStart : Nat)
    (marks : Controller.Horn.Worklist.IndexedNormalize.Marks n) (state : State width 8)
    (normalized : Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart clauses.length marks state) :
    IndexScan.PhysicalIndex clauses recordStart state.heap.size layout.base 0 state.heap ∧
      Controller.Horn.SourceScan.CursorStored state.heap.size layout.recordHeader state.heap ∧
      WorklistMark.Stored ([] : List (Fin n)) layout.base state.heap :=
  ⟨IndexScan.initial clauses layout recordStart marks state normalized,
    normalized.recordCursor, normalized_empty_fifo clauses layout recordStart clauses.length marks state normalized⟩

theorem indexed_captured_model_execution (keep : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      0 state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + 48 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size + 2 * (IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width) (setupCapacity : entry + 58 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (protectedPrefix : Nat) (protectedBound : protectedPrefix ≤ state.heap.size)
    (protectedBase : protectedPrefix ≤ base) (protectedPositive : 0 < protectedPrefix)
    (keepProtected : keep ≤ protectedPrefix) (headerProtected : recordHeader < protectedPrefix)
    (positiveBase : 0 < base)
    (indexSaveAt : SaveAt program entry recordHeader)
    (indexAt : IndexScan.At (n := n) program (entry + 7) base recordStart)
    (indexRestoreAt : RestoreAt program (entry + 39))
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch fifoDone bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry returnPc : Nat) (rest : List (Word width))
    (savedKeep : state.stack = word width keep :: rest)
    (captureAt : ∀ phase : Fin 6, program[entry + 42 + phase.val]? =
      (ForestZeroReclaim.captureCode width)[phase.val]?)
    (tag0 : program[fifoDone]? = some (.constant 0 (word width 1)))
    (tag1 : program[fifoDone + 1]? = some (.emit 0))
    (emitAt : Controller.Horn.WorklistAccept.EmitCodeAt program (fifoDone + 2) base
      (Controller.Horn.WorklistAccept.outputLabels n))
    (successSetup : ∀ phase : Fin 3, program[fifoDone + 2 + 4 * n + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (successLoop : ForestZeroReclaim.At program (fifoDone + 2 + 4 * n + 3) returnPc)
    (successCapacity : fifoDone + 2 + 4 * n + 7 < 2 ^ width)
    (conflictAt : ForestZeroAnswer.At program conflict 0 cleanupEntry)
    (conflictCapacity : conflict + 4 < 2 ^ width) (cleanupFits : cleanupEntry < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (oneFits : 1 < 2 ^ width) :
    ∃ answer : Bool, ∃ queue final ticks peak,
      ticks ≤ 54 * formula.clauses.toList.length +
        48 * (IndexScan.occurrences formula.clauses.toList recordStart).length +
        30 * n + 54 + 4 * (state.heap.size + 2 * (IndexScan.occurrences formula.clauses.toList recordStart).length - keep) ∧
      Execution program state final ticks peak ∧ peak ≤ state.liveWords + 2 * (IndexScan.occurrences formula.clauses.toList recordStart).length + n + 1 ∧
      final.heap.size = keep ∧ final.stack = rest ∧
      final.output = (if answer then
        (List.finRange n).map (fun label => word width (if offAssignment queue label then 1 else 0)) ++
          [word width 1] else [word width 0]) ++ state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∧
      (answer = true → offAssignment queue = Controller.Horn.greatestCandidate formula) := by
  obtain ⟨indexed, indexRun, indexPhysical, indexFrame, indexStack, indexOutput,
    indexSize, indexCursor, indexZero, indexOne, indexPC, indexRunning, indexMarks, indexFIFO⟩ :=
    wrapped_index_execution protectedPrefix program formula.clauses.toList entry recordHeader
      recordStart recordEnd base state indexSaveAt indexAt indexRestoreAt physical header
      position running zero one positiveBase protectedBound protectedBase protectedPositive
      fifo (by omega) room
  have indexHeader := ForestZeroIndexFrame.header_frame indexFrame headerProtected header
  have indexRoom : indexed.heap.size < 2 ^ width := by rw [indexSize]; exact room
  have indexKeep : keep ≤ indexed.heap.size := by rw [indexSize]; omega
  obtain ⟨answer, queue, final, ticks, peak, bound, run, peakBound, finalSize, finalStack, finalOutput,
    finalPC, finalRunning, frame, answerIff, model⟩ :=
    ForestZeroAnswerReclaim.captured_model_reclaim_execution keep formula dual
      recordHeader recordStart recordEnd base (entry + 42) scan seedDone conflict indexed program
      indexPhysical indexHeader indexFIFO separated
      (by intro phase; rw [show entry + 42 + 6 = entry + 48 by omega]; exact setupAt phase) scanAt indexPC indexRunning indexZero indexOne
      indexRoom (by omega) scanCapacity indexKeep prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity
      advanceCapacity bucketCapacity readyCapacity cleanupEntry returnPc rest
      (indexStack.trans savedKeep) indexCursor captureAt tag0 tag1 emitAt successSetup successLoop
      successCapacity conflictAt conflictCapacity cleanupFits cleanupSetup cleanupLoop cleanupCapacity oneFits
  have indexLive : indexed.liveWords = state.liveWords +
      2 * (IndexScan.occurrences formula.clauses.toList recordStart).length := by
    unfold State.liveWords
    rw [indexSize, indexStack, indexOutput]
    omega
  have retained : PrefixFrame keep state.heap indexed.heap :=
    ⟨prefixBound, indexKeep, fun address below => indexFrame.2.2 address (by omega)⟩
  refine ⟨answer, queue, final,
    (16 * (IndexScan.occurrences formula.clauses.toList recordStart).length +
      18 * formula.clauses.toList.length + 16) + ticks, _, ?_, indexRun.append run, ?_, finalSize, finalStack,
    ?_, finalPC, finalRunning, ForestZeroBackendFrame.trans retained frame, answerIff, model⟩
  · rw [indexSize] at bound
    omega
  · rw [indexLive] at peakBound
    omega
  · simpa only [indexOutput] using finalOutput

/-- Incidence construction and the fetched cleanup-count capture prepare the
original-channel solver continuation without emitting a local-coordinate model. -/
theorem indexed_capture_inputs (keep : Nat) (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (entry recordHeader recordStart recordEnd base : Nat) (state : State width 8)
    (savePresent : SaveAt program entry recordHeader)
    (indexPresent : Controller.Horn.IndexScan.At (n := n) program (entry + 7) base recordStart)
    (restorePresent : RestoreAt program (entry + 39))
    (capturePresent : ∀ phase : Fin 6, program[entry + 42 + phase.val]? =
      (ForestZeroReclaim.captureCode width)[phase.val]?)
    (physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base 0 state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (positiveBase : 0 < base) (baseBound : base ≤ state.heap.size)
    (headerBelow : recordHeader < base) (keepBelow : keep ≤ base)
    (fifo : WorklistMark.Stored ([] : List (Fin n)) base state.heap)
    (capacity : entry + 48 < 2 ^ width)
    (room : state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length < 2 ^ width)
    (rest : List (Word width)) (saved : state.stack = word width keep :: rest) :
    ∃ final, Execution program state final
      (16 * (IndexScan.occurrences clauses recordStart).length + 18 * clauses.length + 22)
      (state.liveWords + 2 * (IndexScan.occurrences clauses recordStart).length + 1) ∧
      IndexScan.PhysicalIndex clauses recordStart recordEnd base
        (IndexScan.occurrences clauses recordStart).length final.heap ∧
      Controller.Horn.SourceScan.CursorStored recordEnd recordHeader final.heap ∧
      WorklistMark.Stored ([] : List (Fin n)) base final.heap ∧
      PrefixFrame base state.heap final.heap ∧
      final.heap.size = state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length ∧
      final.heap.size = keep +
        (state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length - keep) ∧
      final.stack = word width
        (state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length - keep) :: rest ∧
      final.output = state.output ∧ final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.pc = word width (entry + 48) ∧ final.halted = false := by
  obtain ⟨indexed, indexRun, indexPhysical, indexFrame, indexStack, indexOutput,
    indexSize, indexCursor, indexZero, indexOne, indexPC, indexRunning, indexMarks, indexFIFO⟩ :=
    wrapped_index_execution base program clauses entry recordHeader recordStart recordEnd base state
      savePresent indexPresent restorePresent physical header position running zero one positiveBase
      baseBound (Nat.le_refl _) positiveBase fifo (by omega) room
  have indexHeader := ForestZeroIndexFrame.header_frame indexFrame headerBelow header
  have indexRoom : indexed.heap.size < 2 ^ width := by rw [indexSize]; exact room
  have retained : keep ≤ indexed.heap.size := by rw [indexSize]; omega
  obtain ⟨final, captureRun, sameHeap, finalStack, finalOutput, finalPC, finalRunning, preserved⟩ :=
    ForestZeroReclaim.capture_execution program (entry + 42) keep indexed rest capturePresent
      indexPC indexRunning (by omega) indexRoom retained (indexStack.trans saved) indexCursor indexOne
  have indexLive : indexed.liveWords = state.liveWords +
      2 * (IndexScan.occurrences clauses recordStart).length := by
    unfold State.liveWords
    rw [indexSize, indexStack, indexOutput]
    omega
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, finalOutput.trans indexOutput,
    (preserved 2 (by decide) (by decide)).trans indexZero,
    (preserved 5 (by decide) (by decide)).trans indexOne, ?_, finalRunning⟩
  · have trace := indexRun.append captureRun
    rw [indexLive] at trace
    convert trace using 1 <;> omega
  · simpa only [sameHeap] using indexPhysical
  · simpa only [sameHeap] using indexHeader
  · simpa only [sameHeap] using indexFIFO
  · simpa only [sameHeap] using indexFrame
  · rw [sameHeap, indexSize]
  · rw [sameHeap, indexSize]
    omega
  · simpa only [indexSize] using finalStack
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC

end Controller.Cost.ForestZeroIndexMarks
