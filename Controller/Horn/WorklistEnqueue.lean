module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistMark

@[expose] public section

/-! A fresh physical off guard commits one FIFO label; a stale guard returns
without changing storage. Off flags represent all marked FIFO history, while
propagation counts refer to its processed prefix and the current bucket prefix. -/
namespace Controller.Horn.WorklistEnqueue
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.IndexScanOuter
open Controller.Horn.IndexScanLoop Controller.Horn.IndexScanRefinement Controller.Horn.IndexScanWhole
variable {width n : Nat}

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

/-- A fetched guard and mark-before-enqueue commit form one six-tick path. -/
theorem fresh_execution (program : Program width 8) (entry exit base : Nat)
    (enqueued : List (Fin n)) (label : Fin n) (state : State width 8)
    (present : At program entry exit) (stored : Stored enqueued base state.heap)
    (fresh : label ∉ enqueued)
    (offHeld : state.reg 3 = word width (offAddress base label))
    (tailHeld : state.reg 0 = word width (queueStart (n := n) base + enqueued.length))
    (labelHeld : state.reg 1 = word width label.val)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 7 < 2 ^ width) (exitFits : exit < 2 ^ width)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      Stored (enqueued ++ [label]) base final.heap ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width (queueStart (n := n) base + enqueued.length + 1) ∧
      final.pc = word width exit ∧ final.halted = false := by
  have queueRoom := fresh_enqueue_bound enqueued stored.nodup label fresh
  have offBound : offAddress base label < state.heap.size := by
    have := stored.fits; have := label.isLt; unfold offAddress; omega
  have queueBound : queueStart (n := n) base + enqueued.length < state.heap.size := by
    have := stored.fits; unfold queueStart; omega
  have off : state.heap[offAddress base label]'offBound = word width 0 := by
    simpa only [ite_eq_right fresh] using stored.flags label
  let loaded := state.advance.put 4 (word width 0)
  let middle := Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)
  have first := fresh_guard program entry exit base state label present offBound off offHeld position running capacity room
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame loaded 4 (entry + 3)
  have middleHeap : middle.heap = state.heap := frame.2.1
  have middleLive : middle.liveWords = state.liveWords := by
    change (Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)).liveWords = _
    rw [frame.2.2.2.2.2]
    rfl
  have middleRegister (register : Fin 8) (different : register ≠ 4) : middle.reg register = state.reg register := by
    change (Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)).reg register = _
    rw [frame.1]
    simp [loaded, State.put, State.advance, different]
  obtain ⟨final, second, finalHeap, size, stack, output, tail, finalPosition, finalRunning⟩ :=
    commit_execution program entry exit base enqueued label middle present
      (by simpa only [middleHeap] using offBound) (by simpa only [middleHeap] using queueBound)
      ((middleRegister 3 (by decide)).trans offHeld) ((middleRegister 0 (by decide)).trans tailHeld)
      ((middleRegister 1 (by decide)).trans labelHeld) ((middleRegister 5 (by decide)).trans one)
      ((middleRegister 2 (by decide)).trans zero) first.2.1
      (by change (Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)).halted = false
          rw [frame.2.2.2.2.1]; exact running)
      capacity exitFits (by simpa only [middleHeap] using room)
  refine ⟨final, ?_, ?_, size.trans (congrArg Array.size middleHeap),
    stack.trans frame.2.2.1, output.trans frame.2.2.2.1, tail, finalPosition, finalRunning⟩
  · simpa only [middleLive, Nat.max_self, Nat.reduceAdd] using first.1.append second
  · rw [finalHeap]
    exact committed_stored enqueued base middle (by simpa only [middleHeap] using stored) label fresh _ _

/-- A marked label takes the fetched stale branch and leaves the physical FIFO
and all original records and bucket links unchanged. -/
theorem stale_execution (program : Program width 8) (entry exit base : Nat) (state : State width 8)
    (label : Fin n) (present : At program entry exit)
    (offBound : offAddress base label < state.heap.size)
    (off : state.heap[offAddress base label]'offBound = word width 1)
    (held : state.reg 3 = word width (offAddress base label)) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 7 < 2 ^ width) (exitFits : exit < 2 ^ width)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = state.reg 0 ∧ final.pc = word width exit ∧ final.halted = false := by
  let loaded := state.advance.put 4 (word width 1)
  let tested := Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)
  let final := Controller.Horn.RuleDispatch.branchFinished tested 2 exit
  have loadAt : program[entry]? = some (.load 4 3) := by simpa [code] using present ⟨0, by decide⟩
  have branchAt : program[entry + 1]? = some (.branchZero 4 (word width (entry + 3))) := by simpa [code] using present ⟨1, by decide⟩
  have returnAt : program[entry + 2]? = some (.branchZero 2 (word width exit)) := by simpa [code] using present ⟨2, by decide⟩
  have addressFits : offAddress base label < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by have := label.isLt; unfold offAddress at offBound; omega
  have first : programStep program state = some loaded := by
    unfold programStep
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega), loadAt]
    simp [step, held, loaded, running, offBound, off, word_val (width := width) (offAddress base label) addressFits]
  have loadedPosition : loaded.pc = word width (entry + 1) := by
    simp [loaded, State.put, State.advance, position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have second := Controller.Horn.RuleDispatch.branch_execution program (entry + 1) (entry + 3) 4 branchAt loaded
    loadedPosition (by simpa [loaded, State.put, State.advance] using running) (by omega)
  have testedEq : tested = loaded.advance := by
    change Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3) = _
    have loadedOne : (loaded.reg 4).val = 1 := by
      change (word width 1).val = 1
      exact word_val 1 oneFits
    unfold Controller.Horn.RuleDispatch.branchFinished
    rw [loadedOne]
    rfl
  have testedPosition : tested.pc = word width (entry + 2) := by
    rw [testedEq]
    simp only [State.advance, loadedPosition, word_val (width := width) (entry + 1) (by omega)]
  have testedZero : tested.reg 2 = word width 0 := by
    simpa only [testedEq, State.advance, loaded, State.put, ite_eq_right (show (2 : Fin 8) ≠ 4 by decide)] using zero
  have third := Controller.Horn.RuleDispatch.branch_execution program (entry + 2) exit 2 returnAt tested
    testedPosition (by simpa only [testedEq, State.advance, loaded, State.put] using running) (by omega)
  have testedFrame := Controller.Horn.RuleDispatch.branchFinished_frame loaded 4 (entry + 3)
  have finalFrame := Controller.Horn.RuleDispatch.branchFinished_frame tested 2 exit
  refine ⟨final, ?_, finalFrame.2.1.trans testedFrame.2.1,
    finalFrame.2.2.1.trans testedFrame.2.2.1, finalFrame.2.2.2.1.trans testedFrame.2.2.2.1, ?_, ?_, ?_⟩
  · have loadedLive : loaded.liveWords = state.liveWords := rfl
    have testedLive : tested.liveWords = state.liveWords := by rw [testedEq]; rfl
    simpa only [loadedLive, testedLive, Nat.max_self, Nat.reduceAdd] using Execution.cons first (second.append third)
  · change (Controller.Horn.RuleDispatch.branchFinished tested 2 exit).reg 0 = _
    rw [finalFrame.1, testedEq]
    simp [loaded, State.put, State.advance]
  · simp [final, Controller.Horn.RuleDispatch.branchFinished, testedZero, word]
  · change (Controller.Horn.RuleDispatch.branchFinished tested 2 exit).halted = false
    rw [finalFrame.2.2.2.2.1, testedEq]
    exact running

/-- Even bucket-head writes never modify an odd variable-off cell. -/
theorem linked_off_frame (state : State width 8) (base row previous : Nat) (label query : Fin n)
    (headBound : headAddress base label < state.heap.size)
    (offBound : offAddress base query < state.heap.size) :
    (IndexBuild.linkedHeap state base label row previous headBound)[offAddress base query]? =
      state.heap[offAddress base query]? := by
  have different : headAddress base label ≠ offAddress base query := by
    unfold headAddress offAddress; omega
  exact IndexBuild.incidence_old_frame state base row previous label headBound _ offBound different

/-- The off words used by the FIFO guard are the physical odd mark cells. -/
def CleanOff (base : Nat) (heap : Array (Word width)) : Prop :=
  ∀ label : Fin n, heap[offAddress base label]? = some (word width 0)

/-- The actual normalizer endpoint supplies the clean off cells. -/
theorem normalized_clean_off (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses) (recordStart index : Nat)
    (marks : Controller.Horn.Worklist.IndexedNormalize.Marks n) (state : State width 8)
    (invariant : Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart index marks state) :
    CleanOff (n := n) layout.base state.heap := by
  intro label
  exact (scratch_zero invariant label).2

/-- The fetched row setup writes only the even scratch endpoint header. -/
theorem setup_clean_off (state : State width 8) (entry base offset count : Nat)
    (headerBound : base + 2 * n < state.heap.size) (clean : CleanOff (n := n) base state.heap) :
    CleanOff (n := n) base (IndexScan.rowFinished state entry base offset count headerBound).heap := by
  intro label
  have different : base + 2 * n ≠ offAddress base label := by
    have := label.isLt
    unfold offAddress
    omega
  change (state.heap.set (base + 2 * n) (word width (offset + 3 + count)) headerBound)[offAddress base label]? = _
  rw [Array.getElem?_set_ne headerBound different]
  exact clean label

/-- Each actual sixteen-tick body endpoint preserves the clean odd off cells. -/
theorem body_clean_off (state : State width 8) (entry base pointer limit row previous : Nat)
    (label : Fin n) (headBound : headAddress base label < state.heap.size)
    (clean : CleanOff (n := n) base state.heap) :
    CleanOff (n := n) base (Controller.Horn.IndexScanLoop.bodyFinished state entry base pointer limit row previous label headBound).heap := by
  rw [Controller.Horn.IndexScanLoop.body_heap]
  intro query
  have bound : offAddress base query < state.heap.size := by
    have value := clean query
    by_contra outside
    have absent : state.heap[offAddress base query]? = none := Array.getElem?_eq_none (by omega)
    rw [absent] at value
    contradiction
  rw [linked_off_frame state base row previous label query headBound bound]
  exact clean query

/-- The existing sixteen-tick body trace also carries its physical off-cell frame. -/
theorem indexed_body_step_clean (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (remaining : consumed < (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (clean : CleanOff (n := n) base state.heap)
    (positiveBase : 0 < base)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width) :
    ∃ final, Execution program state final 16 (state.liveWords + 2) ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex (consumed + 1) (processed + 1) final ∧
      final.heap.size = state.heap.size + 2 ∧ final.stack = state.stack ∧ final.output = state.output ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap ∧ CleanOff (n := n) base final.heap := by
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
  refine ⟨final, trace, ?_, frame.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1, finalHeader,
    body_clean_off state entry base pointer limit row previous label headBound clean⟩
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

theorem indexed_body_prefix_clean (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (capacity : entry + 32 < 2 ^ width)
    (positiveBase : 0 < base)
    (count consumed processed : Nat) (state : State width 8)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (clean : CleanOff (n := n) base state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (remaining : consumed + count ≤ (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (room : state.heap.size + 2 * count < 2 ^ width) :
    ∃ final, Execution program state final (16 * count) (state.liveWords + 2 * count) ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex (consumed + count) (processed + count) final ∧
      final.heap.size = state.heap.size + 2 * count ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap ∧ CleanOff (n := n) base final.heap := by
  induction count generalizing consumed processed state with
  | zero =>
      exact ⟨state, by simpa using Execution.refl state, by simpa using invariant,
        by simp, rfl, rfl, header, clean⟩
  | succ count ih =>
      obtain ⟨middle, first, next, growth, stack, output, nextHeader, nextClean⟩ := indexed_body_step_clean program clauses
        recordStart recordEnd base entry rowIndex consumed processed state present invariant
        (by omega) clean positiveBase header capacity (by omega)
      obtain ⟨final, tail, result, totalGrowth, finalStack, finalOutput, finalHeader, finalClean⟩ :=
        ih (consumed + 1) (processed + 1) middle next nextClean nextHeader (by omega) (by omega)
      have middleLive : middle.liveWords = state.liveWords + 2 := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_, by omega, finalStack.trans stack, finalOutput.trans output, finalHeader, finalClean⟩
      · have trace := first.append tail
        rw [middleLive] at trace
        convert trace using 1 <;> omega
      · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using result

theorem setup_row_clean (program : Program width 8)
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
    (clean : CleanOff (n := n) base state.heap)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex 0 processed final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap ∧ CleanOff (n := n) base final.heap := by
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
  refine ⟨final, trace, ?_, finalSize, rfl, rfl, finalHeader, setup_clean_off state entry base row rule.positives.length headerBound clean⟩
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

theorem terminal_row_clean (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (complete : consumed = (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (clean : CleanOff (n := n) base state.heap)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      RowDone clauses recordStart recordEnd base entry rowIndex processed 0 state final ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap ∧ CleanOff (n := n) base final.heap := by
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
  refine ⟨final, by simpa [tested, test_live] using first.append second, ?_, finalHeader, by simpa only [heap] using clean⟩
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

theorem indexed_row_suffix_clean (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed count : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (complete : consumed + count =
      (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (positiveBase : 0 < base)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (clean : CleanOff (n := n) base state.heap)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 * count < 2 ^ width) :
    ∃ final, Execution program state final (16 * count + 6) (state.liveWords + 2 * count) ∧
      RowDone clauses recordStart recordEnd base entry rowIndex (processed + count) count state final ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap ∧ CleanOff (n := n) base final.heap := by
  obtain ⟨middle, first, next, growth, stack, output, middleHeader, middleClean⟩ := indexed_body_prefix_clean program clauses
    recordStart recordEnd base entry rowIndex present capacity positiveBase count consumed processed state invariant clean header (by omega) room
  obtain ⟨final, second, result, finalHeader, finalClean⟩ := terminal_row_clean program clauses recordStart recordEnd base entry rowIndex
    (consumed + count) (processed + count) middle present next complete middleHeader middleClean capacity (by omega)
  have middleLive : middle.liveWords = state.liveWords + 2 * count := by
    unfold State.liveWords
    rw [growth, stack, output]
    omega
  refine ⟨final, ?_, ?_, finalHeader, finalClean⟩
  · have trace := first.append second
    rw [middleLive, Nat.max_self] at trace
    exact trace
  · refine ⟨result.physical, result.position, result.rowHeld, result.allocationHeld,
      result.zero.trans (next.zero.trans invariant.zero.symm),
      result.one.trans (next.one.trans invariant.one.symm), ?_,
      result.stack.trans stack, result.output.trans output, result.running⟩
    have := result.growth
    omega

theorem outer_row_clean (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : OuterInvariant clauses recordStart recordEnd base entry rowIndex processed state)
    (rowBound : rowIndex < clauses.length) (positiveBase : 0 < base)
    (clean : CleanOff (n := n) base state.heap)
    (capacity : entry + 32 < 2 ^ width)
    (room : state.heap.size + 2 *
      (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length < 2 ^ width) :
    let count := (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'rowBound)).positives.length
    ∃ final, Execution program state final (16 * count + 18) (state.liveWords + 2 * count) ∧
      OuterInvariant clauses recordStart recordEnd base entry (rowIndex + 1) (processed + count) final ∧
      final.heap.size = state.heap.size + 2 * count ∧ final.stack = state.stack ∧ final.output = state.output ∧ CleanOff (n := n) base final.heap := by
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
  obtain ⟨middle, second, body, growth, stack, output, middleHeader, middleClean⟩ := setup_row_clean program clauses
    recordStart recordEnd base entry rowIndex processed tested present rowBound testedPhysical invariant.processedEq
    headerBound ((test_reg state _ _ _ _ 1 (by decide) (by decide)).trans invariant.rowHeld)
    (by simpa [tested] using (test_reg state _ _ _ _ 7 (by decide) (by decide)).trans invariant.allocationHeld)
    ((test_reg state _ _ _ _ 2 (by decide) (by decide)).trans invariant.zero)
    ((test_reg state _ _ _ _ 5 (by decide) (by decide)).trans invariant.one)
    testedPosition (by simpa [tested] using invariant.running) positiveBase testedHeader (by simpa only [tested, test_heap] using clean) capacity
    (by simpa [tested] using (show state.heap.size < 2 ^ width by omega))
  obtain ⟨final, third, result, finalHeader, finalClean⟩ := indexed_row_suffix_clean program clauses
    recordStart recordEnd base entry rowIndex 0 processed count middle present body (by simp [count])
    positiveBase middleHeader middleClean capacity (by rw [growth]; simpa [tested] using room)
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [growth, stack, output]
    simp [tested]
  refine ⟨final, ?_, ?_, ?_, result.stack.trans (stack.trans (test_stack state _ _ _ _)),
    result.output.trans (output.trans (test_output state _ _ _ _)), finalClean⟩
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

theorem outer_suffix_clean (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (positiveBase : 0 < base) (capacity : entry + 32 < 2 ^ width)
    (rows rowIndex processed : Nat) (state : State width 8)
    (invariant : OuterInvariant clauses recordStart recordEnd base entry rowIndex processed state)
    (clean : CleanOff (n := n) base state.heap)
    (complete : rowIndex + rows = clauses.length)
    (room : state.heap.size + 2 * ((IndexScan.occurrences clauses recordStart).length - processed) < 2 ^ width) :
    ∃ final, Execution program state final
      (16 * ((IndexScan.occurrences clauses recordStart).length - processed) + 18 * rows + 4)
      (state.liveWords + 2 * ((IndexScan.occurrences clauses recordStart).length - processed)) ∧
      ScanDone clauses recordStart recordEnd base entry
        ((IndexScan.occurrences clauses recordStart).length - processed) state final ∧ CleanOff (n := n) base final.heap := by
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
      refine ⟨final, by simpa [allProcessed] using trace, ?_, by simpa only [final, test_heap] using clean⟩
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
      obtain ⟨middle, first, next, growth, stack, output, middleClean⟩ := outer_row_clean program clauses
        recordStart recordEnd base entry rowIndex processed state present invariant rowBound positiveBase clean capacity incidenceRoom
      have physicalBound : processed + count ≤ (IndexScan.occurrences clauses recordStart).length := next.physical.prefixBound
      obtain ⟨final, tail, result, finalClean⟩ := ih (rowIndex + 1) (processed + count) middle next middleClean (by omega) (by omega)
      have middleLive : middle.liveWords = state.liveWords + 2 * count := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_, finalClean⟩
      · have trace := first.append tail
        rw [middleLive] at trace
        convert trace using 1 <;> omega
      · refine ⟨result.physical, result.header, result.position, result.allocationHeld,
          result.zero.trans (next.zero.trans invariant.zero.symm),
          result.one.trans (next.one.trans invariant.one.symm), ?_,
          result.stack.trans stack, result.output.trans output, result.running⟩
        have := result.growth
        omega

theorem all_rows_clean (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base 0 state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (positiveBase : 0 < base) (position : state.pc = word width entry)
    (running : state.halted = false) (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (clean : CleanOff (n := n) base state.heap)
    (capacity : entry + 32 < 2 ^ width)
    (room : state.heap.size + 2 * (IndexScan.occurrences clauses recordStart).length < 2 ^ width) :
    ∃ final, Execution program state final
      (16 * (IndexScan.occurrences clauses recordStart).length + 18 * clauses.length + 6)
      (state.liveWords + 2 * (IndexScan.occurrences clauses recordStart).length) ∧
      ScanDone clauses recordStart recordEnd base entry (IndexScan.occurrences clauses recordStart).length state final ∧ CleanOff (n := n) base final.heap := by
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
  obtain ⟨final, tail, result, finalClean⟩ := outer_suffix_clean program clauses recordStart recordEnd base entry present
    positiveBase capacity clauses.length 0 0 middle middleInvariant (by simpa only [middle, frame.1] using clean) (by omega) (by simpa [middle, frame.1] using room)
  refine ⟨final, ?_, ⟨result.physical, result.header, result.position, result.allocationHeld,
    result.zero.trans (frame.2.2.2.2.2 2 (by decide) (by decide)),
    result.one.trans (frame.2.2.2.2.2 5 (by decide) (by decide)), ?_,
    result.stack.trans frame.2.1, result.output.trans frame.2.2.1, result.running⟩, finalClean⟩
  · have trace := first.append tail
    rw [middleLive] at trace
    convert trace using 1 <;> simp only [Nat.sub_zero] <;> omega
  · simpa only [Nat.sub_zero, middle, frame.1] using result.growth

open Controller.Horn.IndexScanCold in
theorem cold_execution_clean (clauses : List (Controller.CNF.Clause (Fin n)))
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (codeFits : (program width clauses).size < 2 ^ width)
    (heapFits : recordStart width clauses + 3 * clauses.length + 3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ final : State width 8, ∃ recordEnd ticks peak : Nat,
      Execution (program width clauses) state final ticks peak ∧
      IndexScan.PhysicalIndex clauses (recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses)
        (IndexScan.occurrences clauses (recordStart width clauses)).length final.heap ∧
      final.pc = word width (program width clauses).size ∧
      final.stack = suffix ∧ final.output = state.output ∧
      ticks ≤ 25 * n + 83 * (clauses.map List.length).sum + 95 * clauses.length + 66 ∧
      peak ≤ state.liveWords + 5 * n + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      CleanOff (n := n) (Controller.Horn.SourceSerialize.base clauses) final.heap ∧
      programWords (program width clauses) + peak ≤
        4 * (IndexScanCold.entry width clauses + 32) + state.liveWords + 5 * n + 4 +
          3 * clauses.length + 3 * (clauses.map List.length).sum := by
  obtain ⟨normalized, marks, normalizeTicks, normalizePeak, normalizeTrace, invariant,
      normalizePosition, normalizeStack, normalizeOutput, normalizeCost, normalizeStorage⟩ :=
    Controller.Horn.NormalizeCold.execution clauses state suffix emptyHeap input position running dual
      (by have := program_size (width := width) clauses; unfold entry at this; omega)
      (by unfold recordStart at heapFits; omega)
  have physical := IndexScan.initial clauses (Controller.Horn.SourceSerialize.layout clauses)
    (recordStart width clauses) marks normalized invariant
  have header : Controller.Horn.SourceScan.CursorStored normalized.heap.size 0 normalized.heap := by
    simpa [Controller.Horn.SourceSerialize.layout] using invariant.recordCursor
  have endpoints := invariant.records.endpoint
  have packed := packed_endpoint clauses (recordStart width clauses)
  have incidences := occurrences_length_le clauses (recordStart width clauses)
  have scanRoom : normalized.heap.size + 2 * (IndexScan.occurrences clauses (recordStart width clauses)).length < 2 ^ width := by
    change normalized.heap.size = Controller.Horn.NormalizeLoop.recordOffset clauses (recordStart width clauses) clauses.length at endpoints
    omega
  obtain ⟨final, scanTrace, result, finalClean⟩ := all_rows_clean (program width clauses) clauses (recordStart width clauses)
    normalized.heap.size (Controller.Horn.SourceSerialize.base clauses) (entry width clauses) normalized
    (index_at clauses) physical header (Controller.Horn.IndexScanWhole.cold_base_positive clauses)
    normalizePosition invariant.input.running invariant.input.zero invariant.input.one
    (normalized_clean_off clauses (Controller.Horn.SourceSerialize.layout clauses)
      (recordStart width clauses) clauses.length marks normalized invariant)
    (by simpa only [program_size] using codeFits) scanRoom
  let full := (append_execution _ _ normalizeTrace).append scanTrace
  refine ⟨final, normalized.heap.size, normalizeTicks +
    (16 * (IndexScan.occurrences clauses (recordStart width clauses)).length + 18 * clauses.length + 6),
    max normalizePeak (normalized.liveWords + 2 * (IndexScan.occurrences clauses (recordStart width clauses)).length),
    full, result.physical, ?_, result.stack.trans normalizeStack, result.output.trans normalizeOutput, ?_, ?_, finalClean, ?_⟩
  · simpa only [program_size] using result.position
  · omega
  · have resident := normalizeTrace.final_storage_le
    omega
  · have resident := normalizeTrace.final_storage_le
    rw [program_words]
    omega

end Controller.Horn.WorklistEnqueue
