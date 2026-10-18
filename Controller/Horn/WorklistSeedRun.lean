module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistSeed
public import Controller.Horn.WorklistFIFORun

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The cold seed scan executes in the appended machine program. Its initial
header setup covers empty formulas, and its row cursor follows original record
successors without rebuilding an index. -/
namespace Controller.Horn.WorklistSeedRun
open Controller.Cost Controller.Horn.WorklistSeed Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketReady
variable {width n : Nat}

/-- The initial scan retains the original linked index and original support
length counts. Its marked queue may grow without processing any queue label. -/
structure ScanInvariant (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) : Prop where
  indexBound : index ≤ clauses.length
  spine : Controller.Horn.WorklistPropagation.Spine clauses recordStart recordEnd base state.heap
  fifo : Stored queue base state.heap
  rows : ∀ row : Fin clauses.length,
    Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[row.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart row.val)
      (Controller.Horn.Worklist.compileClause clauses[row.val]).positives.length (fired row) state.heap
  unvisited : ∀ row : Fin clauses.length, index ≤ row.val → fired row = false
  complete : SeedComplete clauses index fired
  forced : QueueForced clauses queue
  firedEmpty : ∀ row : Fin clauses.length, fired row = true →
    (Controller.Horn.Worklist.compileClause clauses[row.val]).positives.length = 0
  firedHead : ∀ row : Fin clauses.length, fired row = true →
    ∃ head labels, Controller.Horn.Worklist.compileClause clauses[row.val] = .negative head labels ∧ head ∈ queue
  header : state.heap[Controller.Horn.WorklistFIFO.headSlot (n := n) base]? = some (word width recordEnd)
  tail : state.heap[tailSlot (n := n) base]? = some (word width (queueStart (n := n) base + queue.length))
  held : state.reg 1 = word width (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index)
  zero : state.reg 2 = word width 0
  one : state.reg 5 = word width 1
  decrement : state.reg 6 = word width (2 ^ width - 1)
  position : state.pc = word width entry
  running : state.halted = false
  room : state.heap.size < 2 ^ width

/-- Passing a nonempty or disabled original row extends the completed seed
prefix without modifying fired tags or relying on pending flags. -/
theorem complete_unfired_row (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Fin clauses.length) (fired : Fin clauses.length → Bool)
    (complete : SeedComplete clauses index.val fired)
    (inactive : (Controller.Horn.Worklist.compileClause clauses[index.val]).enabled = false ∨
      0 < (Controller.Horn.Worklist.compileClause clauses[index.val]).positives.length) :
    SeedComplete clauses (index.val + 1) fired := by
  intro other before enabled empty
  by_cases same : other = index
  · subst other
    rcases inactive with disabled | nonempty
    · rw [disabled] at enabled
      contradiction
    · omega
  · have distinct : other.val ≠ index.val := fun equation => same (Fin.ext equation)
    exact complete other (by omega) enabled empty

/-- The original-row endpoint test changes only comparison registers and PC. -/
theorem row_test_frame (state : State width 8) (header pointer endpoint exit : Nat) :
    let final := Controller.Horn.IndexScan.testFinished state header pointer endpoint exit
    final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
    final.halted = state.halted ∧ final.liveWords = state.liveWords ∧
    (∀ register : Fin 8, register ≠ 3 → register ≠ 4 → final.reg register = state.reg register) := by
  dsimp only
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame
    (Controller.Horn.IndexScan.testCompared state header pointer endpoint) 3 exit
  refine ⟨frame.2.1, frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1, ?_, ?_⟩
  · unfold Controller.Horn.IndexScan.testFinished
    rw [frame.2.2.2.2.2]
    rfl
  · intro register notThree notFour
    change (Controller.Horn.RuleDispatch.branchFinished
      (Controller.Horn.IndexScan.testCompared state header pointer endpoint) 3 exit).reg register = _
    rw [frame.1]
    simp [Controller.Horn.IndexScan.testCompared, State.put, State.advance, notThree, notFour]

/-- Eight fetched instructions test the actual original cursor, load the
original support length and dispatch its zero/nonzero branch. -/
theorem row_dispatch_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ final.liveWords = state.liveWords ∧
      final.reg 1 = state.reg 1 ∧ final.reg 2 = word width 0 ∧
      final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.reg 7 = word width (Controller.Horn.Worklist.compileClause clauses[index]).positives.length ∧
      final.pc = word width (if (Controller.Horn.Worklist.compileClause clauses[index]).positives.length = 0
        then entry + 13 else entry + 8) := by
  let row := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index
  let count := (Controller.Horn.Worklist.compileClause clauses[index]).positives.length
  have original := invariant.rows ⟨index, nonempty⟩
  have beforeEnd : row < recordEnd := by
    rw [invariant.spine.originalEnd]
    exact Controller.Horn.IndexScanWhole.recordOffset_before_end clauses recordStart index nonempty
  have endFits : recordEnd < 2 ^ width := by
    have endpoint := invariant.spine.endpoint
    have room := invariant.room
    omega
  have rowFits : row < 2 ^ width := by omega
  have headerBound : Controller.Horn.WorklistFIFO.headSlot (n := n) base < state.heap.size := by
    have fits := invariant.fifo.fits
    unfold Controller.Horn.WorklistFIFO.headSlot
    omega
  have headerCell : state.heap[Controller.Horn.WorklistFIFO.headSlot (n := n) base]'headerBound = word width recordEnd := by
    simpa only [Array.getElem?_eq_getElem headerBound, Option.some.injEq] using invariant.header
  let tested := Controller.Horn.IndexScan.testFinished state
    (Controller.Horn.WorklistFIFO.headSlot (n := n) base) row recordEnd done
  have testTrace := Controller.Horn.IndexScan.test_execution program entry
    (Controller.Horn.WorklistFIFO.headSlot (n := n) base) row recordEnd done 1 state
    (Controller.Horn.WorklistSeed.test_at program base entry done conflict present)
    invariant.position invariant.running headerBound headerCell invariant.held (by decide) (by decide)
    (by omega) (by have room := invariant.room; omega) rowFits endFits
  have testFrame := row_test_frame state (Controller.Horn.WorklistFIFO.headSlot (n := n) base) row recordEnd done
  have testedHeap : tested.heap = state.heap := testFrame.1
  have testPC : tested.pc = word width (entry + 4) := by
    simpa only [tested, ite_eq_right (by omega : row ≠ recordEnd)] using
      Controller.Horn.IndexScan.test_position state entry
        (Controller.Horn.WorklistFIFO.headSlot (n := n) base) row recordEnd done invariant.position (by omega) rowFits endFits
  have testedStored : Controller.Horn.WorklistStorage.MutableStored
      (Controller.Horn.Worklist.compileClause clauses[index]) row count (fired ⟨index, nonempty⟩) tested.heap := by
    simpa only [testedHeap, row, count] using original
  obtain ⟨loaded, loadTrace, countHeld, rowHeld, zeroHeld, oneHeld, decrementHeld,
      heap, stack, output, pc, live⟩ := count_load_execution program (entry + 4) row count
      (Controller.Horn.Worklist.compileClause clauses[index]) (fired ⟨index, nonempty⟩) tested testedStored
      (by simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨4, by decide⟩)
      (by simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨5, by decide⟩)
      (by simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨6, by decide⟩)
      ((testFrame.2.2.2.2.2 1 (by decide) (by decide)).trans invariant.held)
      ((testFrame.2.2.2.2.2 5 (by decide) (by decide)).trans invariant.one)
      testPC (testFrame.2.2.2.1.trans invariant.running) (by omega) (by simpa only [testedHeap] using invariant.room)
  let final := Controller.Horn.RuleDispatch.branchFinished loaded 7 (entry + 13)
  have finalFrame := Controller.Horn.RuleDispatch.branchFinished_frame loaded 7 (entry + 13)
  have loadedLive : loaded.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [heap, stack, output, testFrame.1, testFrame.2.1, testFrame.2.2.1]
  have branch := Controller.Horn.RuleDispatch.branch_execution program (entry + 7) (entry + 13) 7
    (by simpa [Controller.Horn.WorklistSeed.code] using present ⟨7, by decide⟩)
    loaded (by simpa [Nat.add_assoc] using pc) live (by omega)
  refine ⟨final, ?_, finalFrame.2.1.trans (heap.trans testFrame.1),
    finalFrame.2.2.1.trans (stack.trans testFrame.2.1),
    finalFrame.2.2.2.1.trans (output.trans testFrame.2.2.1),
    finalFrame.2.2.2.2.1.trans live, finalFrame.2.2.2.2.2.trans loadedLive,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tested, final, testFrame.2.2.2.2.1, loadedLive, Nat.max_self, Nat.reduceAdd] using
      (testTrace.append loadTrace).append branch
  · exact (congrFun finalFrame.1 1).trans (rowHeld.trans (testFrame.2.2.2.2.2 1 (by decide) (by decide)))
  · exact (congrFun finalFrame.1 2).trans (zeroHeld.trans ((testFrame.2.2.2.2.2 2 (by decide) (by decide)).trans invariant.zero))
  · exact (congrFun finalFrame.1 5).trans (oneHeld.trans ((testFrame.2.2.2.2.2 5 (by decide) (by decide)).trans invariant.one))
  · exact (congrFun finalFrame.1 6).trans (decrementHeld.trans ((testFrame.2.2.2.2.2 6 (by decide) (by decide)).trans invariant.decrement))
  · exact (congrFun finalFrame.1 7).trans countHeld
  · have countFits := original.countFits
    have countValue : (word width count).val = count := Nat.mod_eq_of_lt countFits
    have pcValue : (word width (entry + 4 + 3)).val = entry + 4 + 3 := Nat.mod_eq_of_lt (by omega)
    change (Controller.Horn.RuleDispatch.branchFinished loaded 7 (entry + 13)).pc =
      word width (if count = 0 then entry + 13 else entry + 8)
    unfold Controller.Horn.RuleDispatch.branchFinished
    rw [countHeld, countValue]
    by_cases zeroCount : count = 0
    · simp only [ite_eq_left zeroCount]
    · simp only [ite_eq_right zeroCount, State.advance, pc, pcValue, Nat.add_assoc, Nat.reduceAdd]

/-- A nonzero original record executes the actual thirteen-tick scan path and
advances the complete original-row invariant. -/
theorem nonzero_row_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (positive : 0 < (Controller.Horn.Worklist.compileClause clauses[index]).positives.length)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ final, Execution program state final 13 state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base entry (index + 1) queue fired final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  obtain ⟨dispatched, dispatchTrace, heap, stack, output, live, resident,
      rowHeld, zero, one, decrement, countHeld, pc⟩ :=
    row_dispatch_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
      invariant nonempty present capacity
  have atAdvance : ∀ phase : Fin 5, program[(entry + 8) + phase.val]? =
      (#[.add 1 1 7, .add 1 1 5, .add 1 1 5, .add 1 1 5,
        .branchZero 2 (word width entry)] : Program width 8)[phase.val]? := by
    intro phase
    fin_cases phase
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨8, by decide⟩
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨9, by decide⟩
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨10, by decide⟩
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨11, by decide⟩
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨12, by decide⟩
  have successorFits : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index + 3 +
      (Controller.Horn.Worklist.compileClause clauses[index]).positives.length < 2 ^ width := by
    have before := Controller.Horn.IndexScanWhole.recordOffset_mono clauses recordStart (index + 1) clauses.length
      (by omega) (by omega)
    rw [Controller.Horn.NormalizeLoop.recordOffset_succ clauses recordStart index nonempty] at before
    rw [← invariant.spine.originalEnd] at before
    have endpoint := invariant.spine.endpoint
    have room := invariant.room
    omega
  obtain ⟨final, advanceTrace, cursor, registers, finalHeap, finalStack, finalOutput, position, running⟩ :=
    nonzero_advance_execution program (entry + 8) entry
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index)
      (Controller.Horn.Worklist.compileClause clauses[index]).positives.length dispatched atAdvance
      (rowHeld.trans invariant.held) countHeld one zero
      (by simpa only [ite_eq_right (by omega : (Controller.Horn.Worklist.compileClause clauses[index]).positives.length ≠ 0)] using pc)
      live (by omega) successorFits
  have allHeap : final.heap = state.heap := finalHeap.trans heap
  refine ⟨final, ?_, ?_, congrArg Array.size allHeap, finalStack.trans stack, finalOutput.trans output⟩
  · simpa only [resident, Nat.max_self, Nat.reduceAdd] using dispatchTrace.append advanceTrace
  · refine ⟨by omega, ?_, ?_, ?_, ?_,
      complete_unfired_row clauses ⟨index, nonempty⟩ fired invariant.complete (Or.inr positive),
      invariant.forced, invariant.firedEmpty, invariant.firedHead, ?_, ?_, ?_,
      (registers 2 (by decide)).trans zero,
      (registers 5 (by decide)).trans one,
      (registers 6 (by decide)).trans decrement, position, running, ?_⟩
    · simpa only [allHeap] using invariant.spine
    · simpa only [allHeap] using invariant.fifo
    · intro other; simpa only [allHeap] using invariant.rows other
    · intro other bound; exact invariant.unvisited other (by omega)
    · simpa only [allHeap] using invariant.header
    · simpa only [allHeap] using invariant.tail
    · simpa only [Controller.Horn.NormalizeLoop.recordOffset_succ clauses recordStart index nonempty] using cursor
    · simpa only [allHeap] using invariant.room

/-- A zero-body original record saves its actual next record pointer before
the ready adapter reuses registers zero and four. -/
theorem prepare_zero_execution (program : Program width 8) (entry row : Nat) (state : State width 8)
    (present : ∀ phase : Fin 4, program[entry + phase.val]? =
      (#[.copy 4 1, .add 4 4 5, .add 4 4 5, .add 4 4 5] : Program width 8)[phase.val]?)
    (held : state.reg 1 = word width row) (one : state.reg 5 = word width 1)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 4 < 2 ^ width) (successorFits : row + 3 < 2 ^ width) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.reg 4 = word width (row + 3) ∧
      (∀ register : Fin 8, register ≠ 4 → final.reg register = state.reg register) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 4) ∧ final.halted = false := by
  let first := state.advance.put 4 (word width row)
  let second := first.advance.put 4 (word width (row + 1))
  let third := second.advance.put 4 (word width (row + 2))
  let final := third.advance.put 4 (word width (row + 3))
  have wordVal (value : Nat) (fits : value < 2 ^ width) : (word width value).val = value := Nat.mod_eq_of_lt fits
  have fetched (current : State width 8) (offset : Nat) (instruction : Instruction width 8)
      (pc : current.pc = word width (entry + offset)) (fits : entry + offset < 2 ^ width)
      (instructionAt : program[entry + offset]? = some instruction) : programStep program current = step instruction current := by
    unfold programStep
    rw [pc, wordVal (entry + offset) fits, instructionAt]
    rfl
  have nextPC (current : State width 8) (offset : Nat)
      (pc : current.pc = word width (entry + offset)) (fits : entry + offset < 2 ^ width) :
      current.advance.pc = word width (entry + offset + 1) := by
    simp only [State.advance, pc, wordVal (entry + offset) fits]
  have pc1 : first.pc = word width (entry + 1) := by simpa [first, State.put] using nextPC state 0 position (by omega)
  have pc2 : second.pc = word width (entry + 2) := by simpa [second, State.put, Nat.add_assoc] using nextPC first 1 pc1 (by omega)
  have pc3 : third.pc = word width (entry + 3) := by simpa [third, State.put, Nat.add_assoc] using nextPC second 2 pc2 (by omega)
  have oneFits : 1 < 2 ^ width := by omega
  have step1 : programStep program state = some first := by
    rw [fetched state 0 (.copy 4 1) position (by omega) (by simpa using present ⟨0, by decide⟩)]
    simp [step, running, held, first]
  have step2 : programStep program first = some second := by
    rw [fetched first 1 (.add 4 4 5) pc1 (by omega) (by simpa using present ⟨1, by decide⟩)]
    have rowFits : row < 2 ^ width := by omega
    simp [step, first, second, State.put, State.advance, running, one, wordVal row rowFits, wordVal 1 oneFits]
  have step3 : programStep program second = some third := by
    rw [fetched second 2 (.add 4 4 5) pc2 (by omega) (by simpa using present ⟨2, by decide⟩)]
    have rowFits : row + 1 < 2 ^ width := by omega
    simp [step, first, second, third, State.put, State.advance, running, one, wordVal (row + 1) rowFits, wordVal 1 oneFits]
  have step4 : programStep program third = some final := by
    rw [fetched third 3 (.add 4 4 5) pc3 (by omega) (by simpa using present ⟨3, by decide⟩)]
    have rowFits : row + 2 < 2 ^ width := by omega
    simp [step, first, second, third, final, State.put, State.advance, running, one, wordVal (row + 2) rowFits, wordVal 1 oneFits, Nat.add_assoc]
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, ?_, running⟩
  · simpa [first, second, third, final, State.put, State.advance, State.liveWords] using
      Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 (Execution.refl final))))
  · simp [first, second, third, final, State.put, State.advance]
  · intro register different
    simp [first, second, third, final, State.put, State.advance, different]
  · simpa [final, State.put, Nat.add_assoc] using nextPC third 3 pc3 (by omega)

/-- Twelve fetched instructions select an original zero-body row and save
its source-derived successor before ready dispatch. -/
theorem zero_prepare_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (zeroCount : (Controller.Horn.Worklist.compileClause clauses[index]).positives.length = 0)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ final, Execution program state final 12 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ final.liveWords = state.liveWords ∧
      final.reg 1 = state.reg 1 ∧ final.reg 2 = word width 0 ∧
      final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.reg 4 = word width (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart (index + 1)) ∧
      final.pc = word width (entry + 17) := by
  obtain ⟨dispatched, dispatchTrace, heap, stack, output, live, resident,
      rowHeld, zero, one, decrement, _, pc⟩ :=
    row_dispatch_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
      invariant nonempty present capacity
  have atPrepare : ∀ phase : Fin 4, program[(entry + 13) + phase.val]? =
      (#[.copy 4 1, .add 4 4 5, .add 4 4 5, .add 4 4 5] : Program width 8)[phase.val]? := by
    intro phase
    fin_cases phase
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨13, by decide⟩
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨14, by decide⟩
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨15, by decide⟩
    · simpa [Controller.Horn.WorklistSeed.code, Nat.add_assoc] using present ⟨16, by decide⟩
  have successorFits : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index + 3 < 2 ^ width := by
    have before := Controller.Horn.IndexScanWhole.recordOffset_mono clauses recordStart (index + 1) clauses.length
      (by omega) (by omega)
    rw [Controller.Horn.NormalizeLoop.recordOffset_succ clauses recordStart index nonempty, zeroCount] at before
    rw [← invariant.spine.originalEnd] at before
    have endpoint := invariant.spine.endpoint
    have room := invariant.room
    omega
  obtain ⟨final, prepareTrace, next, registers, finalHeap, finalStack, finalOutput, position, running⟩ :=
    prepare_zero_execution program (entry + 13)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) dispatched atPrepare
      (rowHeld.trans invariant.held) one (by simpa only [ite_eq_left zeroCount] using pc) live (by omega) successorFits
  refine ⟨final, ?_, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output, running,
    ?_, (registers 1 (by decide)).trans rowHeld, (registers 2 (by decide)).trans zero,
    (registers 5 (by decide)).trans one, (registers 6 (by decide)).trans decrement, ?_, ?_⟩
  · simpa only [resident, Nat.max_self, Nat.reduceAdd] using dispatchTrace.append prepareTrace
  · unfold State.liveWords
    rw [finalHeap, finalStack, finalOutput, heap, stack, output]
  · simpa only [Controller.Horn.NormalizeLoop.recordOffset_succ clauses recordStart index nonempty,
      zeroCount, Nat.add_zero] using next
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using position

/-- The original empty negative row executes the complete seed path, firing
its actual tag before enqueue. All pending marks leave original support-length
counts unchanged, and the next row retains the full semantic and physical state. -/
theorem negative_row_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (head : Fin n) (labels : List (Fin n))
    (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (original : Controller.Horn.Worklist.compileClause clauses[index] = .negative head labels)
    (empty : labels.length = 0)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ final, Execution program state final (if head ∈ queue then 36 else 39) state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base entry (index + 1) (queueAfter queue head)
        (fun other => if other = (⟨index, nonempty⟩ : Fin clauses.length) then true else fired other) final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  let selected : Fin clauses.length := ⟨index, nonempty⟩
  let nextFired := fun other => if other = selected then true else fired other
  have zeroCount : (Controller.Horn.Worklist.compileClause clauses[index]).positives.length = 0 := by
    simpa only [original, Controller.Horn.Worklist.Rule.positives] using empty
  obtain ⟨prepared, prepareTrace, preparedHeap, preparedStack, preparedOutput, preparedRunning, preparedLive,
      preparedRow, preparedZero, preparedOne, preparedDecrement, preparedNext, preparedPC⟩ :=
    zero_prepare_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
      invariant nonempty zeroCount present capacity
  have readyAt := Controller.Horn.WorklistSeed.ready_at program base entry done conflict present
  have tailBound : tailSlot (n := n) base < prepared.heap.size := by
    have fits := invariant.fifo.fits
    rw [preparedHeap]
    unfold tailSlot
    omega
  have tailCell : prepared.heap[tailSlot (n := n) base]'tailBound = word width (queueStart (n := n) base + queue.length) := by
    have value : prepared.heap[tailSlot (n := n) base]? = some (word width (queueStart (n := n) base + queue.length)) := by
      simpa only [preparedHeap] using invariant.tail
    simpa only [Array.getElem?_eq_getElem tailBound, Option.some.injEq] using value
  have preparedRows : ∀ other : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[other.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)
        (Controller.Horn.Worklist.compileClause clauses[other.val]).positives.length (fired other) prepared.heap := by
    intro other; simpa only [preparedHeap] using invariant.rows other
  have preparedSpine : Controller.Horn.WorklistPropagation.Spine clauses recordStart recordEnd base prepared.heap := by
    simpa only [preparedHeap] using invariant.spine
  have preparedFifo : Stored queue base prepared.heap := by simpa only [preparedHeap] using invariant.fifo
  have unfired : fired selected = false := invariant.unvisited selected (Nat.le_refl _)
  have preparedStored : Controller.Horn.WorklistStorage.MutableStored (.negative head labels)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) 0 false prepared.heap := by
    simpa only [selected, original, Controller.Horn.Worklist.Rule.positives, empty, unfired] using preparedRows selected
  have rowSeparation : base + 5 * n + 4 ≤ Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index := by
    have lower := Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart index
    omega
  have preparedRoom : prepared.heap.size < 2 ^ width := by simpa only [preparedHeap] using invariant.room
  obtain ⟨ready, readyTrace, readySpine, readyFifo, readyRows, readyForced, readyComplete,
      readyNext, readyZero, readyOne, readyDecrement, readySize, readyStack, readyOutput, readyPC, readyRunning⟩ :=
    negative_seed_execution clauses recordStart recordEnd base (entry + 17) (entry + 45) conflict (entry + 43)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart (index + 1)) program queue fired
      selected head labels prepared original empty unfired preparedSpine preparedFifo preparedRows invariant.forced
      invariant.complete separated readyAt tailBound tailCell (preparedRow.trans invariant.held)
      preparedNext preparedOne preparedZero preparedDecrement preparedPC preparedRunning (by omega) preparedRoom
  have readyHeader := negative_record_end_frame program base (entry + 17) (entry + 45) conflict (entry + 43)
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index)
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart (index + 1)) queue head labels prepared ready
    preparedStored readyAt preparedFifo rowSeparation tailBound tailCell (preparedRow.trans invariant.held)
    preparedNext preparedOne preparedZero preparedDecrement preparedPC preparedRunning (by omega) preparedRoom readyTrace
  obtain ⟨same, sameTrace, _, _, _, _, _, _, _, _, _, _, _, _, readyTail⟩ :=
    Controller.Horn.WorklistBucketNegative.negative_tail_framed program base (entry + 17) (entry + 45) conflict (entry + 43)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart (index + 1)) queue head labels prepared readyAt
      preparedFifo preparedStored rowSeparation tailBound tailCell (preparedRow.trans invariant.held)
      preparedNext preparedOne preparedZero preparedDecrement preparedPC preparedRunning (by omega) preparedRoom
  have sameEndpoint := Controller.Horn.JoinedRuleFrame.execution_endpoint_unique readyTrace sameTrace
  rw [← sameEndpoint] at readyTail
  obtain ⟨final, returnTrace, cursor, registers, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    cursor_return_execution program (entry + 43) entry 0 ready
      (by simpa [Controller.Horn.WorklistSeed.code, Controller.Horn.WorklistBucketReady.code] using present ⟨43, by decide⟩)
      (by simpa [Controller.Horn.WorklistSeed.code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨44, by decide⟩)
      readyPC readyRunning readyZero (by omega)
  have readyLive : ready.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [readySize, readyStack, readyOutput, preparedHeap, preparedStack, preparedOutput]
  have finalSize : final.heap.size = state.heap.size := by rw [finalHeap, readySize, preparedHeap]
  have stateRoom := invariant.room
  have headQueued : head ∈ queueAfter queue head := by
    by_cases stale : head ∈ queue <;> simp [queueAfter, stale]
  refine ⟨final, ?_, ?_, finalSize, finalStack.trans (readyStack.trans preparedStack),
    finalOutput.trans (readyOutput.trans preparedOutput)⟩
  · by_cases stale : head ∈ queue
    · simpa only [ite_eq_left stale, preparedLive, readyLive, Nat.max_self, Nat.reduceAdd] using
        (prepareTrace.append readyTrace).append returnTrace
    · simpa only [ite_eq_right stale, preparedLive, readyLive, Nat.max_self, Nat.reduceAdd] using
        (prepareTrace.append readyTrace).append returnTrace
  · refine ⟨by omega, ?_, ?_, ?_, ?_, readyComplete, readyForced, ?_, ?_, ?_, ?_,
      cursor.trans readyNext, (registers 2 (by decide)).trans readyZero,
      (registers 5 (by decide)).trans readyOne, (registers 6 (by decide)).trans readyDecrement,
      finalPC, finalRunning, by omega⟩
    · simpa only [finalHeap] using readySpine
    · simpa only [finalHeap] using readyFifo
    · intro other; simpa only [finalHeap] using readyRows other
    · intro other after
      have different : other ≠ selected := by intro same; rw [same] at after; change index + 1 ≤ index at after; omega
      change (if other = selected then true else fired other) = false
      rw [ite_eq_right different]
      exact invariant.unvisited other (by omega)
    · intro other marked
      change (if other = selected then true else fired other) = true at marked
      by_cases same : other = selected
      · simpa only [same, selected] using zeroCount
      · have old : fired other = true := by simpa only [ite_eq_right same] using marked
        exact invariant.firedEmpty other old
    · intro other marked
      change (if other = selected then true else fired other) = true at marked
      by_cases same : other = selected
      · exact ⟨head, labels, by simpa only [same, selected] using original, headQueued⟩
      · have old : fired other = true := by simpa only [ite_eq_right same] using marked
        obtain ⟨oldHead, oldLabels, source, queued⟩ := invariant.firedHead other old
        exact ⟨oldHead, oldLabels, source,
          Controller.Horn.WorklistBucketNegative.queue_after_includes queue head oldHead queued⟩
    · rw [finalHeap, readyHeader, preparedHeap]
      exact invariant.header
    · simpa only [finalHeap] using readyTail

/-- An original inert row follows the actual zero-tag bypass and saved cursor
return. No queue mark or fired store is performed. -/
theorem skip_row_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (original : Controller.Horn.Worklist.compileClause clauses[index] = .skip)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ final, Execution program state final 16 state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base entry (index + 1) queue fired final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  let selected : Fin clauses.length := ⟨index, nonempty⟩
  have zeroCount : (Controller.Horn.Worklist.compileClause clauses[index]).positives.length = 0 := by
    simp [original, Controller.Horn.Worklist.Rule.positives]
  obtain ⟨prepared, prepareTrace, preparedHeap, preparedStack, preparedOutput, preparedRunning, preparedLive,
      preparedRow, preparedZero, preparedOne, preparedDecrement, preparedNext, preparedPC⟩ :=
    zero_prepare_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
      invariant nonempty zeroCount present capacity
  have old : Controller.Horn.WorklistStorage.MutableStored (n := n) .skip
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) 0 false prepared.heap := by
    have unfired := invariant.unvisited selected (Nat.le_refl _)
    simpa only [preparedHeap, selected, original, Controller.Horn.Worklist.Rule.positives, List.length_nil, unfired] using invariant.rows selected
  have tagZero : Controller.Horn.WorklistStorage.MutableStored (n := n) .skip
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) 0 true prepared.heap := by
    refine ⟨old.fits, old.countFits, ?_, old.headValue, old.countValue, old.body⟩
    simpa [Controller.Horn.RuleCopy.tag] using old.tagValue
  obtain ⟨skipped, skipTrace, skippedHeap, skippedStack, skippedOutput, skipRegisters, skippedPC, skippedRunning⟩ :=
    Controller.Horn.WorklistBucketCases.fired_skip_execution program base (entry + 17) (entry + 45) conflict
      (entry + 43) (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) .skip 0 prepared tagZero
      (Controller.Horn.WorklistSeed.ready_at program base entry done conflict present)
      (preparedRow.trans invariant.held) preparedPC preparedRunning (by omega) (by simpa only [preparedHeap] using invariant.room)
  obtain ⟨final, returnTrace, cursor, registers, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    cursor_return_execution program (entry + 45) entry 4 skipped
      (by simpa [Controller.Horn.WorklistSeed.code, Controller.Horn.WorklistBucketReady.code] using present ⟨45, by decide⟩)
      (by simpa [Controller.Horn.WorklistSeed.code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨46, by decide⟩)
      skippedPC skippedRunning ((skipRegisters 2 (by decide)).trans preparedZero) (by omega)
  have skippedLive : skipped.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [skippedHeap, skippedStack, skippedOutput, preparedHeap, preparedStack, preparedOutput]
  have allHeap : final.heap = state.heap := finalHeap.trans (skippedHeap.trans preparedHeap)
  refine ⟨final, ?_, ?_, congrArg Array.size allHeap,
    finalStack.trans (skippedStack.trans preparedStack), finalOutput.trans (skippedOutput.trans preparedOutput)⟩
  · simpa only [preparedLive, skippedLive, Nat.max_self, Nat.reduceAdd] using
      (prepareTrace.append skipTrace).append returnTrace
  · refine ⟨by omega, ?_, ?_, ?_, ?_,
      complete_unfired_row clauses selected fired invariant.complete (Or.inl (by simp [selected, original, Controller.Horn.Worklist.Rule.enabled])),
      invariant.forced, invariant.firedEmpty, invariant.firedHead, ?_, ?_,
      cursor.trans ((skipRegisters 4 (by decide)).trans preparedNext),
      (registers 2 (by decide)).trans ((skipRegisters 2 (by decide)).trans preparedZero),
      (registers 5 (by decide)).trans ((skipRegisters 5 (by decide)).trans preparedOne),
      (registers 6 (by decide)).trans ((skipRegisters 6 (by decide)).trans preparedDecrement),
      finalPC, finalRunning, ?_⟩
    · simpa only [allHeap] using invariant.spine
    · simpa only [allHeap] using invariant.fifo
    · intro other; simpa only [allHeap] using invariant.rows other
    · intro other bound; exact invariant.unvisited other (by omega)
    · simpa only [allHeap] using invariant.header
    · simpa only [allHeap] using invariant.tail
    · simpa only [allHeap] using invariant.room

/-- An original empty positive clause reaches the actual conflict entry after
seventeen ticks, retaining caller storage and proving original-model impossibility. -/
theorem positive_row_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (labels : List (Fin n)) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (original : Controller.Horn.Worklist.compileClause clauses[index] = .positive labels)
    (empty : labels.length = 0)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ final, Execution program state final 17 state.liveWords ∧
      final.pc = word width conflict ∧ final.halted = false ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
        (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment := by
  let selected : Fin clauses.length := ⟨index, nonempty⟩
  have zeroCount : (Controller.Horn.Worklist.compileClause clauses[index]).positives.length = 0 := by
    simpa only [original, Controller.Horn.Worklist.Rule.positives] using empty
  obtain ⟨prepared, prepareTrace, preparedHeap, preparedStack, preparedOutput, preparedRunning, preparedLive,
      preparedRow, preparedZero, preparedOne, preparedDecrement, preparedNext, preparedPC⟩ :=
    zero_prepare_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
      invariant nonempty zeroCount present capacity
  have stored : Controller.Horn.WorklistStorage.MutableStored (.positive labels)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) 0 false prepared.heap := by
    have unfired := invariant.unvisited selected (Nat.le_refl _)
    simpa only [preparedHeap, selected, original, Controller.Horn.Worklist.Rule.positives, empty, unfired] using invariant.rows selected
  obtain ⟨final, positiveTrace, _, _, _, _, _, _, _, size, stack, output, pc, live⟩ :=
    Controller.Horn.WorklistBucketCases.positive_execution program base (entry + 17) (entry + 45) conflict (entry + 43)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) labels prepared stored
      (Controller.Horn.WorklistSeed.ready_at program base entry done conflict present)
      (preparedRow.trans invariant.held) preparedZero preparedDecrement preparedPC preparedRunning (by omega)
      (by simpa only [preparedHeap] using invariant.room)
  refine ⟨final, ?_, pc, live, ?_, stack.trans preparedStack, output.trans preparedOutput,
    empty_positive_conflict clauses selected labels original empty⟩
  · simpa only [preparedLive, Nat.max_self, Nat.reduceAdd] using prepareTrace.append positiveTrace
  · simpa only [preparedHeap] using size

/-- Every original row takes one of the fetched scan paths, with queue growth
charged only when a fresh original negative head is marked. -/
theorem row_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length) (separated : base + 5 * n + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ nextQueue nextFired final ticks,
      queue.length ≤ nextQueue.length ∧ nextQueue.length ≤ n ∧ ticks ≤ 36 + 3 * (nextQueue.length - queue.length) ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      ((final.pc = word width conflict ∧ final.halted = false ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
        ScanInvariant clauses recordStart recordEnd base entry (index + 1) nextQueue nextFired final) := by
  by_cases positive : 0 < (Controller.Horn.Worklist.compileClause clauses[index]).positives.length
  · obtain ⟨final, trace, result, size, stack, output⟩ :=
      nonzero_row_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
        invariant nonempty positive present capacity
    exact ⟨queue, fired, final, 13, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, Or.inr result⟩
  · have zeroCount : (Controller.Horn.Worklist.compileClause clauses[index]).positives.length = 0 := by omega
    cases original : Controller.Horn.Worklist.compileClause clauses[index] with
    | skip =>
      obtain ⟨final, trace, result, size, stack, output⟩ :=
        skip_row_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
          invariant nonempty original present capacity
      exact ⟨queue, fired, final, 16, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, Or.inr result⟩
    | positive labels =>
      have empty : labels.length = 0 := by simpa only [original, Controller.Horn.Worklist.Rule.positives] using zeroCount
      obtain ⟨final, trace, pc, live, size, stack, output, impossible⟩ :=
        positive_row_execution clauses recordStart recordEnd base entry done conflict index queue fired labels state program
          invariant nonempty original empty present capacity
      exact ⟨queue, fired, final, 17, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, Or.inl ⟨pc, live, impossible⟩⟩
    | negative head labels =>
      have empty : labels.length = 0 := by simpa only [original, Controller.Horn.Worklist.Rule.positives] using zeroCount
      obtain ⟨final, trace, result, size, stack, output⟩ :=
        negative_row_execution clauses recordStart recordEnd base entry done conflict index queue fired head labels state program
          invariant nonempty original empty separated present capacity
      refine ⟨queueAfter queue head,
        (fun other => if other = (⟨index, nonempty⟩ : Fin clauses.length) then true else fired other),
        final, (if head ∈ queue then 36 else 39), ?_, enqueue_bound _ result.fifo.nodup, ?_, trace, size, stack, output, Or.inr result⟩
      · by_cases stale : head ∈ queue <;> simp [queueAfter, stale]
      · by_cases stale : head ∈ queue <;> simp [queueAfter, stale]

/-- The final cursor equality is tested by four fetched instructions, including
when the source formula has no rows. -/
theorem terminal_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry clauses.length queue fired state)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base done clauses.length queue fired final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  have headerBound : Controller.Horn.WorklistFIFO.headSlot (n := n) base < state.heap.size := by
    have fits := invariant.fifo.fits
    unfold Controller.Horn.WorklistFIFO.headSlot
    omega
  have headerCell : state.heap[Controller.Horn.WorklistFIFO.headSlot (n := n) base]'headerBound = word width recordEnd := by
    simpa only [Array.getElem?_eq_getElem headerBound, Option.some.injEq] using invariant.header
  have endFits : recordEnd < 2 ^ width := by
    have endpoint := invariant.spine.endpoint
    have room := invariant.room
    omega
  have held : state.reg 1 = word width recordEnd := by
    simpa only [← invariant.spine.originalEnd] using invariant.held
  let final := Controller.Horn.IndexScan.testFinished state
    (Controller.Horn.WorklistFIFO.headSlot (n := n) base) recordEnd recordEnd done
  have trace := Controller.Horn.IndexScan.test_execution program entry
    (Controller.Horn.WorklistFIFO.headSlot (n := n) base) recordEnd recordEnd done 1 state
    (Controller.Horn.WorklistSeed.test_at program base entry done conflict present)
    invariant.position invariant.running headerBound headerCell held (by decide) (by decide)
    (by omega) (by have room := invariant.room; omega) endFits endFits
  have frame := row_test_frame state (Controller.Horn.WorklistFIFO.headSlot (n := n) base) recordEnd recordEnd done
  have finalHeap : final.heap = state.heap := frame.1
  refine ⟨final, trace, ?_, congrArg Array.size frame.1, frame.2.1, frame.2.2.1⟩
  refine ⟨invariant.indexBound, ?_, ?_, ?_, invariant.unvisited, invariant.complete, invariant.forced,
    invariant.firedEmpty, invariant.firedHead, ?_, ?_,
    (frame.2.2.2.2.2 1 (by decide) (by decide)).trans invariant.held,
    (frame.2.2.2.2.2 2 (by decide) (by decide)).trans invariant.zero,
    (frame.2.2.2.2.2 5 (by decide) (by decide)).trans invariant.one,
    (frame.2.2.2.2.2 6 (by decide) (by decide)).trans invariant.decrement,
    ?_, frame.2.2.2.1.trans invariant.running, ?_⟩
  · simpa only [finalHeap] using invariant.spine
  · simpa only [finalHeap] using invariant.fifo
  · intro other; simpa only [finalHeap] using invariant.rows other
  · simpa only [finalHeap] using invariant.header
  · simpa only [finalHeap] using invariant.tail
  · simpa only [ite_true] using Controller.Horn.IndexScan.test_position state entry
      (Controller.Horn.WorklistFIFO.headSlot (n := n) base) recordEnd recordEnd done
      invariant.position (by omega) endFits endFits
  · simpa only [finalHeap] using invariant.room

/-- The seed scan follows every original record once. Its recursion uses the
source row count, its successor is derived from actual fetched branches, and
its queue-growth charge telescopes across fresh marks. -/
theorem scan_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict : Nat) (program : Program width 8)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (separated : base + 5 * n + 4 ≤ recordStart) (capacity : entry + 47 < 2 ^ width)
    (budget : Nat) :
    ∀ (index : Nat) (queue : List (Fin n)) (fired : Fin clauses.length → Bool) (state : State width 8),
      index + budget = clauses.length →
      ScanInvariant clauses recordStart recordEnd base entry index queue fired state →
      ∃ nextQueue nextFired final ticks,
        queue.length ≤ nextQueue.length ∧ nextQueue.length ≤ n ∧ ticks ≤ 36 * budget + 3 * (nextQueue.length - queue.length) + 4 ∧
        Execution program state final ticks state.liveWords ∧
        final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
        ((final.pc = word width conflict ∧ final.halted = false ∧
          ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
            (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
          ScanInvariant clauses recordStart recordEnd base done clauses.length nextQueue nextFired final) := by
  induction budget with
  | zero =>
    intro index queue fired state ledger invariant
    have last : index = clauses.length := by omega
    subst index
    obtain ⟨final, trace, result, size, stack, output⟩ := terminal_execution clauses recordStart recordEnd base
      entry done conflict queue fired state program invariant present capacity
    exact ⟨queue, fired, final, 4, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, Or.inr result⟩
  | succ budget ih =>
    intro index queue fired state ledger invariant
    obtain ⟨middleQueue, middleFired, middle, stepTicks, growth, middleBound, stepCost, stepTrace, size, stack, output, outcome⟩ :=
      row_execution clauses recordStart recordEnd base entry done conflict index queue fired state program invariant
        (by omega) separated present capacity
    rcases outcome with conflictResult | continuing
    · refine ⟨middleQueue, middleFired, middle, stepTicks, growth, middleBound, ?_, stepTrace, size, stack, output, Or.inl conflictResult⟩
      omega
    · obtain ⟨finalQueue, finalFired, final, restTicks, restGrowth, finalBound, restCost, restTrace,
          finalSize, finalStack, finalOutput, result⟩ :=
        ih (index + 1) middleQueue middleFired middle (by omega) continuing
      have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [size, stack, output]
      refine ⟨finalQueue, finalFired, final, stepTicks + restTicks, Nat.le_trans growth restGrowth, finalBound,
        ?_, ?_, finalSize.trans size, finalStack.trans stack, finalOutput.trans output, result⟩
      · omega
      · simpa only [middleLive, Nat.max_self] using stepTrace.append restTrace

/-- Both seed scratch-header stores preserve every original row, physical
bucket head and node, and the existing FIFO storage. -/
theorem scratch_header_frame (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base position : Nat) (heap : Array (Word width))
    (queue : List (Fin n)) (counts : Fin clauses.length → Nat) (fired : Fin clauses.length → Bool)
    (spine : Controller.Horn.WorklistPropagation.Spine clauses recordStart recordEnd base heap)
    (fifo : Stored queue base heap)
    (rows : ∀ row : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[row.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart row.val) (counts row) (fired row) heap)
    (bound : position < heap.size) (aboveHeads : base + 2 * n ≤ position)
    (belowRows : position < recordStart) (belowQueue : position < queueStart (n := n) base)
    (value : Word width) :
    Controller.Horn.WorklistPropagation.Spine clauses recordStart recordEnd base (heap.set position value bound) ∧
      Stored queue base (heap.set position value bound) ∧
      ∀ row : Fin clauses.length,
        Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[row.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart row.val)
          (counts row) (fired row) (heap.set position value bound) := by
  have startBelow : recordStart ≤ recordEnd := by
    rw [spine.originalEnd]
    exact Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart clauses.length
  refine ⟨Controller.Horn.WorklistBucketChain.spine_store clauses recordStart recordEnd base position heap
    spine bound aboveHeads (by omega) value,
    Controller.Horn.WorklistBucketChain.fifo_store queue base position heap fifo bound
      (Or.inl ⟨aboveHeads, belowQueue⟩) value, ?_⟩
  intro row
  apply Controller.Horn.WorklistBucketChain.mutable_store_outside
    (Controller.Horn.Worklist.compileClause clauses[row.val])
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart row.val) (counts row) position
    (fired row) heap (rows row) bound ?_ value
  left
  have lower := Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart row.val
  omega

/-- Nine actual fetched setup instructions copy the original endpoint header,
initialize the row cursor and decrement, and enter the seed scan with an empty
FIFO tail. All writes use preallocated scratch headers. -/
theorem cold_setup_execution (program : Program width 8)
    (base recordStart recordEnd entry scan : Nat) (state : State width 8)
    (present : ∀ phase : Fin 9, program[entry + phase.val]? =
      (coldSetupCode (n := n) width base recordStart scan)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0)
    (sourceBound : 0 < state.heap.size) (sourceValue : state.heap[0]'sourceBound = word width recordEnd)
    (headBound : Controller.Horn.WorklistFIFO.headSlot (n := n) base < state.heap.size)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 9 < 2 ^ width) :
    ∃ final, Execution program state final 9 state.liveWords ∧
      final.reg 1 = word width recordStart ∧ final.reg 2 = state.reg 2 ∧
      final.reg 5 = state.reg 5 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.heap = (state.heap.set (Controller.Horn.WorklistFIFO.headSlot (n := n) base)
        (word width recordEnd) headBound).set (tailSlot (n := n) base)
        (word width (queueStart (n := n) base)) (by simpa using tailBound) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width scan ∧ final.halted = false := by
  let first := state.advance.put 1 (word width recordStart)
  let second := first.advance.put 6 (word width (2 ^ width - 1))
  let third := second.advance.put 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := n) base))
  let fourth := third.advance.put 0 (word width recordEnd)
  let fifth : State width 8 := { fourth.advance with heap :=
    (state.heap.set (Controller.Horn.WorklistFIFO.headSlot (n := n) base) (word width recordEnd) headBound) }
  let sixth := fifth.advance.put 3 (word width (tailSlot (n := n) base))
  let seventh := sixth.advance.put 0 (word width (queueStart (n := n) base))
  let eighth : State width 8 := { seventh.advance with heap :=
    (fifth.heap.set (tailSlot (n := n) base) (word width (queueStart (n := n) base)) (by simpa [fifth] using tailBound)) }
  let final : State width 8 := { eighth.advance with pc := word width scan }
  have wordVal (value : Nat) (fits : value < 2 ^ width) : (word width value).val = value := Nat.mod_eq_of_lt fits
  have fetched (current : State width 8) (offset : Nat) (instruction : Instruction width 8)
      (pc : current.pc = word width (entry + offset)) (bound : entry + offset < 2 ^ width)
      (instructionAt : program[entry + offset]? = some instruction) :
      programStep program current = step instruction current := by
    unfold programStep
    rw [pc, wordVal (entry + offset) bound, instructionAt]
    rfl
  have nextPC (current : State width 8) (offset : Nat)
      (pc : current.pc = word width (entry + offset)) (bound : entry + offset < 2 ^ width) :
      current.advance.pc = word width (entry + offset + 1) := by
    simp only [State.advance, pc, wordVal (entry + offset) bound]
  have pc1 : first.pc = word width (entry + 1) := by simpa [first, State.put] using nextPC state 0 position (by omega)
  have pc2 : second.pc = word width (entry + 2) := by
    simpa [second, State.put, Nat.add_assoc] using nextPC first 1 pc1 (by omega)
  have pc3 : third.pc = word width (entry + 3) := by
    simpa [third, State.put, Nat.add_assoc] using nextPC second 2 pc2 (by omega)
  have pc4 : fourth.pc = word width (entry + 4) := by
    simpa [fourth, State.put, Nat.add_assoc] using nextPC third 3 pc3 (by omega)
  have pc5 : fifth.pc = word width (entry + 5) := by
    simpa [fifth, State.put, Nat.add_assoc] using nextPC fourth 4 pc4 (by omega)
  have pc6 : sixth.pc = word width (entry + 6) := by
    simpa [sixth, State.put, Nat.add_assoc] using nextPC fifth 5 pc5 (by omega)
  have pc7 : seventh.pc = word width (entry + 7) := by
    simpa [seventh, State.put, Nat.add_assoc] using nextPC sixth 6 pc6 (by omega)
  have pc8 : eighth.pc = word width (entry + 8) := by
    simpa [eighth, State.put, Nat.add_assoc] using nextPC seventh 7 pc7 (by omega)
  have step1 : programStep program state = some first := by
    rw [fetched state 0 (.constant 1 (word width recordStart)) position (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨0, by decide⟩)]
    simp [step, first, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound]
  have step2 : programStep program first = some second := by
    rw [fetched first 1 (.constant 6 (word width (2 ^ width - 1))) pc1 (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨1, by decide⟩)]
    simp [step, first, second, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound]
  have step3 : programStep program second = some third := by
    rw [fetched second 2 (.constant 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := n) base))) pc2 (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨2, by decide⟩)]
    simp [step, first, second, third, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound]
  have step4 : programStep program third = some fourth := by
    rw [fetched third 3 (.load 0 2) pc3 (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨3, by decide⟩)]
    simp [step, first, second, third, fourth, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound]
  have step5 : programStep program fourth = some fifth := by
    rw [fetched fourth 4 (.store 3 0) pc4 (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨4, by decide⟩)]
    have addressFits : Controller.Horn.WorklistFIFO.headSlot (n := n) base < 2 ^ width := by omega
    simp [step, first, second, third, fourth, fifth, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt addressFits]
  have step6 : programStep program fifth = some sixth := by
    rw [fetched fifth 5 (.constant 3 (word width (tailSlot (n := n) base))) pc5 (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨5, by decide⟩)]
    simp [step, first, second, third, fourth, fifth, sixth, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound]
  have step7 : programStep program sixth = some seventh := by
    rw [fetched sixth 6 (.constant 0 (word width (queueStart (n := n) base))) pc6 (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨6, by decide⟩)]
    simp [step, first, second, third, fourth, fifth, sixth, seventh, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound]
  have step8 : programStep program seventh = some eighth := by
    rw [fetched seventh 7 (.store 3 0) pc7 (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨7, by decide⟩)]
    have addressFits : tailSlot (n := n) base < 2 ^ width := by omega
    simp [step, first, second, third, fourth, fifth, sixth, seventh, eighth, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound, Nat.mod_eq_of_lt addressFits]
  have step9 : programStep program eighth = some final := by
    rw [fetched eighth 8 (.branchZero 2 (word width scan)) pc8 (by omega)
      (by simpa [coldSetupCode, setupCode] using present ⟨8, by decide⟩)]
    simp [step, first, second, third, fourth, fifth, sixth, seventh, eighth, final, State.put, State.advance, running, zero, word, sourceBound, sourceValue, headBound, tailBound]
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, running⟩
  · simpa [first, second, third, fourth, fifth, sixth, seventh, eighth, final,
      State.put, State.advance, State.liveWords] using
      Execution.cons step1 (Execution.cons step2 (Execution.cons step3 (Execution.cons step4 (Execution.cons step5 (Execution.cons step6 (Execution.cons step7 (Execution.cons step8 (Execution.cons step9 (Execution.refl final)))))))))
  all_goals simp [first, second, third, fourth, fifth, sixth, seventh, eighth, final, State.put, State.advance]

/-- The actual cold setup creates the initial full scan invariant from the
original completed physical index, original global endpoint header, and actual
empty off/FIFO storage. No normalized rows or links are recreated. -/
theorem initial_scan_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry scan : Nat) (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex clauses recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences clauses recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd 0 state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : ∀ phase : Fin 9, program[entry + phase.val]? =
      (coldSetupCode (n := n) width base recordStart scan)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (capacity : entry + 9 < 2 ^ width) :
    ∃ final, Execution program state final 9 state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base scan 0 [] (fun _ => false) final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  have headBound : Controller.Horn.WorklistFIFO.headSlot (n := n) base < state.heap.size := by
    have fits := fifo.fits
    unfold Controller.Horn.WorklistFIFO.headSlot
    omega
  have tailBound : tailSlot (n := n) base < state.heap.size := by have fits := fifo.fits; unfold tailSlot; omega
  have spine := Controller.Horn.WorklistPropagation.spine_of_index clauses recordStart recordEnd base state.heap physical
  have rows : ∀ row : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[row.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart row.val)
        (Controller.Horn.Worklist.compileClause clauses[row.val]).positives.length false state.heap := by
    intro row
    exact Controller.Horn.WorklistStorage.initial (physical.records row)
  obtain ⟨final, trace, cursor, finalZero, finalOne, decrement, heap, size, stack, output, pc, live⟩ :=
    cold_setup_execution program base recordStart recordEnd entry scan state present position running zero
      header.bound header.value headBound tailBound room capacity
  let firstHeap := state.heap.set (Controller.Horn.WorklistFIFO.headSlot (n := n) base) (word width recordEnd) headBound
  have firstFrame := scratch_header_frame clauses recordStart recordEnd base
    (Controller.Horn.WorklistFIFO.headSlot (n := n) base) state.heap []
    (fun row => (Controller.Horn.Worklist.compileClause clauses[row.val]).positives.length) (fun _ => false)
    spine fifo rows headBound (by unfold Controller.Horn.WorklistFIFO.headSlot; omega)
    (by unfold Controller.Horn.WorklistFIFO.headSlot; omega)
    (by unfold Controller.Horn.WorklistFIFO.headSlot queueStart; omega) (word width recordEnd)
  have secondFrame := scratch_header_frame clauses recordStart recordEnd base (tailSlot (n := n) base)
    firstHeap [] (fun row => (Controller.Horn.Worklist.compileClause clauses[row.val]).positives.length) (fun _ => false)
    firstFrame.1 firstFrame.2.1 firstFrame.2.2 (by simpa [firstHeap] using tailBound)
    (by unfold tailSlot; omega) (by unfold tailSlot; omega) (by unfold tailSlot queueStart; omega)
    (word width (queueStart (n := n) base))
  have headerValue : final.heap[Controller.Horn.WorklistFIFO.headSlot (n := n) base]? = some (word width recordEnd) := by
    rw [heap]
    rw [Array.getElem?_set_ne (by simpa using tailBound)
      (by unfold tailSlot Controller.Horn.WorklistFIFO.headSlot; omega)]
    exact Array.getElem?_set_self headBound
  have tailValue : final.heap[tailSlot (n := n) base]? = some (word width (queueStart (n := n) base)) := by
    rw [heap]
    exact Array.getElem?_set_self (by simpa using tailBound)
  refine ⟨final, trace, ?_, size, stack, output⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, headerValue, ?_, ?_,
    finalZero.trans zero, finalOne.trans one, decrement, pc, live, by omega⟩
  · simpa only [heap, firstHeap] using secondFrame.1
  · simpa only [heap, firstHeap] using secondFrame.2.1
  · intro row; simpa only [heap, firstHeap] using secondFrame.2.2 row
  · intro row bound; rfl
  · intro row before; omega
  · intro assignment models label member; exact False.elim (List.not_mem_nil member)
  · intro row marked; exact False.elim (Bool.false_ne_true marked)
  · intro row marked; exact False.elim (Bool.false_ne_true marked)
  · simpa only [List.length_nil, Nat.add_zero] using tailValue
  · simpa [Controller.Horn.NormalizeLoop.recordOffset] using cursor

/-- Normalization, physical index construction and the seed scanner are one
appended program. Its end is the actual continuation entry for FIFO setup. -/
def program (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) (conflict : Nat) : Program width 8 :=
  Controller.Horn.IndexScanCold.program width clauses ++
    coldSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses)
      (Controller.Horn.IndexScanCold.recordStart width clauses)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 9) ++
    Controller.Horn.WorklistSeed.code (n := n) width (Controller.Horn.SourceSerialize.base clauses)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 9)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 56) conflict

@[simp] theorem program_size (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) (conflict : Nat) :
    (program width clauses conflict).size = (Controller.Horn.IndexScanCold.program width clauses).size + 56 := by
  simp [program, Nat.add_assoc]

theorem setup_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) (conflict : Nat) :
    ∀ phase : Fin 9,
      (program width clauses conflict)[(Controller.Horn.IndexScanCold.program width clauses).size + phase.val]? =
        (coldSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses)
          (Controller.Horn.IndexScanCold.recordStart width clauses)
          ((Controller.Horn.IndexScanCold.program width clauses).size + 9))[phase.val]? := by
  intro phase
  unfold program
  rw [Array.getElem?_append_left (by simp only [Array.size_append, cold_setup_size]; have := phase.isLt; omega)]
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem scan_at (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) (conflict : Nat) :
    Controller.Horn.WorklistSeed.At (n := n) (program width clauses conflict)
      (Controller.Horn.SourceSerialize.base clauses)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 9)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 56) conflict := by
  intro phase
  unfold program
  rw [Array.getElem?_append_right (by simp only [Array.size_append, cold_setup_size]; omega)]
  simp only [Array.size_append, cold_setup_size, Nat.add_sub_cancel_left]

/-- The complete cold seed endpoint, including exact original-row semantics
and the combined fetched trace resource bounds. -/
def ColdSeedResult (clauses : List (Controller.CNF.Clause (Fin n))) (conflict : Nat)
    (state : State width 8) (suffix : List (Word width)) (recordEnd : Nat)
    (queue : List (Fin n)) (fired : Fin clauses.length → Bool)
    (final : State width 8) (ticks peak : Nat) : Prop :=
      Execution (program width clauses conflict) state final ticks peak ∧
      final.stack = suffix ∧ final.output = state.output ∧ queue.length ≤ n ∧
      ticks ≤ 28 * n + 83 * (clauses.map List.length).sum + 131 * clauses.length + 79 ∧
      peak ≤ state.liveWords + 5 * n + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      programWords (program width clauses conflict) + peak ≤
        4 * (Controller.Horn.IndexScanCold.entry width clauses + 88) +
          state.liveWords + 5 * n + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      ((final.pc = word width conflict ∧ final.halted = false ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
        ScanInvariant clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
          (Controller.Horn.SourceSerialize.base clauses) (program width clauses conflict).size
          clauses.length queue fired final)

/-- Original serialized input executes normalization, physical indexing, actual
nine-tick seed setup and the complete one-pass seed scan. The pending queue and
all semantic seed facts come from these traces. -/
theorem cold_seed_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (conflict : Nat) (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (codeFits : (program width clauses conflict).size < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ (recordEnd : Nat) (queue : List (Fin n)) (fired : Fin clauses.length → Bool)
      (final : State width 8) (ticks peak : Nat),
      ColdSeedResult clauses conflict state suffix recordEnd queue fired final ticks peak := by
  obtain ⟨indexed, recordEnd, coldTicks, coldPeak, coldTrace, physical, header, fifo, indexedPC,
      indexedRunning, indexedZero, indexedOne, indexedRoom, indexedStack, indexedOutput, coldCost, coldStorage⟩ :=
    cold_seed_input clauses state suffix emptyHeap input position running dual
      (by have size := program_size width clauses conflict; omega) heapFits
  have separated : Controller.Horn.SourceSerialize.base clauses + 5 * n + 4 ≤
      Controller.Horn.IndexScanCold.recordStart width clauses := by
    simp [Controller.Horn.IndexScanCold.recordStart, Controller.Horn.NormalizeCold.words]
  have appendedCold : Execution (program width clauses conflict) state indexed coldTicks coldPeak := by
    have appended := Controller.Horn.IndexScanCold.append_execution
      (Controller.Horn.IndexScanCold.program width clauses)
      (coldSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses)
        (Controller.Horn.IndexScanCold.recordStart width clauses)
        ((Controller.Horn.IndexScanCold.program width clauses).size + 9) ++
       Controller.Horn.WorklistSeed.code (n := n) width (Controller.Horn.SourceSerialize.base clauses)
        ((Controller.Horn.IndexScanCold.program width clauses).size + 9)
        ((Controller.Horn.IndexScanCold.program width clauses).size + 56) conflict) coldTrace
    simpa only [program, Array.append_assoc] using appended
  obtain ⟨started, setupTrace, initial, setupSize, setupStack, setupOutput⟩ :=
    initial_scan_execution clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses) (Controller.Horn.IndexScanCold.program width clauses).size
      ((Controller.Horn.IndexScanCold.program width clauses).size + 9) indexed (program width clauses conflict)
      physical header fifo separated (setup_at width clauses conflict) indexedPC indexedRunning
      indexedZero indexedOne indexedRoom (by have size := program_size width clauses conflict; omega)
  obtain ⟨queue, fired, final, seedTicks, _, queueBound, seedCost, seedTrace, _, seedStack, seedOutput, result⟩ :=
    scan_execution clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 9)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 56) conflict
      (program width clauses conflict) (scan_at width clauses conflict) separated
      (by have size := program_size width clauses conflict; omega) clauses.length 0 [] (fun _ => false) started (by omega) initial
  have startedLive : started.liveWords = indexed.liveWords := by unfold State.liveWords; rw [setupSize, setupStack, setupOutput]
  have indexedStorage := coldTrace.final_storage_le
  let full := (appendedCold.append setupTrace).append seedTrace
  refine ⟨recordEnd, queue, fired, final, coldTicks + 9 + seedTicks,
    max (max coldPeak indexed.liveWords) started.liveWords, full,
    seedStack.trans (setupStack.trans indexedStack), seedOutput.trans (setupOutput.trans indexedOutput),
    queueBound, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_nil, Nat.sub_zero] at seedCost
    omega
  · rw [startedLive]
    omega
  · unfold programWords
    rw [program_size, Controller.Horn.IndexScanCold.program_size, startedLive]
    omega
  · rcases result with conflictResult | complete
    · exact Or.inl conflictResult
    · right
      simpa only [program_size] using complete

end Controller.Horn.WorklistSeedRun
