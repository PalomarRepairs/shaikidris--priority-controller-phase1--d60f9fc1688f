module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistSeedRun
public import Controller.Cost.ForestZeroBackendFrame

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Actual seed-row execution preserves the caller source prefix. -/
namespace Controller.Cost.ForestZeroSeedFrame
open Controller.Cost Controller.Horn.WorklistSeed Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketReady Controller.Horn.WorklistSeedRun
open Controller.Cost.ForestZeroBackendFrame
variable {width n : Nat}

theorem nonzero_row_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (positive : 0 < (Controller.Horn.Worklist.compileClause clauses[index]).positives.length)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size) :
    ∃ final, Execution program state final 13 state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base entry (index + 1) queue fired final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
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
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    rw [allHeap]
    exact Controller.Cost.ForestZeroBackendFrame.refl state.heap prefixBound
  refine ⟨final, ?_, ?_, congrArg Array.size allHeap, finalStack.trans stack, finalOutput.trans output, retained⟩
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


theorem negative_ready_prefix (prefixSize : Nat) (program : Program width 8)
    (base entry skip conflict continuation row next : Nat) (queue : List (Fin n))
    (head : Fin n) (labels : List (Fin n)) (state final : State width 8)
    (stored : Controller.Horn.WorklistStorage.MutableStored (.negative head labels) row 0 false state.heap)
    (present : Controller.Horn.WorklistBucketReady.At (n := n) program base entry skip conflict continuation)
    (fifo : Stored queue base state.heap) (separated : base + 5 * n + 4 ≤ row)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[tailSlot (n := n) base]'tailBound = word width (queueStart (n := n) base + queue.length))
    (rowHeld : state.reg 1 = word width row) (nextHeld : state.reg 4 = word width next)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (actual : Execution program state final (if head ∈ queue then 22 else 25) state.liveWords)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨same, trace, _, _, _, size, _, _, _, _, _, _, _, writes, _⟩ :=
    Controller.Horn.WorklistBucketNegative.negative_tail_framed program base entry skip conflict continuation
      row next queue head labels state present fifo stored separated tailBound tailValue rowHeld nextHeld
      one zero decrement position running capacity room
  have endpoint := Controller.Horn.JoinedRuleFrame.execution_endpoint_unique actual trace
  rw [endpoint]
  refine ⟨prefixBound, ?_, ?_⟩
  · rw [size]; exact prefixBound
  · intro pos bound
    apply writes
    · omega
    · unfold nextSlot; omega
    · unfold tailSlot; omega
    · have headBound := head.isLt
      unfold Controller.Horn.WorklistStorage.offAddress
      omega
    · unfold queueStart
      omega

theorem negative_row_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (head : Fin n) (labels : List (Fin n))
    (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (original : Controller.Horn.Worklist.compileClause clauses[index] = .negative head labels)
    (empty : labels.length = 0)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ final, Execution program state final (if head ∈ queue then 36 else 39) state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base entry (index + 1) (queueAfter queue head)
        (fun other => if other = (⟨index, nonempty⟩ : Fin clauses.length) then true else fired other) final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      PrefixFrame prefixSize state.heap final.heap := by
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
  have readyPrefix := negative_ready_prefix prefixSize program base (entry + 17) (entry + 45) conflict (entry + 43)
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index)
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart (index + 1)) queue head labels prepared ready
    preparedStored readyAt preparedFifo rowSeparation tailBound tailCell (preparedRow.trans invariant.held)
    preparedNext preparedOne preparedZero preparedDecrement preparedPC preparedRunning (by omega) preparedRoom readyTrace
    (by simpa only [preparedHeap] using prefixBound) prefixBelow
  have finalPrefix : PrefixFrame prefixSize state.heap final.heap := by
    simpa only [finalHeap, preparedHeap] using readyPrefix
  have readyLive : ready.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [readySize, readyStack, readyOutput, preparedHeap, preparedStack, preparedOutput]
  have finalSize : final.heap.size = state.heap.size := by rw [finalHeap, readySize, preparedHeap]
  have stateRoom := invariant.room
  have headQueued : head ∈ queueAfter queue head := by
    by_cases stale : head ∈ queue <;> simp [queueAfter, stale]
  refine ⟨final, ?_, ?_, finalSize, finalStack.trans (readyStack.trans preparedStack),
    finalOutput.trans (readyOutput.trans preparedOutput), finalPrefix⟩
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

theorem skip_row_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (original : Controller.Horn.Worklist.compileClause clauses[index] = .skip)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size) :
    ∃ final, Execution program state final 16 state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base entry (index + 1) queue fired final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
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
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    rw [allHeap]
    exact Controller.Cost.ForestZeroBackendFrame.refl state.heap prefixBound
  refine ⟨final, ?_, ?_, congrArg Array.size allHeap,
    finalStack.trans (skippedStack.trans preparedStack), finalOutput.trans (skippedOutput.trans preparedOutput), retained⟩
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

theorem positive_row_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (labels : List (Fin n)) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length)
    (original : Controller.Horn.Worklist.compileClause clauses[index] = .positive labels)
    (empty : labels.length = 0)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBelow : prefixSize ≤ base) (separated : base + 5 * n + 4 ≤ recordStart) :
    ∃ final, Execution program state final 17 state.liveWords ∧
      final.pc = word width conflict ∧ final.halted = false ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      (¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
        (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∧
      PrefixFrame prefixSize state.heap final.heap := by
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
  obtain ⟨final, positiveTrace, _, _, _, _, _, _, finalHeap, size, stack, output, pc, live⟩ :=
    Controller.Horn.WorklistBucketCases.positive_execution program base (entry + 17) (entry + 45) conflict (entry + 43)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) labels prepared stored
      (Controller.Horn.WorklistSeed.ready_at program base entry done conflict present)
      (preparedRow.trans invariant.held) preparedZero preparedDecrement preparedPC preparedRunning (by omega)
      (by simpa only [preparedHeap] using invariant.room)
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    rw [finalHeap]
    have rowAbove := Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart index
    have frame := Controller.Cost.ForestZeroBackendFrame.store (prefixSize := prefixSize) prepared.heap
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index) (word width 0)
      (by have fits := stored.fits; omega) (by omega) (by simpa only [preparedHeap] using prefixBound)
    simpa only [preparedHeap] using frame
  refine ⟨final, ?_, pc, live, ?_, stack.trans preparedStack, output.trans preparedOutput,
    empty_positive_conflict clauses selected labels original empty, retained⟩
  · simpa only [preparedLive, Nat.max_self, Nat.reduceAdd] using prepareTrace.append positiveTrace
  · simpa only [preparedHeap] using size

theorem row_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length) (separated : base + 5 * n + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBelow : prefixSize ≤ base) :
    ∃ nextQueue nextFired final ticks,
      queue.length ≤ nextQueue.length ∧ nextQueue.length ≤ n ∧ ticks ≤ 36 + 3 * (nextQueue.length - queue.length) ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap ∧
      ((final.pc = word width conflict ∧ final.halted = false ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
        ScanInvariant clauses recordStart recordEnd base entry (index + 1) nextQueue nextFired final) := by
  by_cases positive : 0 < (Controller.Horn.Worklist.compileClause clauses[index]).positives.length
  · obtain ⟨final, trace, result, size, stack, output, frame⟩ :=
      nonzero_row_execution prefixSize clauses recordStart recordEnd base entry done conflict index queue fired state program
        invariant nonempty positive present capacity prefixBound
    exact ⟨queue, fired, final, 13, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, frame, Or.inr result⟩
  · have zeroCount : (Controller.Horn.Worklist.compileClause clauses[index]).positives.length = 0 := by omega
    cases original : Controller.Horn.Worklist.compileClause clauses[index] with
    | skip =>
      obtain ⟨final, trace, result, size, stack, output, frame⟩ :=
        skip_row_execution prefixSize clauses recordStart recordEnd base entry done conflict index queue fired state program
          invariant nonempty original present capacity prefixBound
      exact ⟨queue, fired, final, 16, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, frame, Or.inr result⟩
    | positive labels =>
      have empty : labels.length = 0 := by simpa only [original, Controller.Horn.Worklist.Rule.positives] using zeroCount
      obtain ⟨final, trace, pc, live, size, stack, output, impossible, frame⟩ :=
        positive_row_execution prefixSize clauses recordStart recordEnd base entry done conflict index queue fired labels state program
          invariant nonempty original empty present capacity prefixBound prefixBelow separated
      exact ⟨queue, fired, final, 17, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, frame, Or.inl ⟨pc, live, impossible⟩⟩
    | negative head labels =>
      have empty : labels.length = 0 := by simpa only [original, Controller.Horn.Worklist.Rule.positives] using zeroCount
      obtain ⟨final, trace, result, size, stack, output, frame⟩ :=
        negative_row_execution prefixSize clauses recordStart recordEnd base entry done conflict index queue fired head labels state program
          invariant nonempty original empty separated present capacity prefixBound prefixBelow
      refine ⟨queueAfter queue head,
        (fun other => if other = (⟨index, nonempty⟩ : Fin clauses.length) then true else fired other),
        final, (if head ∈ queue then 36 else 39), ?_, enqueue_bound _ result.fifo.nodup, ?_, trace, size, stack, output, frame, Or.inr result⟩
      · by_cases stale : head ∈ queue <;> simp [queueAfter, stale]
      · by_cases stale : head ∈ queue <;> simp [queueAfter, stale]

theorem terminal_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict : Nat) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry clauses.length queue fired state)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      ScanInvariant clauses recordStart recordEnd base done clauses.length queue fired final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
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
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    rw [finalHeap]
    exact Controller.Cost.ForestZeroBackendFrame.refl state.heap prefixBound
  refine ⟨final, trace, ?_, congrArg Array.size frame.1, frame.2.1, frame.2.2.1, retained⟩
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

theorem scan_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done conflict : Nat) (program : Program width 8)
    (present : Controller.Horn.WorklistSeed.At (n := n) program base entry done conflict)
    (separated : base + 5 * n + 4 ≤ recordStart) (capacity : entry + 47 < 2 ^ width)
    (budget : Nat) (prefixBelow : prefixSize ≤ base) :
    ∀ (index : Nat) (queue : List (Fin n)) (fired : Fin clauses.length → Bool) (state : State width 8),
      index + budget = clauses.length →
      ScanInvariant clauses recordStart recordEnd base entry index queue fired state →
      prefixSize ≤ state.heap.size →
      ∃ nextQueue nextFired final ticks,
        queue.length ≤ nextQueue.length ∧ nextQueue.length ≤ n ∧ ticks ≤ 36 * budget + 3 * (nextQueue.length - queue.length) + 4 ∧
        Execution program state final ticks state.liveWords ∧
        final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap ∧
        ((final.pc = word width conflict ∧ final.halted = false ∧
          ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
            (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
          ScanInvariant clauses recordStart recordEnd base done clauses.length nextQueue nextFired final) := by
  induction budget with
  | zero =>
    intro index queue fired state ledger invariant prefixBound
    have last : index = clauses.length := by omega
    subst index
    obtain ⟨final, trace, result, size, stack, output, frame⟩ := terminal_execution prefixSize clauses recordStart recordEnd base
      entry done conflict queue fired state program invariant present capacity prefixBound
    exact ⟨queue, fired, final, 4, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, frame, Or.inr result⟩
  | succ budget ih =>
    intro index queue fired state ledger invariant prefixBound
    obtain ⟨middleQueue, middleFired, middle, stepTicks, growth, middleBound, stepCost, stepTrace, size, stack, output, stepFrame, outcome⟩ :=
      row_execution prefixSize clauses recordStart recordEnd base entry done conflict index queue fired state program invariant
        (by omega) separated present capacity prefixBound prefixBelow
    rcases outcome with conflictResult | continuing
    · refine ⟨middleQueue, middleFired, middle, stepTicks, growth, middleBound, ?_, stepTrace, size, stack, output, stepFrame, Or.inl conflictResult⟩
      omega
    · obtain ⟨finalQueue, finalFired, final, restTicks, restGrowth, finalBound, restCost, restTrace,
          finalSize, finalStack, finalOutput, restFrame, result⟩ :=
        ih (index + 1) middleQueue middleFired middle (by omega) continuing (by simpa only [size] using prefixBound)
      have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [size, stack, output]
      refine ⟨finalQueue, finalFired, final, stepTicks + restTicks, Nat.le_trans growth restGrowth, finalBound,
        ?_, ?_, finalSize.trans size, finalStack.trans stack, finalOutput.trans output, Controller.Cost.ForestZeroBackendFrame.trans stepFrame restFrame, result⟩
      · omega
      · simpa only [middleLive, Nat.max_self] using stepTrace.append restTrace

end Controller.Cost.ForestZeroSeedFrame
