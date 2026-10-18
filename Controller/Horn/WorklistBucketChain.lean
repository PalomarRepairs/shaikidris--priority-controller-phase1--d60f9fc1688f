module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucketCases

@[expose] public section

/-! Linked-bucket transitions retain the original source records and incidence
spine. The FIFO includes pending marks while count changes charge only visited
original incidences. -/
namespace Controller.Horn.WorklistBucketChain
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.WorklistPropagation
variable {width n : Nat}

theorem fifo_frame (queue : List (Fin n)) (base : Nat) (before after : Array (Word width))
    (stored : Controller.Horn.WorklistMark.Stored queue base before) (size : after.size = before.size)
    (frame : ∀ pos, pos < base + 2 * n ∨
      (queueStart (n := n) base ≤ pos ∧ pos < base + 4 * n + 4) → after[pos]? = before[pos]?) :
    Controller.Horn.WorklistMark.Stored queue base after := by
  have cell (pos : Nat) (inside : pos < before.size) (coverage : pos < base + 2 * n ∨
      (queueStart (n := n) base ≤ pos ∧ pos < base + 4 * n + 4)) :
      after[pos]'(by omega) = before[pos]'inside := by
    have equal := frame pos coverage
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem inside] at equal
    exact Option.some.inj equal
  refine ⟨stored.nodup, by rw [size]; exact stored.fits, ?_, ?_⟩
  · intro label
    have inside : offAddress base label < before.size := by have := stored.fits; have := label.isLt; unfold offAddress; omega
    exact (cell _ inside (Or.inl (by have := label.isLt; unfold offAddress; omega))).trans (stored.flags label)
  · refine ⟨by rw [size]; exact stored.queue.fits, ?_⟩
    intro index
    have length := enqueue_bound queue stored.nodup
    have inside : queueStart (n := n) base + index.val < before.size := by have := stored.queue.fits; have := index.isLt; omega
    exact (cell _ inside (Or.inr ⟨by omega, by have := index.isLt; unfold queueStart; omega⟩)).trans (stored.queue.entry index)

theorem fifo_store (queue : List (Fin n)) (base index : Nat) (heap : Array (Word width))
    (stored : Controller.Horn.WorklistMark.Stored queue base heap) (bound : index < heap.size)
    (outside : (base + 2 * n ≤ index ∧ index < queueStart (n := n) base) ∨ base + 4 * n + 4 ≤ index)
    (value : Word width) : Controller.Horn.WorklistMark.Stored queue base (heap.set index value bound) := by
  apply fifo_frame queue base heap _ stored (by simp)
  intro pos coverage
  have different : index ≠ pos := by rcases outside with low | high <;> rcases coverage with flags | queue <;> omega
  exact Array.getElem?_set_ne bound different

/-- The complete negative iteration includes the nonnil test, original count
store, ready branch, fired tag, original head read and physical FIFO operation. -/
theorem negative_iteration (program : Program width 8)
    (entry exit ready base skip conflict row next node : Nat)
    (queue : List (Fin n)) (head : Fin n) (labels : List (Fin n)) (state : State width 8)
    (linked : NodeStored row next node state.heap)
    (stored : MutableStored (.negative head labels) row 1 false state.heap)
    (fifo : Stored queue base state.heap)
    (separated : base + 5 * n + 4 ≤ row)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (tailBound : Controller.Horn.WorklistBucketReady.tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]'tailBound =
      word width (queueStart (n := n) base + queue.length))
    (positiveNode : 0 < node) (held : state.reg 0 = word width node)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final (if head ∈ queue then 32 else 35) state.liveWords ∧
      Stored (Controller.Horn.WorklistBucketReady.queueAfter queue head) base final.heap ∧
      MutableStored (.negative head labels) row 0 true final.heap ∧
      final.reg 0 = word width next ∧ final.heap.size = state.heap.size ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false := by
  obtain ⟨middle, first, result, heap, rowHeld, nextHeld, count, middleZero, middleOne, middleDecrement,
      size, stack, output, pc, live⟩ := Controller.Horn.WorklistBucketCases.bucket_visit_execution
        program entry exit ready row next node 0 (.negative head labels) false state linked stored loopAt
        positiveNode held one zero decrement position running capacity room
  have countBound : row + 2 < state.heap.size := by have := stored.fits; omega
  have middleFifo : Stored queue base middle.heap := by
    rw [heap]
    exact fifo_store queue base (row + 2) state.heap fifo countBound (Or.inr (by omega)) (word width 0)
  have middleTailBound : Controller.Horn.WorklistBucketReady.tailSlot (n := n) base < middle.heap.size := by omega
  have middleTail : middle.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]'middleTailBound =
      word width (queueStart (n := n) base + queue.length) := by
    simpa only [heap] using
      (Array.getElem_set_ne countBound tailBound (by unfold Controller.Horn.WorklistBucketReady.tailSlot; omega)).trans tailValue
  let dispatched := Controller.Horn.RuleDispatch.branchFinished middle 7 ready
  have branch := Controller.Horn.RuleDispatch.branch_execution program (entry + 9) ready 7
    (by simpa [Controller.Horn.WorklistBucketLoop.code] using loopAt ⟨9, by decide⟩) middle pc live (by omega)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame middle 7 ready
  have dispatchHeap : dispatched.heap = middle.heap := frame.2.1
  have dispatchPC : dispatched.pc = word width ready := by
    simp [dispatched, Controller.Horn.RuleDispatch.branchFinished, count, word]
  have dispatchLive : dispatched.liveWords = middle.liveWords := frame.2.2.2.2.2
  obtain ⟨final, last, finalFifo, finalStored, nextFinal, finalSize, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    Controller.Horn.WorklistBucketReady.negative_execution program base ready skip conflict entry row next queue head labels
      dispatched readyAt (by simpa only [dispatchHeap] using middleFifo)
      (by simpa only [dispatchHeap] using result) separated
      (by simpa only [dispatchHeap] using middleTailBound)
      (by simpa only [dispatchHeap] using middleTail)
      ((congrFun frame.1 1).trans rowHeld) ((congrFun frame.1 4).trans nextHeld)
      ((congrFun frame.1 5).trans middleOne) ((congrFun frame.1 2).trans middleZero)
      ((congrFun frame.1 6).trans middleDecrement) dispatchPC (frame.2.2.2.2.1.trans live)
      readyCapacity (by simpa only [dispatchHeap, size] using room)
  have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [size, stack, output]
  refine ⟨final, ?_, finalFifo, finalStored, nextFinal,
    finalSize.trans ((congrArg Array.size dispatchHeap).trans size),
    finalStack.trans (frame.2.2.1.trans stack), finalOutput.trans (frame.2.2.2.1.trans output), finalPC, finalRunning⟩
  · have trace := first.append (branch.append last)
    by_cases stale : head ∈ queue
    · simpa only [ite_eq_left stale, dispatchLive, middleLive, Nat.max_self, Nat.reduceAdd] using trace
    · simpa only [ite_eq_right stale, dispatchLive, middleLive, Nat.max_self, Nat.reduceAdd] using trace


/-- A store between the scratch heads and original record end preserves every
original predecessor link, endpoint and physical bucket head. -/
theorem spine_store (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base index : Nat) (heap : Array (Word width))
    (spine : Spine clauses recordStart recordEnd base heap)
    (bound : index < heap.size) (aboveHeads : base + 2 * n ≤ index)
    (belowNodes : index < recordEnd) (value : Word width) :
    Spine clauses recordStart recordEnd base (heap.set index value bound) := by
  refine ⟨by simpa using spine.endpoint, ?_, ?_, spine.originalEnd, spine.separation, spine.positiveEnd⟩
  · intro label
    have different : index ≠ headAddress base label := by
      have := label.isLt
      unfold headAddress
      omega
    exact (Array.getElem?_set_ne bound different).trans (spine.heads label)
  · intro nodeIndex
    have stored := spine.nodes nodeIndex
    have firstBound : recordEnd + 2 * nodeIndex.val < heap.size := by have := stored.fits; omega
    have secondBound : recordEnd + 2 * nodeIndex.val + 1 < heap.size := by have := stored.fits; omega
    refine ⟨by simpa using stored.fits, stored.rowFits, stored.previousFits, stored.offsetFits, ?_, ?_⟩
    · exact (Array.getElem_set_ne bound firstBound (by omega)).trans stored.row
    · exact (Array.getElem_set_ne bound secondBound (by omega)).trans stored.next

/-- The actual original row's count word lies before the fixed original end. -/
theorem original_count_store_spine (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (index : Fin clauses.length)
    (heap : Array (Word width)) (spine : Spine clauses recordStart recordEnd base heap)
    (bound : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2 < heap.size)
    (value : Word width) :
    Spine clauses recordStart recordEnd base
      (heap.set (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2) value bound) := by
  have lower := Controller.Horn.IndexScanWhole.recordOffset_mono clauses recordStart 0 index.val (by omega) (by have := index.isLt; omega)
  have upper := Controller.Horn.IndexScanWhole.recordOffset_mono clauses recordStart (index.val + 1) clauses.length
    (by have := index.isLt; omega) (by omega)
  rw [Controller.Horn.NormalizeLoop.recordOffset_succ clauses recordStart index.val index.isLt] at upper
  have startValue : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart 0 = recordStart := by
    simp [Controller.Horn.NormalizeLoop.recordOffset]
  rw [startValue] at lower
  apply spine_store clauses recordStart recordEnd base _ heap spine bound
  · have := spine.separation; omega
  · rw [spine.originalEnd]; omega

/-- A store outside one original record preserves all of its mutable and
immutable words, including its complete original positive body. -/
theorem mutable_store_outside (rule : Controller.Horn.Worklist.Rule (Fin n))
    (row count index : Nat) (fired : Bool) (heap : Array (Word width))
    (stored : MutableStored rule row count fired heap) (bound : index < heap.size)
    (outside : index < row ∨ row + 3 + rule.positives.length ≤ index) (value : Word width) :
    MutableStored rule row count fired (heap.set index value bound) := by
  have different (pos : Nat) (lower : row ≤ pos) (upper : pos < row + 3 + rule.positives.length) : index ≠ pos := by
    rcases outside with low | high <;> omega
  refine ⟨by simpa using stored.fits, stored.countFits, ?_, ?_, ?_, ?_⟩
  · exact (Array.getElem_set_ne bound (by have := stored.fits; omega) (different row (by omega) (by omega))).trans stored.tagValue
  · exact (Array.getElem_set_ne bound (by have := stored.fits; omega) (different (row + 1) (by omega) (by omega))).trans stored.headValue
  · exact (Array.getElem_set_ne bound (by have := stored.fits; omega) (different (row + 2) (by omega) (by omega))).trans stored.countValue
  · refine ⟨by simpa using stored.body.fits, ?_⟩
    intro labelIndex
    exact (Array.getElem_set_ne bound (by have := stored.body.fits; have := labelIndex.isLt; omega)
      (different (row + 3 + labelIndex.val) (by omega) (by have := labelIndex.isLt; omega))).trans (stored.body.entry labelIndex)


/-- The original packed layout proves disjointness of every other record from
the visited count store; no per-row memory-disjointness premise is supplied. -/
theorem count_store_rows (clauses : List (Controller.CNF.Clause (Fin n))) (recordStart : Nat)
    (counts : Fin clauses.length → Nat) (fired : Fin clauses.length → Bool)
    (index : Fin clauses.length) (newCount : Nat) (heap : Array (Word width))
    (rows : ∀ other : Fin clauses.length,
      MutableStored (Controller.Horn.Worklist.compileClause clauses[other.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val) (counts other) (fired other) heap)
    (fits : newCount < 2 ^ width) :
    ∀ other : Fin clauses.length,
      MutableStored (Controller.Horn.Worklist.compileClause clauses[other.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)
        (if other = index then newCount else counts other) (fired other)
        (heap.set (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2)
          (word width newCount) (by have := (rows index).fits; omega)) := by
  intro other
  by_cases equal : other = index
  · subst other
    simpa using store_count (rows index) fits
  · have different : index.val ≠ other.val := by
      intro values
      exact equal (Fin.ext values.symm)
    have outside : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2 <
        Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val ∨
      Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val + 3 +
        (Controller.Horn.Worklist.compileClause clauses[other.val]).positives.length ≤
          Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2 := by
      by_cases before : index.val < other.val
      · have ordered := Controller.Horn.IndexScanWhole.recordOffset_mono clauses recordStart (index.val + 1) other.val
          (by omega) (by have := other.isLt; omega)
        rw [Controller.Horn.NormalizeLoop.recordOffset_succ clauses recordStart index.val index.isLt] at ordered
        exact Or.inl (by omega)
      · have after : other.val < index.val := by omega
        have ordered := Controller.Horn.IndexScanWhole.recordOffset_mono clauses recordStart (other.val + 1) index.val
          (by omega) (by have := index.isLt; omega)
        rw [Controller.Horn.NormalizeLoop.recordOffset_succ clauses recordStart other.val other.isLt] at ordered
        exact Or.inr (by omega)
    simpa only [ite_eq_right equal] using mutable_store_outside
      (Controller.Horn.Worklist.compileClause clauses[other.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val) (counts other)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2) (fired other) heap (rows other)
      (by have := (rows index).fits; omega) outside (word width newCount)


/-- One actual nonzero original occurrence iteration retains the complete
original spine, FIFO, and all original rows, changing only its physical count. -/
theorem nonzero_original_iteration (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready : Nat) (program : Program width 8)
    (queue : List (Fin n)) (counts : Fin clauses.length → Nat) (fired : Fin clauses.length → Bool)
    (rowIndex : Fin clauses.length) (edgeIndex : Fin (Controller.Horn.IndexScan.occurrences clauses recordStart).length)
    (remaining : Nat) (state : State width 8)
    (spine : Spine clauses recordStart recordEnd base state.heap)
    (fifo : Stored queue base state.heap)
    (rows : ∀ other : Fin clauses.length,
      MutableStored (Controller.Horn.Worklist.compileClause clauses[other.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val) (counts other) (fired other) state.heap)
    (sourceRow : (Controller.Horn.IndexScan.occurrences clauses recordStart)[edgeIndex.val].1 =
      Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex.val)
    (countAt : counts rowIndex = remaining + 1) (positiveCount : 0 < remaining)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (held : state.reg 0 = word width (recordEnd + 2 * edgeIndex.val))
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 12 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 12 state.liveWords ∧
      Spine clauses recordStart recordEnd base final.heap ∧ Stored queue base final.heap ∧
      (∀ other : Fin clauses.length,
        MutableStored (Controller.Horn.Worklist.compileClause clauses[other.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)
          (if other = rowIndex then remaining else counts other) (fired other) final.heap) ∧
      final.reg 0 = word width (Controller.Horn.IndexScan.heads recordEnd
        ((Controller.Horn.IndexScan.occurrences clauses recordStart).take edgeIndex.val)
        (Controller.Horn.IndexScan.occurrences clauses recordStart)[edgeIndex.val].2) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.reg 6 = word width (2 ^ width - 1) ∧ final.heap.size = state.heap.size ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width entry ∧ final.halted = false := by
  have stored : MutableStored (Controller.Horn.Worklist.compileClause clauses[rowIndex.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex.val)
      (remaining + 1) (fired rowIndex) state.heap := by simpa only [countAt] using rows rowIndex
  have linked : NodeStored (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex.val)
      (Controller.Horn.IndexScan.heads recordEnd
        ((Controller.Horn.IndexScan.occurrences clauses recordStart).take edgeIndex.val)
        (Controller.Horn.IndexScan.occurrences clauses recordStart)[edgeIndex.val].2)
      (recordEnd + 2 * edgeIndex.val) state.heap := by simpa only [sourceRow] using spine.nodes edgeIndex
  obtain ⟨final, trace, finalStored, heap, nextHeld, finalZero, finalOne, finalDecrement,
      size, stack, output, pc, live⟩ := Controller.Horn.WorklistBucketCases.nonzero_iteration
        program entry exit ready (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex.val)
        (Controller.Horn.IndexScan.heads recordEnd
          ((Controller.Horn.IndexScan.occurrences clauses recordStart).take edgeIndex.val)
          (Controller.Horn.IndexScan.occurrences clauses recordStart)[edgeIndex.val].2)
        (recordEnd + 2 * edgeIndex.val) remaining (Controller.Horn.Worklist.compileClause clauses[rowIndex.val])
        (fired rowIndex) state linked stored present (by have := spine.positiveEnd; omega)
        positiveCount held one zero decrement position running capacity room
  have bound : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex.val + 2 < state.heap.size :=
    by have := stored.fits; omega
  have countFits : remaining < 2 ^ width := by have := stored.countFits; omega
  have startLower := Controller.Horn.IndexScanWhole.recordOffset_mono clauses recordStart 0 rowIndex.val
    (by omega) (by have := rowIndex.isLt; omega)
  have startValue : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart 0 = recordStart :=
    by simp [Controller.Horn.NormalizeLoop.recordOffset]
  rw [startValue] at startLower
  refine ⟨final, trace, ?_, ?_, ?_, nextHeld, finalZero, finalOne, finalDecrement, size, stack, output, pc, live⟩
  · simpa only [heap] using original_count_store_spine clauses recordStart recordEnd base rowIndex state.heap spine bound (word width remaining)
  · simpa only [heap] using fifo_store queue base
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex.val + 2) state.heap fifo bound
      (Or.inr (by omega)) (word width remaining)
  · intro other
    simpa only [heap] using count_store_rows clauses recordStart counts fired rowIndex remaining state.heap rows countFits other

end Controller.Horn.WorklistBucketChain
