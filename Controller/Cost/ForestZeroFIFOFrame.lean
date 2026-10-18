module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistFIFORun
public import Controller.Cost.ForestZeroBackendFrame

@[expose] public section

/-! Actual worklist transitions preserve all source cells below the mutable
scratch region; every exceptional store is bounded by original physical rows. -/
namespace Controller.Cost.ForestZeroFIFOFrame
open Controller.Horn
open Controller.Cost Controller.Cost.ForestZeroBackendFrame
open Controller.Horn.WorklistPropagation Controller.Horn.WorklistFIFORun
open Controller.Horn.WorklistBucketSuccessor Controller.Horn.WorklistPropagationStep
open Controller.Horn.WorklistBucketRun Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketReady Controller.Horn.WorklistBucketFrame
open Controller.Horn.WorklistBucketNegative Controller.Horn.WorklistBucketCharge
variable {width n : Nat}

theorem nonzero_prefix_frame (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (index : Fin clauses.length)
    (current : Fin (IndexScan.occurrences clauses recordStart).length) (state final : State width 8)
    (invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited
      (recordEnd + 2 * current.val) fired state.heap)
    (sourceRow : (IndexScan.occurrences clauses recordStart)[current.val].1 =
      Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
    (sourceLabel : (IndexScan.occurrences clauses recordStart)[current.val].2 = active)
    (nonzero : 0 < rowCounts clauses recordStart queue head active visited index - 1)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (held : state.reg 0 = word width (recordEnd + 2 * current.val))
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 12 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (actual : Execution program state final 12 state.liveWords)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    PrefixFrame prefixSize state.heap final.heap := by
  have countPositive : 0 < rowCounts clauses recordStart queue head active visited index := by omega
  have stored : Controller.Horn.WorklistStorage.MutableStored
      (Controller.Horn.Worklist.compileClause clauses[index.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
      (rowCounts clauses recordStart queue head active visited index - 1 + 1) (fired index) state.heap := by
    have original := invariant.rows index
    have count : rowCounts clauses recordStart queue head active visited index =
        rowCounts clauses recordStart queue head active visited index - 1 + 1 := by omega
    change Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
      (rowCounts clauses recordStart queue head active visited index) (fired index) state.heap at original
    simpa only [← count] using original
  have linked : Controller.Horn.WorklistStorage.NodeStored
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
      (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
      (recordEnd + 2 * current.val) state.heap := by
    simpa only [sourceRow, sourceLabel] using invariant.spine.nodes current
  obtain ⟨same, sameTrace, _, heap, _, _, _, _, _, _, _, _, _⟩ :=
    Controller.Horn.WorklistBucketCases.nonzero_iteration program entry exit ready
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
      (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
      (recordEnd + 2 * current.val) (rowCounts clauses recordStart queue head active visited index - 1)
      (Controller.Horn.Worklist.compileClause clauses[index.val]) (fired index) state linked stored present
      (by have := invariant.spine.positiveEnd; omega) nonzero held one zero decrement position running capacity room
  have equal := Controller.Horn.JoinedRuleFrame.execution_endpoint_unique actual sameTrace
  have rowLower : recordStart ≤ Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val := by
    unfold Controller.Horn.NormalizeLoop.recordOffset
    omega
  rw [equal, heap]
  exact Controller.Cost.ForestZeroBackendFrame.store state.heap
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2)
    (word width (rowCounts clauses recordStart queue head active visited index - 1))
    (by have := stored.fits; omega) (by omega) prefixBound

theorem negative_head_successor (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (active forcedHead : Fin n) (labels : List (Fin n))
    (visited : List Nat) (fired : Fin clauses.length → Bool) (index : Fin clauses.length)
    (current : Fin (IndexScan.occurrences clauses recordStart).length) (state : State width 8)
    (invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited
      (recordEnd + 2 * current.val) fired state.heap)
    (firedZero : FiredZero clauses recordStart queue head (some active) visited fired)
    (sourceRule : Controller.Horn.Worklist.compileClause clauses[index.val] = .negative forcedHead labels)
    (sourceRow : (IndexScan.occurrences clauses recordStart)[current.val].1 =
      Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
    (sourceLabel : (IndexScan.occurrences clauses recordStart)[current.val].2 = active)
    (readyCount : rowCounts clauses recordStart queue head active visited index - 1 = 0)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[tailSlot (n := n) base]'tailBound = word width (queueStart (n := n) base + queue.length))
    (held : state.reg 0 = word width (recordEnd + 2 * current.val))
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (room : state.heap.size < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size)
    (prefixBelow : prefixSize ≤ base) :
    ∃ final, Execution program state final (if forcedHead ∈ queue then 32 else 35) state.liveWords ∧
      Invariant clauses recordStart recordEnd base (queueAfter queue forcedHead) head (some active)
        (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
        (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
        (fun other => if other = index then true else fired other) final.heap ∧
      FiredZero clauses recordStart (queueAfter queue forcedHead) head (some active)
        (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
        (fun other => if other = index then true else fired other) ∧
      final.reg 0 = word width (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.heap[tailSlot (n := n) base]? = some (word width (queueStart (n := n) base + (queueAfter queue forcedHead).length)) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      (∀ assignment : Fin n → Bool, (∀ label ∈ queue, assignment label = false) →
        Controller.Horn.Worklist.Rule.Holds assignment (.negative forcedHead labels) → assignment forcedHead = false) ∧
      final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]? ∧
      PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨indices, visitedMap, path⟩ := invariant.path active (by simp)
  have fresh := invariant.activeFresh active (by simp)
  have unvisited : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∉ visited := by
    simpa only [sourceRow, ← visitedMap] using current_row_unvisited clauses recordStart recordEnd active indices current
      path sourceLabel invariant.spine.positiveEnd
  have incident := occurrence_incident clauses recordStart current index active sourceRow sourceLabel
  have predecessorPositive := fresh_visit_positive (Controller.Horn.Worklist.compileClause clauses[index.val]) queue head active visited
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) unvisited incident fresh
  have notFired := fresh_row_not_fired clauses recordStart queue head active visited fired firedZero index unvisited incident fresh
  have oldOne : rowCounts clauses recordStart queue head active visited index = 1 := by
    change 0 < rowCounts clauses recordStart queue head active visited index at predecessorPositive
    omega
  have storedOld : MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
      (rowCounts clauses recordStart queue head active visited index) (fired index) state.heap := invariant.rows index
  have stored : MutableStored (.negative forcedHead labels)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) 1 false state.heap := by
    simpa only [sourceRule, oldOne, notFired] using storedOld
  have linked : NodeStored (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
      (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
      (recordEnd + 2 * current.val) state.heap := by simpa only [sourceRow, sourceLabel] using invariant.spine.nodes current
  obtain ⟨middle, first, selected, heap, rowHeld, nextHeld, count, middleZero, middleOne, middleDecrement,
      size, stack, output, pc, live⟩ := Controller.Horn.WorklistBucketCases.bucket_visit_execution program entry exit ready
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
        (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
        (recordEnd + 2 * current.val) 0 (.negative forcedHead labels) false state linked stored loopAt
        (by have := invariant.spine.positiveEnd; omega) held one zero decrement position running capacity room
  have bound : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2 < state.heap.size :=
    by have := stored.fits; omega
  have startLower : recordStart ≤ Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val := by
    have lower := Controller.Horn.IndexScanWhole.recordOffset_mono clauses recordStart 0 index.val (by omega) (by have := index.isLt; omega)
    simpa [Controller.Horn.NormalizeLoop.recordOffset] using lower
  have middleSpine : Spine clauses recordStart recordEnd base middle.heap := by
    simpa only [heap] using Controller.Horn.WorklistBucketChain.original_count_store_spine clauses recordStart recordEnd base
      index state.heap invariant.spine bound (word width 0)
  have middleFifo : Stored queue base middle.heap := by
    simpa only [heap] using Controller.Horn.WorklistBucketChain.fifo_store queue base
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val + 2) state.heap invariant.fifo bound
      (Or.inr (by omega)) (word width 0)
  have countValues (other : Fin clauses.length) : rowCounts clauses recordStart queue head active
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val]) other =
      if other = index then 0 else rowCounts clauses recordStart queue head active visited other := by
    have successor := visited_count_successor clauses recordStart queue head active visited index unvisited incident fresh other
    change rowCounts clauses recordStart queue head active
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val]) other =
      (if other = index then rowCounts clauses recordStart queue head active visited other - 1
        else rowCounts clauses recordStart queue head active visited other) at successor
    by_cases equal : other = index
    · subst other; simpa [oldOne] using successor
    · simpa only [ite_eq_right equal] using successor
  have middleRows : ∀ other : Fin clauses.length,
      MutableStored (Controller.Horn.Worklist.compileClause clauses[other.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)
        (rowCounts clauses recordStart queue head active
          (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val]) other) (fired other) middle.heap := by
    intro other
    simpa only [heap, countValues] using Controller.Horn.WorklistBucketChain.count_store_rows clauses recordStart
      (rowCounts clauses recordStart queue head active visited) fired index 0 state.heap invariant.rows (by have := stored.countFits; omega) other
  have selectedZero : rowCounts clauses recordStart queue head active
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val]) index = 0 := by
    simpa using countValues index
  have middleTailBound : tailSlot (n := n) base < middle.heap.size := by omega
  have middleTail : middle.heap[tailSlot (n := n) base]'middleTailBound = word width (queueStart (n := n) base + queue.length) := by
    simpa only [heap] using (Array.getElem_set_ne bound tailBound (by unfold tailSlot; omega)).trans tailValue
  let dispatched := Controller.Horn.RuleDispatch.branchFinished middle 7 ready
  have branch := Controller.Horn.RuleDispatch.branch_execution program (entry + 9) ready 7
    (by simpa [Controller.Horn.WorklistBucketLoop.code] using loopAt ⟨9, by decide⟩) middle pc live (by omega)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame middle 7 ready
  have dispatchHeap : dispatched.heap = middle.heap := frame.2.1
  have dispatchPC : dispatched.pc = word width ready := by simp [dispatched, Controller.Horn.RuleDispatch.branchFinished, count, word]
  have dispatchLive : dispatched.liveWords = middle.liveWords := frame.2.2.2.2.2
  have dispatchStored : MutableStored (.negative forcedHead labels)
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) 0 false dispatched.heap := by
    simpa only [dispatchHeap] using selected
  obtain ⟨final, last, finalSpine, finalFifo, finalRows, finalNext, finalZero, finalOne, finalDecrement,
      finalSize, finalStack, finalOutput, finalPC, finalRunning⟩ := negative_original_framed clauses
        recordStart recordEnd base ready skip conflict entry
        (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active) program queue
        (rowCounts clauses recordStart queue head active
          (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])) fired index forcedHead labels dispatched
        sourceRule selectedZero notFired (by simpa only [dispatchHeap] using middleSpine)
        (by simpa only [dispatchHeap] using middleFifo) (by intro other; simpa only [dispatchHeap] using middleRows other)
        separated readyAt (by simpa only [dispatchHeap] using middleTailBound)
        (by simpa only [dispatchHeap] using middleTail) ((congrFun frame.1 1).trans rowHeld)
        ((congrFun frame.1 4).trans nextHeld) ((congrFun frame.1 5).trans middleOne)
        ((congrFun frame.1 2).trans middleZero) ((congrFun frame.1 6).trans middleDecrement) dispatchPC
        (frame.2.2.2.2.1.trans live) readyCapacity (by simpa only [dispatchHeap, size] using room)
  obtain ⟨tailFinal, tailTrace, _, _, _, _, _, _, _, _, _, _, _, tailGeneral, finalTail⟩ := negative_tail_framed program base ready skip conflict entry
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
      (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active) queue forcedHead labels dispatched
      readyAt (by simpa only [dispatchHeap] using middleFifo) dispatchStored (by omega)
      (by simpa only [dispatchHeap] using middleTailBound) (by simpa only [dispatchHeap] using middleTail)
      ((congrFun frame.1 1).trans rowHeld) ((congrFun frame.1 4).trans nextHeld) ((congrFun frame.1 5).trans middleOne)
      ((congrFun frame.1 2).trans middleZero) ((congrFun frame.1 6).trans middleDecrement) dispatchPC
      (frame.2.2.2.2.1.trans live) readyCapacity (by simpa only [dispatchHeap, size] using room)
  have sameFinal := Controller.Horn.JoinedRuleFrame.execution_endpoint_unique last tailTrace
  have savedTail : final.heap[tailSlot (n := n) base]? = some (word width (queueStart (n := n) base + (queueAfter queue forcedHead).length)) := by
    simpa only [sameFinal] using finalTail
  have savedHead : final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]? := by
    have tailHead := tailGeneral (headSlot (n := n) base)
      (by unfold headSlot; omega)
      (by unfold headSlot nextSlot; omega)
      (by unfold headSlot tailSlot; omega)
      (by have := forcedHead.isLt; unfold headSlot offAddress; omega)
      (by unfold headSlot queueStart; omega)
    calc
      final.heap[headSlot (n := n) base]? = tailFinal.heap[headSlot (n := n) base]? := congrArg (fun final : State width 8 => final.heap[headSlot (n := n) base]?) sameFinal
      _ = dispatched.heap[headSlot (n := n) base]? := tailHead
      _ = middle.heap[headSlot (n := n) base]? := congrArg (fun heap : Array (Word width) => heap[headSlot (n := n) base]?) dispatchHeap
      _ = state.heap[headSlot (n := n) base]? := by
        rw [heap]
        exact Array.getElem?_set_ne bound (by unfold headSlot; omega)
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    refine ⟨prefixBound, ?_, ?_⟩
    · rw [finalSize, dispatchHeap, size]; exact prefixBound
    · intro pos below
      have tailCell := tailGeneral pos
        (by omega) (by unfold nextSlot; omega) (by unfold tailSlot; omega)
        (by have := forcedHead.isLt; unfold offAddress; omega)
        (by unfold queueStart; omega)
      calc
        final.heap[pos]? = tailFinal.heap[pos]? := congrArg (fun final : State width 8 => final.heap[pos]?) sameFinal
        _ = dispatched.heap[pos]? := tailCell
        _ = middle.heap[pos]? := congrArg (fun heap : Array (Word width) => heap[pos]?) dispatchHeap
        _ = state.heap[pos]? := by
          rw [heap]
          exact Array.getElem?_set_ne bound (by omega)
  have extendedPath := prefix_append _ recordEnd active _ _ _ indices [current] path
    (LinkPrefix.cons current [] _ sourceLabel (LinkPrefix.nil _))
  have currentBound : head < queue.length := by
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp invariant.activeCurrent.symm
    exact inside
  have finalInvariant : Invariant clauses recordStart recordEnd base (queueAfter queue forcedHead) head (some active)
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
      (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
      (fun other => if other = index then true else fired other) final.heap := by
    refine ⟨finalSpine, finalFifo, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_cases stale : forcedHead ∈ queue <;> simp [queueAfter, stale] <;> omega
    · rw [queue_after_index queue forcedHead head currentBound]; exact invariant.activeCurrent
    · simp
    · intro label member
      have equal : label = active := by simpa using member
      subst label
      refine ⟨indices ++ [current], ?_, extendedPath⟩
      simp only [List.map_append, List.map_cons, List.map_nil, sourceRow, ← visitedMap]
    · intro label member
      exact queue_after_includes queue forcedHead label (invariant.activeQueued label member)
    · intro label member
      rw [queue_after_take queue forcedHead head invariant.headBound]
      exact invariant.activeFresh label member
    · intro other
      simpa only [queue_after_processed queue forcedHead head (some active)
        (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val) invariant.headBound, rowCounts] using finalRows other
  have finalFiredZero : FiredZero clauses recordStart (queueAfter queue forcedHead) head (some active)
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
      (fun other => if other = index then true else fired other) := by
    intro other wasFired
    rw [queue_after_processed queue forcedHead head (some active)
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val) invariant.headBound]
    by_cases equal : other = index
    · subst other; exact selectedZero
    · have oldFired : fired other = true := by simpa only [ite_eq_right equal] using wasFired
      exact zero_monotone _ _ _ (processed_visit_subset queue head active visited
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)) (firedZero other oldFired)
  have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [size, stack, output]
  refine ⟨final, ?_, finalInvariant, finalFiredZero, finalNext, finalZero, finalOne, finalDecrement, savedTail,
    finalSize.trans ((congrArg Array.size dispatchHeap).trans size), finalStack.trans (frame.2.2.1.trans stack),
    finalOutput.trans (frame.2.2.2.1.trans output), finalPC, finalRunning, ?_, savedHead, retained⟩
  · have trace := first.append (branch.append last)
    by_cases stale : forcedHead ∈ queue
    · simpa only [ite_eq_left stale, dispatchLive, middleLive, Nat.max_self, Nat.reduceAdd] using trace
    · simpa only [ite_eq_right stale, dispatchLive, middleLive, Nat.max_self, Nat.reduceAdd] using trace
  · intro assignment falseQueue model
    apply zero_forces_head queue head (some active)
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) forcedHead labels assignment
      invariant.activeQueued _ falseQueue model
    simpa only [rowCounts, sourceRule] using selectedZero

theorem conflict_iteration (prefixSize : Nat) (program : Program width 8)
    (entry exit ready base skip conflict row next node : Nat) (labels : List (Fin n))
    (state : State width 8) (linked : NodeStored row next node state.heap)
    (stored : MutableStored (.positive labels) row 1 false state.heap)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (positiveNode : 0 < node) (held : state.reg 0 = word width node)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (room : state.heap.size < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size)
    (rowAbove : prefixSize ≤ row) :
    ∃ final, Execution program state final 15 state.liveWords ∧
      MutableStored (.positive labels) row 0 true final.heap ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width conflict ∧ final.halted = false ∧ PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨middle, first, result, heap, rowHeld, nextHeld, count, middleZero, middleOne, middleDecrement,
      size, stack, output, pc, live⟩ := Controller.Horn.WorklistBucketCases.bucket_visit_execution program entry exit ready row next node 0
        (.positive labels) false state linked stored loopAt positiveNode held one zero decrement position running capacity room
  let dispatched := Controller.Horn.RuleDispatch.branchFinished middle 7 ready
  have branch := Controller.Horn.RuleDispatch.branch_execution program (entry + 9) ready 7
    (by simpa [Controller.Horn.WorklistBucketLoop.code] using loopAt ⟨9, by decide⟩)
    middle pc live (by omega)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame middle 7 ready
  have dispatchPC : dispatched.pc = word width ready := by
    simp [dispatched, Controller.Horn.RuleDispatch.branchFinished, count, word]
  have dispatchHeap : dispatched.heap = middle.heap := frame.2.1
  have dispatchLive : dispatched.liveWords = middle.liveWords := frame.2.2.2.2.2
  obtain ⟨final, last, finalStored, _, _, _, _, _, finalHeap, finalSize, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    Controller.Horn.WorklistBucketCases.positive_execution program base ready skip conflict entry row labels dispatched
      (by simpa only [dispatchHeap] using result) readyAt ((congrFun frame.1 1).trans rowHeld)
      ((congrFun frame.1 2).trans middleZero) ((congrFun frame.1 6).trans middleDecrement) dispatchPC
      (frame.2.2.2.2.1.trans live) readyCapacity (by simpa only [dispatchHeap, size] using room)
  have firstFrame : PrefixFrame prefixSize state.heap dispatched.heap := by
    rw [dispatchHeap, heap]
    exact Controller.Cost.ForestZeroBackendFrame.store state.heap (row + 2) (word width 0)
      (by have := stored.fits; omega) (by omega) prefixBound
  have lastFrame : PrefixFrame prefixSize dispatched.heap final.heap := by
    rw [finalHeap]
    exact Controller.Cost.ForestZeroBackendFrame.store dispatched.heap row (word width 0)
      (by have fits := result.fits; rw [dispatchHeap]; omega) rowAbove firstFrame.2.1
  have retained := Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame
  have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [size, stack, output]
  refine ⟨final, ?_, finalStored, finalSize.trans ((congrArg Array.size frame.2.1).trans size),
    finalStack.trans (frame.2.2.1.trans stack), finalOutput.trans (frame.2.2.2.1.trans output), finalPC, finalRunning, retained⟩
  · simpa only [dispatchLive, middleLive, Nat.max_self, Nat.reduceAdd] using first.append (branch.append last)

theorem step_head_charged (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (bound : Nat) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state)
    (nonnil : IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take bound) active ≠ 0)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    (∃ nextQueue nextVisited nextFired nextBound final ticks,
      nextBound < bound ∧ matching (IndexScan.occurrences clauses recordStart) active bound =
        matching (IndexScan.occurrences clauses recordStart) active nextBound + 1 ∧
      queue.length ≤ nextQueue.length ∧ nextQueue.take head = queue.take head ∧ ticks ≤ 32 + 3 * (nextQueue.length - queue.length) ∧
      Execution program state final ticks state.liveWords ∧
      Snapshot clauses recordStart recordEnd base entry nextQueue head active nextVisited nextFired nextBound final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]? ∧
      PrefixFrame prefixSize state.heap final.heap) ∨
    (∃ final, Execution program state final 15 state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width conflict ∧ final.halted = false ∧ PrefixFrame prefixSize state.heap final.heap) := by
  rcases head_frontier (IndexScan.occurrences clauses recordStart) recordEnd
    snapshot.invariant.spine.positiveEnd active bound snapshot.within with nil | ⟨current, less, label, pointer⟩
  · exact False.elim (nonnil nil)
  have charged := matching_predecessor (IndexScan.occurrences clauses recordStart) recordEnd
    snapshot.invariant.spine.positiveEnd active bound snapshot.within current less label pointer
  have invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited
      (recordEnd + 2 * current.val) fired state.heap := by
    simpa only [pointer] using snapshot.invariant
  have held : state.reg 0 = word width (recordEnd + 2 * current.val) := by
    simpa only [pointer] using snapshot.held
  obtain ⟨index, sourceRow, incident⟩ := occurrence_source clauses recordStart
    (IndexScan.occurrences clauses recordStart)[current.val].1
    (IndexScan.occurrences clauses recordStart)[current.val].2 (List.getElem_mem current.isLt)
  have sourceIncident : active ∈ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives := by
    simpa only [label] using incident
  by_cases countZero : rowCounts clauses recordStart queue head active visited index - 1 = 0
  · have fresh := invariant.activeFresh active (by simp)
    obtain ⟨indices, mapRows, path⟩ := invariant.path active (by simp)
    have unvisited : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∉ visited := by
      simpa only [sourceRow, ← mapRows] using current_row_unvisited clauses recordStart recordEnd active indices current
        path label invariant.spine.positiveEnd
    have predecessorPositive := Controller.Horn.WorklistPropagationStep.fresh_visit_positive
      (Controller.Horn.Worklist.compileClause clauses[index.val]) queue head active visited
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) unvisited sourceIncident fresh
    have notFired := Controller.Horn.WorklistPropagationStep.fresh_row_not_fired clauses recordStart queue head active visited fired
      snapshot.firedZero index unvisited sourceIncident fresh
    have oldOne : rowCounts clauses recordStart queue head active visited index = 1 := by
      change 0 < rowCounts clauses recordStart queue head active visited index at predecessorPositive
      omega
    cases ruleEq : Controller.Horn.Worklist.compileClause clauses[index.val] with
    | skip => simp [ruleEq, Controller.Horn.Worklist.Rule.positives] at sourceIncident
    | positive labels =>
      have selected : Controller.Horn.WorklistStorage.MutableStored (.positive labels)
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) 1 false state.heap := by
        have stored := invariant.rows index
        change Controller.Horn.WorklistStorage.MutableStored
          (Controller.Horn.Worklist.compileClause clauses[index.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
          (rowCounts clauses recordStart queue head active visited index) (fired index) state.heap at stored
        simpa only [ruleEq, oldOne, notFired] using stored
      have linked : Controller.Horn.WorklistStorage.NodeStored
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
          (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
          (recordEnd + 2 * current.val) state.heap := by
        simpa only [sourceRow, label] using invariant.spine.nodes current
      obtain ⟨final, trace, _, size, stack, output, pc, running, frame⟩ :=
        conflict_iteration prefixSize program entry exit ready base skip conflict
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
          (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
          (recordEnd + 2 * current.val) labels state linked selected loopAt readyAt
          (by have := invariant.spine.positiveEnd; omega) held snapshot.one snapshot.zero snapshot.decrement
          snapshot.position snapshot.running capacity readyCapacity snapshot.room prefixBound
          (by have rowAbove := Controller.Horn.NormalizeLoop.recordOffset_above clauses recordStart index.val; omega)
      exact Or.inr ⟨final, trace, size, stack, output, pc, running, frame⟩
    | negative forcedHead labels =>
      have tailBound : Controller.Horn.WorklistBucketReady.tailSlot (n := n) base < state.heap.size := by
        have := invariant.fifo.fits
        unfold Controller.Horn.WorklistBucketReady.tailSlot
        omega
      have tailValue : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]'tailBound =
          word width (Controller.Horn.WorklistMark.queueStart (n := n) base + queue.length) := by
        have value := snapshot.tail
        simpa only [Array.getElem?_eq_getElem tailBound, Option.some.injEq] using value
      obtain ⟨final, trace, nextInvariant, nextFired, next, zero, one, decrement, tail,
          size, stack, output, pc, running, _, headFrame, frame⟩ := negative_head_successor prefixSize
        clauses recordStart recordEnd base entry exit ready skip conflict program queue head active forcedHead labels
        visited fired index current state invariant snapshot.firedZero ruleEq sourceRow label countZero separated loopAt readyAt
        tailBound tailValue held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running
        capacity readyCapacity snapshot.room prefixBound prefixBelow
      refine Or.inl ⟨Controller.Horn.WorklistBucketReady.queueAfter queue forcedHead,
        visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
        (fun other => if other = index then true else fired other), current.val, final,
        (if forcedHead ∈ queue then 32 else 35), less, charged, (queue_growth queue forcedHead).1,
        queue_after_take queue forcedHead head invariant.headBound, ?_, trace, ?_, size, stack, output, headFrame, frame⟩
      · exact (negative_cost queue forcedHead).le
      · exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
          decrement, pc, running, by simpa only [size] using snapshot.room⟩
  · have positiveCount : 0 < rowCounts clauses recordStart queue head active visited index - 1 := by omega
    obtain ⟨final, trace, nextInvariant, nextFired, next, zero, one, decrement, tail,
        size, stack, output, pc, running⟩ := nonzero_tail clauses recordStart recordEnd base entry exit ready program
      queue head active visited fired index current state invariant snapshot.firedZero sourceRow label positiveCount
      separated loopAt snapshot.tail held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running capacity snapshot.room
    have headFrame := nonzero_head_frame clauses recordStart recordEnd base entry exit ready program queue head active visited fired
      index current state final invariant sourceRow label positiveCount separated loopAt held snapshot.one snapshot.zero
      snapshot.decrement snapshot.position snapshot.running capacity snapshot.room trace
    have frame := nonzero_prefix_frame prefixSize clauses recordStart recordEnd base entry exit ready program
      queue head active visited fired index current state final invariant sourceRow label positiveCount separated loopAt
      held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running capacity snapshot.room
      trace prefixBound prefixBelow
    refine Or.inl ⟨queue, visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
      fired, current.val, final, 12, less, charged, Nat.le_refl _, rfl, by omega, trace, ?_, size, stack, output, headFrame, frame⟩
    exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
      decrement, pc, running, by simpa only [size] using snapshot.room⟩

theorem bucket_head_charged (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (head : Nat) (active : Fin n)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (bound : Nat) (queue : List (Fin n)) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ finalQueue final ticks,
      queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧ finalQueue.take head = queue.take head ∧
      ticks ≤ 32 * matching (IndexScan.occurrences clauses recordStart) active bound +
        3 * (finalQueue.length - queue.length) + 1 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧ PrefixFrame prefixSize state.heap final.heap ∧
      (final.pc = word width conflict ∨
        ∃ finalVisited finalFired,
          final.pc = word width exit ∧
          Invariant clauses recordStart recordEnd base finalQueue head (some active) finalVisited 0 finalFired final.heap ∧
          FiredZero clauses recordStart finalQueue head (some active) finalVisited finalFired ∧
          final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
            some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + finalQueue.length)) ∧
          final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
          final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]?) := by
  induction bound using Nat.strong_induction_on generalizing queue visited fired state with
  | h bound ih =>
    by_cases nil : IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take bound) active = 0
    · have invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired state.heap := by
        simpa only [nil] using snapshot.invariant
      have held : state.reg 0 = word width 0 := by simpa only [nil] using snapshot.held
      obtain ⟨final, trace, finalInvariant, finalFired, registers, heap, stack, output, pc, running⟩ :=
        nil_endpoint clauses recordStart recordEnd base entry exit ready program queue head active visited fired state
          invariant snapshot.firedZero loopAt held snapshot.position snapshot.running capacity
      have retained : PrefixFrame prefixSize state.heap final.heap := by
        rw [heap]
        exact Controller.Cost.ForestZeroBackendFrame.refl state.heap prefixBound
      refine ⟨queue, final, 1, Nat.le_refl _, invariant.fifo.nodup, rfl, by omega, trace,
        by simpa only [heap], stack, output, running, retained,
        Or.inr ⟨visited, fired, pc, finalInvariant, finalFired, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simpa only [heap] using snapshot.tail
      · exact (congrFun registers 2).trans snapshot.zero
      · exact (congrFun registers 5).trans snapshot.one
      · exact (congrFun registers 6).trans snapshot.decrement
      · exact congrArg (fun heap : Array (Word width) => heap[headSlot (n := n) base]?) heap
    · have matchingPositive : 0 < matching (IndexScan.occurrences clauses recordStart) active bound := by
        rcases head_frontier (IndexScan.occurrences clauses recordStart) recordEnd
          snapshot.invariant.spine.positiveEnd active bound snapshot.within with zero | ⟨index, less, label, pointer⟩
        · contradiction
        · have charged := matching_predecessor (IndexScan.occurrences clauses recordStart) recordEnd
            snapshot.invariant.spine.positiveEnd active bound snapshot.within index less label pointer
          omega
      rcases step_head_charged prefixSize clauses recordStart recordEnd base entry exit ready skip conflict program queue head active
        visited fired bound state snapshot nil separated loopAt readyAt capacity readyCapacity prefixBound prefixBelow with continued | failed
      · obtain ⟨nextQueue, nextVisited, nextFired, nextBound, middle, firstTicks,
          smaller, matchingStep, growth, middlePrefix, firstBound, first, middleSnapshot, middleSize, middleStack, middleOutput, middleHead, firstFrame⟩ := continued
        obtain ⟨finalQueue, final, lastTicks, lastGrowth, unique, finalPrefix, lastBound, last,
            finalSize, finalStack, finalOutput, running, lastFrame, outcome⟩ :=
          ih nextBound smaller nextQueue nextVisited nextFired middle middleSnapshot (by simpa only [middleSize] using prefixBound)
        have middleLive : middle.liveWords = state.liveWords := by
          unfold State.liveWords
          rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, final, firstTicks + lastTicks, by omega, unique, finalPrefix.trans middlePrefix, by omega,
          ?_, finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, running, Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame, ?_⟩
        · simpa only [middleLive, Nat.max_self] using first.append last
        · rcases outcome with failed | ⟨finalVisited, finalFired, pc, invariant, firedZero, tail, zero, one, decrement, header⟩
          · exact Or.inl failed
          · exact Or.inr ⟨finalVisited, finalFired, pc, invariant, firedZero, tail, zero, one, decrement, header.trans middleHead⟩
      · obtain ⟨final, trace, size, stack, output, pc, running, frame⟩ := failed
        exact ⟨queue, final, 15, Nat.le_refl _, snapshot.invariant.fifo.nodup, rfl,
          by omega, trace, size, stack, output, running, frame, Or.inl pc⟩

end Controller.Cost.ForestZeroFIFOFrame
