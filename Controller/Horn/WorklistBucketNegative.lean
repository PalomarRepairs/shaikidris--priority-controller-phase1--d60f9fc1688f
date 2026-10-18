module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucketSuccessor

@[expose] public section

/-! Ready negative occurrences fire their original record and mark a pending
FIFO head. Count semantics remain tied to physically processed labels. -/
namespace Controller.Horn.WorklistBucketNegative
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.WorklistPropagation Controller.Horn.WorklistPropagationStep
open Controller.Horn.WorklistBucketReady Controller.Horn.WorklistBucketFrame
open Controller.Horn.WorklistBucketSuccessor
variable {width n : Nat}

theorem queue_after_take (queue : List (Fin n)) (label : Fin n) (head : Nat)
    (bound : head ≤ queue.length) : (queueAfter queue label).take head = queue.take head := by
  by_cases stale : label ∈ queue
  · simp only [queueAfter, ite_eq_left stale]
  · simp only [queueAfter, ite_eq_right stale]
    exact List.take_append_of_le_length bound

theorem queue_after_index (queue : List (Fin n)) (label : Fin n) (head : Nat)
    (bound : head < queue.length) : (queueAfter queue label)[head]? = queue[head]? := by
  by_cases stale : label ∈ queue
  · simp only [queueAfter, ite_eq_left stale]
  · simp only [queueAfter, ite_eq_right stale]
    exact List.getElem?_append_left bound

theorem queue_after_includes (queue : List (Fin n)) (label : Fin n) :
    ∀ query ∈ queue, query ∈ queueAfter queue label := by
  intro query member
  by_cases stale : label ∈ queue <;> simp [queueAfter, stale, member]

theorem queue_after_processed (queue : List (Fin n)) (label : Fin n) (head : Nat)
    (active : Option (Fin n)) (visited : List Nat) (row : Nat) (bound : head ≤ queue.length) :
    processedForRow (queueAfter queue label) head active visited row = processedForRow queue head active visited row := by
  unfold processedForRow
  rw [queue_after_take queue label head bound]

/-- Count-zero support forces the original negative head in every model whose
queued labels are already false, even though pending labels have not changed counts. -/
theorem zero_forces_head (queue : List (Fin n)) (head : Nat) (active : Option (Fin n))
    (visited : List Nat) (row : Nat) (label : Fin n) (labels : List (Fin n)) (assignment : Fin n → Bool)
    (queued : ∀ query ∈ active.toList, query ∈ queue)
    (countZero : remaining (.negative label labels) (processedForRow queue head active visited row) = 0)
    (falseQueue : ∀ query ∈ queue, assignment query = false)
    (model : Controller.Horn.Worklist.Rule.Holds assignment (.negative label labels)) : assignment label = false := by
  rcases model with forced | ⟨positive, incident, trueValue⟩
  · exact forced
  · have member := zero_support_queued (.negative label labels) queue head active visited row queued countZero positive incident
    have falseValue := falseQueue positive member
    rw [falseValue] at trueValue
    contradiction

theorem negative_tail_framed (program : Program width 8) (base entry skip conflict bucket row next : Nat)
    (queue : List (Fin n)) (head : Fin n) (labels : List (Fin n)) (state : State width 8)
    (present : Controller.Horn.WorklistBucketReady.At (n := n) program base entry skip conflict bucket)
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (stored : MutableStored (.negative head labels) row 0 false state.heap)
    (separated : base + 5 * n + 4 ≤ row)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[tailSlot (n := n) base]'tailBound =
      word width (queueStart (n := n) base + queue.length))
    (rowHeld : state.reg 1 = word width row) (nextHeld : state.reg 4 = word width next)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final (if head ∈ queue then 22 else 25) state.liveWords ∧
      Controller.Horn.WorklistMark.Stored (queueAfter queue head) base final.heap ∧
      MutableStored (.negative head labels) row 0 true final.heap ∧
      final.reg 0 = word width next ∧ final.heap.size = state.heap.size ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width bucket ∧ final.halted = false ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      (∀ pos, row ≠ pos → nextSlot (n := n) base ≠ pos → tailSlot (n := n) base ≠ pos →
        offAddress base head ≠ pos → queueStart (n := n) base + queue.length ≠ pos →
          final.heap[pos]? = state.heap[pos]?) ∧
      final.heap[tailSlot (n := n) base]? = some (word width (queueStart (n := n) base + (queueAfter queue head).length)) := by
  obtain ⟨firedState, fireTrace, firedStored, rowFrame, nextFrame, zeroFrame, oneFrame, decrementFrame,
      firedHeap, firedSize, firedStack, firedOutput, firedPC, firedRunning⟩ :=
    negative_prefix program base entry skip conflict bucket row head labels state stored present rowHeld zero decrement
      position running capacity room
  have rowBound : row < state.heap.size := by have := stored.fits; omega
  have firedFifo : Controller.Horn.WorklistMark.Stored queue base firedState.heap := by
    rw [firedHeap]
    exact Controller.Horn.WorklistBucketChain.fifo_store queue base row state.heap fifo rowBound (Or.inr (by omega)) (word width 0)
  have firedTailBound : tailSlot (n := n) base < firedState.heap.size := by omega
  have firedTail : firedState.heap[tailSlot (n := n) base]'firedTailBound =
      word width (queueStart (n := n) base + queue.length) := by
    simpa only [firedHeap] using
      (Array.getElem_set_ne rowBound tailBound (by unfold tailSlot; omega)).trans tailValue
  have headBound : row + 1 < firedState.heap.size := by have := firedStored.fits; omega
  have originalHead : firedState.heap[row + 1]'headBound = word width head.val := by
    simpa [Controller.Horn.RuleCopy.headWord] using firedStored.headValue
  obtain ⟨prepared, prepareTrace, headReady, offReady, tailReady, preparedZero, preparedOne, preparedDecrement,
      preparedHeap, preparedStack, preparedOutput, preparedPC, preparedRunning⟩ :=
    prepare_execution program base entry skip conflict bucket row next (queueStart (n := n) base + queue.length)
      head firedState present firedFifo.fits headBound separated originalHead firedTailBound firedTail
      (rowFrame.trans rowHeld) (nextFrame.trans nextHeld) (oneFrame.trans one) firedPC firedRunning capacity (by omega)
  have preparedSize : prepared.heap.size = firedState.heap.size := by rw [preparedHeap]; simp
  have nextBound : nextSlot (n := n) base < firedState.heap.size := by have := firedFifo.fits; unfold nextSlot; omega
  have preparedFifo : Controller.Horn.WorklistMark.Stored queue base prepared.heap := by
    rw [preparedHeap]
    exact Controller.Horn.WorklistBucketChain.fifo_store queue base _ firedState.heap firedFifo nextBound
      (Or.inl ⟨by unfold nextSlot; omega, by unfold nextSlot queueStart; omega⟩) (word width next)
  have preparedStored : MutableStored (.negative head labels) row 0 true prepared.heap := by
    rw [preparedHeap]
    exact Controller.Horn.WorklistBucketChain.mutable_store_outside _ row 0 (nextSlot (n := n) base) true
      firedState.heap firedStored nextBound (Or.inl (by unfold nextSlot; omega)) (word width next)
  have saved : prepared.heap[nextSlot (n := n) base]? = some (word width next) := by
    rw [preparedHeap]
    simp
  obtain ⟨queued, enqueueTrace, queuedFifo, queuedStored, queuedNext, queuedTail, queuedZero, queuedSize,
      queuedStack, queuedOutput, queuedPC, queuedRunning, queuedOne, queuedDecrement, queuedFrame⟩ :=
    enqueue_framed program base entry skip conflict bucket row next queue head labels prepared present preparedFifo
      preparedStored separated saved offReady tailReady headReady (preparedOne.trans (oneFrame.trans one))
      (preparedZero.trans (zeroFrame.trans zero)) preparedPC preparedRunning capacity (by omega)
  have queuedNextBound : nextSlot (n := n) base < queued.heap.size := by have := queuedFifo.fits; unfold nextSlot; omega
  have queuedNextValue : queued.heap[nextSlot (n := n) base]'queuedNextBound = word width next := by
    rw [Array.getElem?_eq_getElem queuedNextBound] at queuedNext
    exact Option.some.inj queuedNext
  obtain ⟨final, returnTrace, finalNext, finalHeap, finalStack, finalOutput, finalPC, finalRunning, returnZero, returnOne, returnDecrement⟩ :=
    return_framed program base entry skip conflict bucket next
      (queueStart (n := n) base + (queueAfter queue head).length) queued present queuedFifo.fits queuedNextBound
      queuedNextValue queuedTail queuedZero queuedPC queuedRunning capacity (by omega)
  have finalSize : final.heap.size = queued.heap.size := by rw [finalHeap]; simp
  have finalFifo : Controller.Horn.WorklistMark.Stored (queueAfter queue head) base final.heap := by
    rw [finalHeap]
    exact Controller.Horn.WorklistBucketChain.fifo_store _ base _ queued.heap queuedFifo (by have := queuedFifo.fits; unfold tailSlot; omega)
      (Or.inl ⟨by unfold tailSlot; omega, by unfold tailSlot queueStart; omega⟩) _
  have finalStored : MutableStored (.negative head labels) row 0 true final.heap := by
    rw [finalHeap]
    exact Controller.Horn.WorklistBucketChain.mutable_store_outside _ row 0 (tailSlot (n := n) base) true
      queued.heap queuedStored (by have := queuedFifo.fits; unfold tailSlot; omega)
      (Or.inl (by unfold tailSlot; omega)) _
  have fireLive : firedState.liveWords = state.liveWords := by unfold State.liveWords; rw [firedSize, firedStack, firedOutput]
  have prepareLive : prepared.liveWords = state.liveWords := by unfold State.liveWords; rw [preparedSize, preparedStack, preparedOutput]; exact fireLive
  have queueLive : queued.liveWords = state.liveWords := by unfold State.liveWords; rw [queuedSize, queuedStack, queuedOutput]; exact prepareLive
  refine ⟨final, ?_, finalFifo, finalStored, finalNext, ?_,
    finalStack.trans (queuedStack.trans (preparedStack.trans firedStack)),
    finalOutput.trans (queuedOutput.trans (preparedOutput.trans firedOutput)), finalPC, finalRunning,
    returnZero.trans queuedZero,
    returnOne.trans (queuedOne.trans (preparedOne.trans (oneFrame.trans one))),
    returnDecrement.trans (queuedDecrement.trans (preparedDecrement.trans (decrementFrame.trans decrement))), ?_, ?_⟩
  · have trace := ((fireTrace.append prepareTrace).append enqueueTrace).append returnTrace
    rw [fireLive, prepareLive, queueLive] at trace
    by_cases stale : head ∈ queue <;> simpa [stale] using trace
  · exact finalSize.trans (queuedSize.trans (preparedSize.trans firedSize))

  · intro pos rowDifferent nextDifferent tailDifferent offDifferent queueDifferent
    calc
      final.heap[pos]? = queued.heap[pos]? := by
        rw [finalHeap]
        exact Array.getElem?_set_ne (by have := queuedFifo.fits; unfold tailSlot; omega) tailDifferent
      _ = prepared.heap[pos]? := queuedFrame pos offDifferent queueDifferent
      _ = firedState.heap[pos]? := by
        rw [preparedHeap]
        exact Array.getElem?_set_ne nextBound nextDifferent
      _ = state.heap[pos]? := by
        rw [firedHeap]
        exact Array.getElem?_set_ne rowBound rowDifferent



  · rw [finalHeap]
    simp


/-- A ready negative physical occurrence completes the actual 35/32-tick
iteration, extending only pending FIFO marks and its visited original link. -/
theorem negative_successor (clauses : List (Controller.CNF.Clause (Fin n)))
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
    (room : state.heap.size < 2 ^ width) :
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
        Controller.Horn.Worklist.Rule.Holds assignment (.negative forcedHead labels) → assignment forcedHead = false) := by
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
  obtain ⟨tailFinal, tailTrace, _, _, _, _, _, _, _, _, _, _, _, _, finalTail⟩ := negative_tail_framed program base ready skip conflict entry
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
    finalOutput.trans (frame.2.2.2.1.trans output), finalPC, finalRunning, ?_⟩
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

end Controller.Horn.WorklistBucketNegative
