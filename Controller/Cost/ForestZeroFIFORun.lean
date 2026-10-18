module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroFIFOFrame

@[expose] public section

/-! The actual FIFO fetch/bucket/advance recursion retains the caller's source
prefix while charging original incidences and fresh queue entries once. -/
namespace Controller.Cost.ForestZeroFIFORun
open Controller.Horn
open Controller.Cost Controller.Cost.ForestZeroBackendFrame
open Controller.Horn.WorklistPropagation Controller.Horn.WorklistFIFORun
open Controller.Horn.WorklistBucketSuccessor Controller.Horn.WorklistPropagationStep
open Controller.Horn.WorklistBucketRun Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketReady Controller.Horn.WorklistBucketFrame
open Controller.Horn.WorklistBucketNegative Controller.Horn.WorklistBucketCharge
variable {width n : Nat}

theorem fetch_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done bucket : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (fired : Fin clauses.length → Bool) (state : State width 8)
    (spine : Spine clauses recordStart recordEnd base state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (rows : ∀ index : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
        (Controller.Horn.WorklistPropagation.remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take head))
        (fired index) state.heap)
    (firedZero : Controller.Horn.WorklistPropagationStep.FiredZero clauses recordStart queue head none [] fired)
    (headBound : head < queue.length)
    (headValue : state.heap[headSlot (n := n) base]? = some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + head)))
    (tailValue : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
      some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + queue.length)))
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : FetchAt (n := n) program base entry done bucket)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 14 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ active final, queue[head]? = some active ∧ Execution program state final 14 state.liveWords ∧
      Controller.Horn.WorklistBucketRun.Snapshot clauses recordStart recordEnd base bucket queue head active [] fired
        (IndexScan.occurrences clauses recordStart).length final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.heap[headSlot (n := n) base]? = some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + head)) ∧ PrefixFrame prefixSize state.heap final.heap := by
  let active : Fin n := queue[head]
  let pointer := Controller.Horn.WorklistMark.queueStart (n := n) base + head
  let tail := Controller.Horn.WorklistMark.queueStart (n := n) base + queue.length
  have headSlotBound : headSlot (n := n) base < state.heap.size := by have := fifo.fits; unfold headSlot; omega
  have tailSlotBound : Controller.Horn.WorklistBucketReady.tailSlot (n := n) base < state.heap.size := by
    have := fifo.fits; unfold Controller.Horn.WorklistBucketReady.tailSlot; omega
  have pointerBound : pointer < state.heap.size := by have := fifo.queue.fits; dsimp [pointer]; omega
  have tailFits : tail < 2 ^ width := by have := fifo.queue.fits; dsimp [tail]; omega
  have headCell : state.heap[headSlot (n := n) base]'headSlotBound = word width pointer := by
    simpa only [Array.getElem?_eq_getElem headSlotBound, Option.some.injEq] using headValue
  have tailCell : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]'tailSlotBound = word width tail := by
    simpa only [Array.getElem?_eq_getElem tailSlotBound, Option.some.injEq] using tailValue
  obtain ⟨tested, first, testPC, testHeap, testStack, testOutput, testRunning, held, testRegs⟩ :=
    header_test_execution program base entry done bucket pointer tail state present headSlotBound headCell tailSlotBound tailCell
      position running capacity room (by omega) tailFits
  have different : pointer ≠ tail := by dsimp [pointer, tail]; omega
  have bodyPC : tested.pc = word width (entry + 6) := by simpa only [ite_eq_right different] using testPC
  have labelCell : tested.heap[pointer]'(by simpa only [testHeap] using pointerBound) = word width active.val := by
    simpa only [testHeap] using fifo.queue.entry ⟨head, headBound⟩
  have bucketBound : Controller.Horn.WorklistStorage.headAddress base active < state.heap.size := by
    have := fifo.fits; have := active.isLt; unfold Controller.Horn.WorklistStorage.headAddress; omega
  have bucketCell : tested.heap[Controller.Horn.WorklistStorage.headAddress base active]'(by simpa only [testHeap] using bucketBound) =
      word width (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) active) := by
    have value := spine.heads active
    simpa only [testHeap, Array.getElem?_eq_getElem bucketBound, Option.some.injEq] using value
  obtain ⟨final, last, finalHeap, finalNext, finalActive, finalRegs, size, stack, output, pc, live⟩ :=
    label_bucket_execution program base entry done bucket pointer
      (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) active) queue active tested present
      (by simpa only [testHeap] using fifo) (by simpa only [testHeap] using pointerBound) labelCell bucketCell held
      ((testRegs 2 (by decide) (by decide) (by decide)).trans zero) bodyPC testRunning capacity
      (by simpa only [testHeap] using room)
  have testedLive : tested.liveWords = state.liveWords := by unfold State.liveWords; rw [testHeap, testStack, testOutput]
  have actualHeap : final.heap = state.heap.set (activeSlot (n := n) base) (word width active.val)
      (by have := fifo.fits; unfold activeSlot; omega) := by simpa only [testHeap] using finalHeap
  obtain ⟨finalSpine, finalFifo, finalRows⟩ := active_store_frame clauses recordStart recordEnd base queue
    (fun index => Controller.Horn.WorklistPropagation.remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take head))
    fired state.heap (word width active.val) spine fifo rows separated
  have current : queue[head]? = some active := by simp only [List.getElem?_eq_getElem headBound]; rfl
  have fresh : active ∉ queue.take head := by
    have taken : (queue.take (head + 1)).Nodup := fifo.nodup.take
    rw [List.take_add_one, current] at taken
    have disjoint := (List.nodup_append.mp taken).2.2
    intro member
    exact disjoint active member active (by simp) rfl
  have invariant : Invariant clauses recordStart recordEnd base queue head (some active) []
      (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) active) fired final.heap := by
    refine ⟨?_, ?_, by omega, current.symm, by simp, ?_, ?_, ?_, ?_⟩
    · simpa only [actualHeap] using finalSpine
    · simpa only [actualHeap] using finalFifo
    · intro label member
      have equal : label = active := by simpa using member
      subst label
      exact ⟨[], rfl, LinkPrefix.nil _⟩
    · intro label member
      have equal : label = active := by simpa using member
      subst label
      exact List.getElem_mem headBound
    · intro label member
      have equal : label = active := by simpa using member
      subst label
      exact fresh
    · intro index
      simpa only [actualHeap, processedForRow, List.not_mem_nil, ite_false, List.append_nil] using finalRows index
  have finalFired : Controller.Horn.WorklistPropagationStep.FiredZero clauses recordStart queue head (some active) [] fired := by
    simpa only [Controller.Horn.WorklistPropagationStep.FiredZero, processedForRow, List.not_mem_nil, ite_false, List.append_nil] using firedZero
  have slotBound : activeSlot (n := n) base < state.heap.size := by have := fifo.fits; unfold activeSlot; omega
  have headFrame : final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]? := by
    rw [actualHeap]
    exact Array.getElem?_set_ne slotBound (by unfold activeSlot headSlot; omega)
  have tailFrame : final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
      state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? := by
    rw [actualHeap]
    exact Array.getElem?_set_ne slotBound (by unfold activeSlot Controller.Horn.WorklistBucketReady.tailSlot; omega)
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    rw [actualHeap]
    exact Controller.Cost.ForestZeroBackendFrame.store state.heap (activeSlot (n := n) base)
      (word width active.val) slotBound (by unfold activeSlot; omega) prefixBound
  refine ⟨active, final, current, ?_, ?_, size.trans (congrArg Array.size testHeap), stack.trans testStack,
    output.trans testOutput, headFrame.trans headValue, retained⟩
  · simpa only [testedLive, Nat.max_self, Nat.reduceAdd] using first.append last
  · refine ⟨Nat.le_refl _, ?_, finalFired, tailFrame.trans tailValue, ?_, ?_, ?_, ?_, pc, live, ?_⟩
    · simpa only [List.take_length] using invariant
    · simpa only [List.take_length] using finalNext
    · exact (finalRegs 2 (by decide) (by decide) (by decide) (by decide)).trans ((testRegs 2 (by decide) (by decide) (by decide)).trans zero)
    · exact (finalRegs 5 (by decide) (by decide) (by decide) (by decide)).trans ((testRegs 5 (by decide) (by decide) (by decide)).trans one)
    · exact (finalRegs 6 (by decide) (by decide) (by decide) (by decide)).trans ((testRegs 6 (by decide) (by decide) (by decide)).trans decrement)
    · simpa only [size, testHeap] using room

theorem fifo_empty (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base fetch done bucket : Nat) (program : Program width 8)
    (queue : List (Fin n)) (fired : Fin clauses.length → Bool) (state : State width 8)
    (initial : Ready clauses recordStart recordEnd base fetch queue queue.length fired state)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch done bucket)
    (capacity : fetch + 14 < 2 ^ width) (prefixBound : prefixSize ≤ state.heap.size) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      Done clauses recordStart recordEnd base done queue fired final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ PrefixFrame prefixSize state.heap final.heap := by
  have headBound : headSlot (n := n) base < state.heap.size := by have := initial.fifo.fits; unfold headSlot; omega
  have tailBound : tailSlot (n := n) base < state.heap.size := by have := initial.fifo.fits; unfold tailSlot; omega
  have headCell : state.heap[headSlot (n := n) base]'headBound = word width (queueStart (n := n) base + queue.length) := by
    simpa only [Array.getElem?_eq_getElem headBound, Option.some.injEq] using initial.headValue
  have tailCell : state.heap[tailSlot (n := n) base]'tailBound = word width (queueStart (n := n) base + queue.length) := by
    simpa only [Array.getElem?_eq_getElem tailBound, Option.some.injEq] using initial.tailValue
  have pointerFits : queueStart (n := n) base + queue.length < 2 ^ width := by
    have queueBound := WorklistMark.enqueue_bound queue initial.fifo.nodup
    have fits := initial.fifo.fits
    have room := initial.room
    unfold queueStart
    omega
  obtain ⟨final, trace, pc, heap, stack, output, running, _, regs⟩ := WorklistFIFO.header_test_execution
    program base fetch done bucket (queueStart (n := n) base + queue.length) (queueStart (n := n) base + queue.length)
    state fetchAt headBound headCell tailBound tailCell initial.position initial.running capacity initial.room pointerFits pointerFits
  have retained : PrefixFrame prefixSize state.heap final.heap := by
    rw [heap]
    exact Controller.Cost.ForestZeroBackendFrame.refl state.heap prefixBound
  refine ⟨final, trace, ?_, congrArg Array.size heap, stack, output, retained⟩
  refine ⟨?_, ?_, ?_, initial.firedZero, ?_, ?_,
    (regs 2 (by decide) (by decide) (by decide)).trans initial.zero,
    (regs 5 (by decide) (by decide) (by decide)).trans initial.one,
    (regs 6 (by decide) (by decide) (by decide)).trans initial.decrement,
    by simpa only [ite_true] using pc, running, ?_⟩
  · simpa only [heap] using initial.spine
  · simpa only [heap] using initial.fifo
  · intro index; simpa only [heap, List.take_length] using initial.rows index
  · simpa only [heap] using initial.headValue
  · simpa only [heap] using initial.tailValue
  · simpa only [heap] using initial.room

theorem fifo_cycle (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base fetch done bucket advance ready skip conflict : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (fired : Fin clauses.length → Bool) (state : State width 8)
    (initial : Ready clauses recordStart recordEnd base fetch queue head fired state)
    (nonempty : head < queue.length)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch done bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ active finalQueue final ticks,
      queue[head]? = some active ∧ queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧ finalQueue.take head = queue.take head ∧
      ticks ≤ 32 * matching (IndexScan.occurrences clauses recordStart) active (IndexScan.occurrences clauses recordStart).length +
        3 * (finalQueue.length - queue.length) + 20 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧ PrefixFrame prefixSize state.heap final.heap ∧
      (final.pc = word width conflict ∨
        ∃ finalFired, Ready clauses recordStart recordEnd base fetch finalQueue (head + 1) finalFired final ∧
          finalQueue.take (head + 1) = queue.take head ++ [active]) := by
  obtain ⟨active, fetchedState, activeValue, first, snapshot, fetchedSize, fetchedStack, fetchedOutput, fetchedHead, firstFrame⟩ :=
    fetch_execution prefixSize clauses recordStart recordEnd base fetch done bucket program queue head fired state
      initial.spine initial.fifo initial.rows initial.firedZero nonempty initial.headValue initial.tailValue separated fetchAt
      initial.zero initial.one initial.decrement initial.position initial.running fetchCapacity initial.room prefixBound prefixBelow
  obtain ⟨finalQueue, bucketState, bucketTicks, growth, unique, processedPrefix, charged, middle, bucketSize, bucketStack,
      bucketOutput, bucketRunning, middleFrame, outcome⟩ := Controller.Cost.ForestZeroFIFOFrame.bucket_head_charged prefixSize clauses recordStart recordEnd base bucket advance ready skip conflict program
        head active separated loopAt readyAt bucketCapacity readyCapacity (IndexScan.occurrences clauses recordStart).length
        queue [] fired fetchedState snapshot (by simpa only [fetchedSize] using prefixBound) prefixBelow
  have fetchedLive : fetchedState.liveWords = state.liveWords := by
    unfold State.liveWords; rw [fetchedSize, fetchedStack, fetchedOutput]
  have bucketLive : bucketState.liveWords = state.liveWords := by
    unfold State.liveWords; rw [bucketSize, bucketStack, bucketOutput, fetchedSize, fetchedStack, fetchedOutput]
  rcases outcome with conflictPC | ⟨visited, finalFired, advancePC, invariant, firedZero, tail, zero, one, decrement, header⟩
  · refine ⟨active, finalQueue, bucketState, 14 + bucketTicks, activeValue, growth, unique, processedPrefix, by omega, ?_,
      bucketSize.trans fetchedSize, bucketStack.trans fetchedStack, bucketOutput.trans fetchedOutput, bucketRunning,
      Controller.Cost.ForestZeroBackendFrame.trans firstFrame middleFrame, Or.inl conflictPC⟩
    simpa only [fetchedLive, Nat.max_self] using first.append middle
  · have nextHead : head + 1 ≤ finalQueue.length := by
      obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp invariant.activeCurrent.symm
      omega
    have headBound : headSlot (n := n) base < bucketState.heap.size := by have := invariant.fifo.fits; unfold headSlot; omega
    have currentHead : bucketState.heap[headSlot (n := n) base]? = some (word width (queueStart (n := n) base + head)) := header.trans fetchedHead
    have headCell : bucketState.heap[headSlot (n := n) base]'headBound = word width (queueStart (n := n) base + head) := by
      simpa only [Array.getElem?_eq_getElem headBound, Option.some.injEq] using currentHead
    have nextFits : queueStart (n := n) base + head + 1 < 2 ^ width := by
      have := invariant.fifo.queue.fits
      have bucketRoom : bucketState.heap.size < 2 ^ width := by simpa only [bucketSize, fetchedSize] using initial.room
      omega
    obtain ⟨final, last, heap, _, regs, size, stack, output, pc, running⟩ := WorklistFIFO.head_advance_execution
      program base advance fetch (queueStart (n := n) base + head) bucketState advanceAt headBound headCell one zero
      advancePC bucketRunning advanceCapacity (by simpa only [bucketSize, fetchedSize] using initial.room) nextFits
    have lastFrame : PrefixFrame prefixSize bucketState.heap final.heap := by
      rw [heap]
      exact Controller.Cost.ForestZeroBackendFrame.store bucketState.heap (headSlot (n := n) base)
        (word width (queueStart (n := n) base + head + 1)) headBound
        (by unfold headSlot; omega) (by simpa only [bucketSize, fetchedSize] using prefixBound)
    have retained := Controller.Cost.ForestZeroBackendFrame.trans
      (Controller.Cost.ForestZeroBackendFrame.trans firstFrame middleFrame) lastFrame
    have completedRows := WorklistBucketComplete.rows_after_head clauses recordStart recordEnd base finalQueue head active visited finalFired bucketState.heap invariant none
    have completedZero := WorklistBucketComplete.fired_after_head clauses recordStart recordEnd base finalQueue head active visited finalFired bucketState.heap invariant firedZero none
    have baselineRows : ∀ index : Fin clauses.length,
        MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
          (remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (finalQueue.take (head + 1))) (finalFired index) bucketState.heap := by
      simpa only [processedForRow, List.not_mem_nil, ite_false, List.append_nil] using completedRows
    obtain ⟨finalSpine, finalFifo, finalRows⟩ := WorklistFIFO.head_store_frame clauses recordStart recordEnd base finalQueue
      (fun index => remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (finalQueue.take (head + 1)))
      finalFired bucketState.heap (word width (queueStart (n := n) base + head + 1)) invariant.spine invariant.fifo baselineRows separated
    have finalHead : final.heap[headSlot (n := n) base]? = some (word width (queueStart (n := n) base + (head + 1))) := by
      rw [heap]
      simp only [Array.getElem?_set_self, Nat.add_assoc]
    have finalTail : final.heap[tailSlot (n := n) base]? = some (word width (queueStart (n := n) base + finalQueue.length)) := by
      rw [heap]
      exact (Array.getElem?_set_ne headBound (by unfold headSlot tailSlot; omega)).trans tail
    have finalReady : Ready clauses recordStart recordEnd base fetch finalQueue (head + 1) finalFired final := by
      refine ⟨?_, ?_, nextHead, ?_, completedZero, finalHead, finalTail,
        (regs 2 (by decide) (by decide)).trans zero, (regs 5 (by decide) (by decide)).trans one,
        (regs 6 (by decide) (by decide)).trans decrement, pc, running, ?_⟩
      · simpa only [heap] using finalSpine
      · simpa only [heap] using finalFifo
      · intro index; simpa only [heap] using finalRows index
      · simpa only [size, bucketSize, fetchedSize] using initial.room
    refine ⟨active, finalQueue, final, 14 + bucketTicks + 5, activeValue, growth, unique, processedPrefix, by omega, ?_,
      size.trans (bucketSize.trans fetchedSize), stack.trans (bucketStack.trans fetchedStack),
      output.trans (bucketOutput.trans fetchedOutput), running, retained, Or.inr ⟨finalFired, finalReady, ?_⟩⟩
    · simpa only [fetchedLive, bucketLive, Nat.max_self] using (first.append middle).append last
    · rw [List.take_add_one, ← invariant.activeCurrent, processedPrefix]
      rfl

theorem fifo_runtime (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base fetch done bucket advance ready skip conflict : Nat) (program : Program width 8)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch done bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (budget head : Nat) (queue : List (Fin n)) (fired : Fin clauses.length → Bool) (state : State width 8)
    (capacityLedger : head + budget = n)
    (initial : Ready clauses recordStart recordEnd base fetch queue head fired state)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ finalQueue finalFired final ticks,
      queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧
      ticks ≤ 32 * pendingIncidences (IndexScan.occurrences clauses recordStart) (queue.take head) +
        20 * budget + 3 * (finalQueue.length - queue.length) + 6 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧ PrefixFrame prefixSize state.heap final.heap ∧
      (final.pc = word width conflict ∨ Done clauses recordStart recordEnd base done finalQueue finalFired final) := by
  induction budget generalizing head queue fired state with
  | zero =>
    have queueBound := Controller.Horn.WorklistMark.enqueue_bound queue initial.fifo.nodup
    have equal : head = queue.length := by have := initial.headBound; omega
    have atEnd : Ready clauses recordStart recordEnd base fetch queue queue.length fired state := by simpa only [equal] using initial
    obtain ⟨final, trace, finished, size, stack, output, frame⟩ := fifo_empty prefixSize clauses recordStart recordEnd base fetch done bucket program queue fired state atEnd fetchAt fetchCapacity prefixBound
    exact ⟨queue, fired, final, 6, Nat.le_refl _, initial.fifo.nodup, by omega, trace, size, stack, output,
      finished.running, frame, Or.inr finished⟩
  | succ budget ih =>
    by_cases equal : head = queue.length
    · have atEnd : Ready clauses recordStart recordEnd base fetch queue queue.length fired state := by simpa only [equal] using initial
      obtain ⟨final, trace, finished, size, stack, output, frame⟩ := fifo_empty prefixSize clauses recordStart recordEnd base fetch done bucket program queue fired state atEnd fetchAt fetchCapacity prefixBound
      exact ⟨queue, fired, final, 6, Nat.le_refl _, initial.fifo.nodup, by omega, trace, size, stack, output,
        finished.running, frame, Or.inr finished⟩
    · have nonempty : head < queue.length := by have := initial.headBound; omega
      obtain ⟨active, nextQueue, middle, firstTicks, activeValue, growth, unique, prefixEqual, firstBound, first,
          middleSize, middleStack, middleOutput, middleRunning, firstFrame, outcome⟩ := fifo_cycle prefixSize clauses recordStart recordEnd base
        fetch done bucket advance ready skip conflict program queue head fired state initial nonempty separated fetchAt advanceAt
        loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity prefixBound prefixBelow
      have fresh : active ∉ queue.take head := by
        have taken : (queue.take (head + 1)).Nodup := initial.fifo.nodup.take
        rw [List.take_add_one, activeValue] at taken
        have disjoint := (List.nodup_append.mp taken).2.2
        intro member
        exact disjoint active member active (by simp) rfl
      have partition := incidence_partition (IndexScan.occurrences clauses recordStart) (queue.take head) active fresh
      rcases outcome with conflictPC | ⟨nextFired, nextReady, promoted⟩
      · exact ⟨nextQueue, fired, middle, firstTicks, growth, unique, by omega, first,
          middleSize, middleStack, middleOutput, middleRunning, firstFrame, Or.inl conflictPC⟩
      · obtain ⟨finalQueue, finalFired, final, lastTicks, lastGrowth, finalUnique, lastBound, last,
          finalSize, finalStack, finalOutput, finalRunning, lastFrame, result⟩ := ih (head + 1) nextQueue nextFired middle (by omega) nextReady (by simpa only [middleSize] using prefixBound)
        have potential : pendingIncidences (IndexScan.occurrences clauses recordStart) (nextQueue.take (head + 1)) +
            matching (IndexScan.occurrences clauses recordStart) active (IndexScan.occurrences clauses recordStart).length =
            pendingIncidences (IndexScan.occurrences clauses recordStart) (queue.take head) := by
          rw [promoted]
          exact partition.symm
        have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, finalFired, final, firstTicks + lastTicks, by omega, finalUnique, by omega, ?_,
          finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, finalRunning, Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame, result⟩
        simpa only [middleLive, Nat.max_self] using first.append last

theorem fifo_linear_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base fetch done bucket advance ready skip conflict : Nat) (program : Program width 8)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch done bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (head : Nat) (queue : List (Fin n)) (fired : Fin clauses.length → Bool) (state : State width 8)
    (initial : Ready clauses recordStart recordEnd base fetch queue head fired state)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ finalQueue finalFired final ticks,
      finalQueue.Nodup ∧ ticks ≤ 32 * (IndexScan.occurrences clauses recordStart).length + 23 * n + 6 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧ PrefixFrame prefixSize state.heap final.heap ∧
      (final.pc = word width conflict ∨ Done clauses recordStart recordEnd base done finalQueue finalFired final) := by
  have queueBound := Controller.Horn.WorklistMark.enqueue_bound queue initial.fifo.nodup
  have headBound : head ≤ n := by have := initial.headBound; omega
  obtain ⟨finalQueue, finalFired, final, ticks, growth, unique, charged, trace, size, stack, output, running, frame, result⟩ :=
    fifo_runtime prefixSize clauses recordStart recordEnd base fetch done bucket advance ready skip conflict program separated fetchAt advanceAt loopAt readyAt
      fetchCapacity advanceCapacity bucketCapacity readyCapacity (n - head) head queue fired state (by omega) initial prefixBound prefixBelow
  have finalBound := Controller.Horn.WorklistMark.enqueue_bound finalQueue unique
  have incidences := incidence_bound (IndexScan.occurrences clauses recordStart) (queue.take head)
  exact ⟨finalQueue, finalFired, final, ticks, unique, by omega, trace, size, stack, output, running, frame, result⟩

end Controller.Cost.ForestZeroFIFORun
