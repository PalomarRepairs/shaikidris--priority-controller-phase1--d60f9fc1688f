module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistOutcome
public import Controller.Cost.ForestZeroFIFORun
public import Controller.Cost.ForestZeroSeedCaller

@[expose] public section

/-! Actual FIFO transitions retain the caller source prefix and the semantic
invariants needed to justify both conflict and model outcomes. -/
set_option autoImplicit false

namespace Controller.Cost.ForestZeroOutcome
open Controller.Horn Controller.Horn.WorklistOutcome Controller.Horn.WorklistSeed
open Controller.Cost Controller.Cost.ForestZeroBackendFrame
open Controller.Horn.WorklistPropagation Controller.Horn.WorklistFIFORun
open Controller.Horn.WorklistBucketSuccessor Controller.Horn.WorklistPropagationStep
open Controller.Horn.WorklistBucketRun Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketReady Controller.Horn.WorklistBucketFrame
open Controller.Horn.WorklistBucketNegative Controller.Horn.WorklistBucketCharge
variable {width n : Nat}

theorem semantic_step (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (bound : Nat) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state)
    (complete : ProcessedComplete clauses recordStart queue head (some active) visited fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
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
      ProcessedComplete clauses recordStart nextQueue head (some active) nextVisited nextFired ∧
      FiredMeaning clauses nextQueue nextFired ∧ QueueForced clauses nextQueue ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]? ∧
      PrefixFrame prefixSize state.heap final.heap) ∨
    (∃ final, Execution program state final 15 state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width conflict ∧ final.halted = false ∧
      (¬ ∃ assignment : Fin n → Bool, ∀ other : Fin clauses.length,
        (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment) ∧
      PrefixFrame prefixSize state.heap final.heap) := by
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
  have fresh := invariant.activeFresh active (by simp)
  obtain ⟨indices, mapRows, path⟩ := invariant.path active (by simp)
  have unvisited : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∉ visited := by
    simpa only [sourceRow, ← mapRows] using current_row_unvisited clauses recordStart recordEnd active indices current
      path label invariant.spine.positiveEnd
  by_cases countZero : rowCounts clauses recordStart queue head active visited index - 1 = 0
  · have predecessorPositive := Controller.Horn.WorklistPropagationStep.fresh_visit_positive
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
      obtain ⟨final, trace, _, size, stack, output, pc, running, retained⟩ :=
        ForestZeroFIFOFrame.conflict_iteration prefixSize program entry exit ready base skip conflict
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
          (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
          (recordEnd + 2 * current.val) labels state linked selected loopAt readyAt
          (by have := invariant.spine.positiveEnd; omega) held snapshot.one snapshot.zero snapshot.decrement
          snapshot.position snapshot.running capacity readyCapacity snapshot.room prefixBound
          (by unfold Controller.Horn.NormalizeLoop.recordOffset; omega)
      refine Or.inr ⟨final, trace, size, stack, output, pc, running, ?_, retained⟩
      apply processed_positive_conflict clauses recordStart queue head (some active)
        (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
        index labels ruleEq invariant.activeQueued ?_ forced
      have counts := visited_count_successor clauses recordStart queue head active visited index
        unvisited sourceIncident fresh index
      rw [counts, ite_eq_left rfl]
      change rowCounts clauses recordStart queue head active visited index - 1 = 0
      exact countZero
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
          size, stack, output, pc, running, headForced, headFrame, retained⟩ := ForestZeroFIFOFrame.negative_head_successor
        prefixSize clauses recordStart recordEnd base entry exit ready skip conflict program queue head active forcedHead labels
        visited fired index current state invariant snapshot.firedZero ruleEq sourceRow label countZero separated loopAt readyAt
        tailBound tailValue held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running
        capacity readyCapacity snapshot.room prefixBound prefixBelow
      refine Or.inl ⟨Controller.Horn.WorklistBucketReady.queueAfter queue forcedHead,
        visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
        (fun other => if other = index then true else fired other), current.val, final,
        (if forcedHead ∈ queue then 32 else 35), less, charged, (queue_growth queue forcedHead).1,
        queue_after_take queue forcedHead head invariant.headBound, ?_, trace, ?_, ?_, ?_, ?_, size, stack, output, headFrame, retained⟩
      · exact (negative_cost queue forcedHead).le
      · exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
          decrement, pc, running, by simpa only [size] using snapshot.room⟩
      · exact enqueue_complete clauses recordStart queue head (some active) _ _ forcedHead
          invariant.headBound (fired_complete clauses recordStart queue head active visited fired index
            complete unvisited sourceIncident fresh)
      · exact negative_fired_meaning clauses queue fired index forcedHead labels ruleEq meaning
      · apply Controller.Horn.WorklistSeed.queue_after_forced clauses queue forcedHead forced
        intro assignment models
        apply headForced assignment (forced assignment models)
        simpa only [ruleEq] using models index
  · have positiveCount : 0 < rowCounts clauses recordStart queue head active visited index - 1 := by omega
    obtain ⟨final, trace, nextInvariant, nextFired, next, zero, one, decrement, tail,
        size, stack, output, pc, running⟩ := nonzero_tail clauses recordStart recordEnd base entry exit ready program
      queue head active visited fired index current state invariant snapshot.firedZero sourceRow label positiveCount
      separated loopAt snapshot.tail held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running capacity snapshot.room
    have headFrame := nonzero_head_frame clauses recordStart recordEnd base entry exit ready program queue head active visited fired
      index current state final invariant sourceRow label positiveCount separated loopAt held snapshot.one snapshot.zero
      snapshot.decrement snapshot.position snapshot.running capacity snapshot.room trace
    have retained := ForestZeroFIFOFrame.nonzero_prefix_frame prefixSize clauses recordStart recordEnd base entry exit ready
      program queue head active visited fired index current state final invariant sourceRow label positiveCount separated loopAt
      held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running capacity snapshot.room trace prefixBound prefixBelow
    refine Or.inl ⟨queue, visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
      fired, current.val, final, 12, less, charged, Nat.le_refl _, rfl, by omega, trace, ?_, ?_, ?_, ?_, size, stack, output, headFrame, retained⟩
    · exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
      decrement, pc, running, by simpa only [size] using snapshot.room⟩
    · apply nonzero_complete clauses recordStart queue head active visited fired index
        complete unvisited sourceIncident fresh
      change 1 < rowCounts clauses recordStart queue head active visited index
      omega
    · exact meaning
    · exact forced

theorem semantic_bucket (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (head : Nat) (active : Fin n)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (bound : Nat) (queue : List (Fin n)) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state)
    (complete : ProcessedComplete clauses recordStart queue head (some active) visited fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ finalQueue final ticks,
      queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧ finalQueue.take head = queue.take head ∧
      ticks ≤ 32 * matching (IndexScan.occurrences clauses recordStart) active bound +
        3 * (finalQueue.length - queue.length) + 1 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      ((final.pc = word width conflict ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ other : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment) ∨
        ∃ finalVisited finalFired,
          final.pc = word width exit ∧
          Invariant clauses recordStart recordEnd base finalQueue head (some active) finalVisited 0 finalFired final.heap ∧
          FiredZero clauses recordStart finalQueue head (some active) finalVisited finalFired ∧
          final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
            some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + finalQueue.length)) ∧
          final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
          final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]? ∧
          ProcessedComplete clauses recordStart finalQueue head (some active) finalVisited finalFired ∧
          FiredMeaning clauses finalQueue finalFired ∧ QueueForced clauses finalQueue) ∧
      PrefixFrame prefixSize state.heap final.heap := by
  induction bound using Nat.strong_induction_on generalizing queue visited fired state with
  | h bound ih =>
    by_cases nil : IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take bound) active = 0
    · have invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired state.heap := by
        simpa only [nil] using snapshot.invariant
      have held : state.reg 0 = word width 0 := by simpa only [nil] using snapshot.held
      obtain ⟨final, trace, finalInvariant, finalFired, registers, heap, stack, output, pc, running⟩ :=
        nil_endpoint clauses recordStart recordEnd base entry exit ready program queue head active visited fired state
          invariant snapshot.firedZero loopAt held snapshot.position snapshot.running capacity
      refine ⟨queue, final, 1, Nat.le_refl _, invariant.fifo.nodup, rfl, by omega, trace,
        by simpa only [heap], stack, output, running,
        Or.inr ⟨visited, fired, pc, finalInvariant, finalFired, ?_, ?_, ?_, ?_, ?_, complete, meaning, forced⟩, ?_⟩
      · simpa only [heap] using snapshot.tail
      · exact (congrFun registers 2).trans snapshot.zero
      · exact (congrFun registers 5).trans snapshot.one
      · exact (congrFun registers 6).trans snapshot.decrement
      · exact congrArg (fun heap : Array (Word width) => heap[headSlot (n := n) base]?) heap
      · simpa only [heap] using (Controller.Cost.ForestZeroBackendFrame.refl state.heap prefixBound)
    · have matchingPositive : 0 < matching (IndexScan.occurrences clauses recordStart) active bound := by
        rcases head_frontier (IndexScan.occurrences clauses recordStart) recordEnd
          snapshot.invariant.spine.positiveEnd active bound snapshot.within with zero | ⟨index, less, label, pointer⟩
        · contradiction
        · have charged := matching_predecessor (IndexScan.occurrences clauses recordStart) recordEnd
            snapshot.invariant.spine.positiveEnd active bound snapshot.within index less label pointer
          omega
      rcases semantic_step prefixSize clauses recordStart recordEnd base entry exit ready skip conflict program queue head active
        visited fired bound state snapshot complete meaning forced nil separated loopAt readyAt capacity readyCapacity prefixBound prefixBelow with continued | failed
      · obtain ⟨nextQueue, nextVisited, nextFired, nextBound, middle, firstTicks,
          smaller, matchingStep, growth, middlePrefix, firstBound, first, middleSnapshot, middleComplete, middleMeaning, middleForced, middleSize, middleStack, middleOutput, middleHead, middleFrame⟩ := continued
        obtain ⟨finalQueue, final, lastTicks, lastGrowth, unique, finalPrefix, lastBound, last,
            finalSize, finalStack, finalOutput, running, outcome, lastFrame⟩ :=
          ih nextBound smaller nextQueue nextVisited nextFired middle middleSnapshot middleComplete middleMeaning middleForced (by simpa only [middleSize] using prefixBound)
        have middleLive : middle.liveWords = state.liveWords := by
          unfold State.liveWords
          rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, final, firstTicks + lastTicks, by omega, unique, finalPrefix.trans middlePrefix, by omega,
          ?_, finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, running, ?_, Controller.Cost.ForestZeroBackendFrame.trans middleFrame lastFrame⟩
        · simpa only [middleLive, Nat.max_self] using first.append last
        · rcases outcome with failed | ⟨finalVisited, finalFired, pc, invariant, firedZero, tail, zero, one, decrement, header, finalComplete, finalMeaning, finalForced⟩
          · exact Or.inl failed
          · exact Or.inr ⟨finalVisited, finalFired, pc, invariant, firedZero, tail, zero, one, decrement, header.trans middleHead, finalComplete, finalMeaning, finalForced⟩
      · obtain ⟨final, trace, size, stack, output, pc, running, noModels, retained⟩ := failed
        exact ⟨queue, final, 15, Nat.le_refl _, snapshot.invariant.fifo.nodup, rfl,
          by omega, trace, size, stack, output, running, Or.inl ⟨pc, noModels⟩, retained⟩

theorem semantic_cycle (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base fetch done bucket advance ready skip conflict : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (fired : Fin clauses.length → Bool) (state : State width 8)
    (initial : Ready clauses recordStart recordEnd base fetch queue head fired state)
    (complete : ProcessedComplete clauses recordStart queue head none [] fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
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
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      ((final.pc = word width conflict ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ other : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment) ∨
        ∃ finalFired, Ready clauses recordStart recordEnd base fetch finalQueue (head + 1) finalFired final ∧
          finalQueue.take (head + 1) = queue.take head ++ [active] ∧
          ProcessedComplete clauses recordStart finalQueue (head + 1) none [] finalFired ∧
          FiredMeaning clauses finalQueue finalFired ∧ QueueForced clauses finalQueue) ∧
      PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨active, fetchedState, activeValue, first, snapshot, fetchedSize, fetchedStack, fetchedOutput, fetchedHead, firstFrame⟩ :=
    ForestZeroFIFORun.fetch_execution prefixSize clauses recordStart recordEnd base fetch done bucket program queue head fired state
      initial.spine initial.fifo initial.rows initial.firedZero nonempty initial.headValue initial.tailValue separated fetchAt
      initial.zero initial.one initial.decrement initial.position initial.running fetchCapacity initial.room prefixBound prefixBelow
  obtain ⟨finalQueue, bucketState, bucketTicks, growth, unique, processedPrefix, charged, middle, bucketSize, bucketStack,
      bucketOutput, bucketRunning, outcome, middleFrame⟩ := semantic_bucket prefixSize clauses recordStart recordEnd base bucket advance ready skip conflict program
        head active separated loopAt readyAt bucketCapacity readyCapacity (IndexScan.occurrences clauses recordStart).length
        queue [] fired fetchedState snapshot
        (by simpa [ProcessedComplete, processedForRow] using complete) meaning forced (by simpa only [fetchedSize] using prefixBound) prefixBelow
  have fetchedLive : fetchedState.liveWords = state.liveWords := by
    unfold State.liveWords; rw [fetchedSize, fetchedStack, fetchedOutput]
  have bucketLive : bucketState.liveWords = state.liveWords := by
    unfold State.liveWords; rw [bucketSize, bucketStack, bucketOutput, fetchedSize, fetchedStack, fetchedOutput]
  rcases outcome with conflictPC | ⟨visited, finalFired, advancePC, invariant, firedZero, tail, zero, one, decrement, header, bucketComplete, finalMeaning, finalForced⟩
  · refine ⟨active, finalQueue, bucketState, 14 + bucketTicks, activeValue, growth, unique, processedPrefix, by omega, ?_,
      bucketSize.trans fetchedSize, bucketStack.trans fetchedStack, bucketOutput.trans fetchedOutput, bucketRunning, Or.inl conflictPC, Controller.Cost.ForestZeroBackendFrame.trans firstFrame middleFrame⟩
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
      exact Controller.Cost.ForestZeroBackendFrame.store bucketState.heap
        (headSlot (n := n) base) (word width (queueStart (n := n) base + head + 1))
        headBound (by unfold headSlot; omega) middleFrame.2.1
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
      output.trans (bucketOutput.trans fetchedOutput), running, Or.inr ⟨finalFired, finalReady, ?_, ?_, finalMeaning, finalForced⟩,
      Controller.Cost.ForestZeroBackendFrame.trans
        (Controller.Cost.ForestZeroBackendFrame.trans firstFrame middleFrame) lastFrame⟩
    · simpa only [fetchedLive, bucketLive, Nat.max_self] using (first.append middle).append last
    · rw [List.take_add_one, ← invariant.activeCurrent, processedPrefix]
      rfl
    · intro index enabled countZero
      apply bucketComplete index enabled
      rw [WorklistBucketComplete.completed_counts clauses recordStart recordEnd base finalQueue head active
        visited finalFired bucketState.heap invariant index]
      simpa [processedForRow] using countZero

theorem semantic_runtime (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
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
    (complete : ProcessedComplete clauses recordStart queue head none [] fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ finalQueue finalFired final ticks,
      queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧
      ticks ≤ 32 * pendingIncidences (IndexScan.occurrences clauses recordStart) (queue.take head) +
        20 * budget + 3 * (finalQueue.length - queue.length) + 6 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      ((final.pc = word width conflict ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ other : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment) ∨
        (Done clauses recordStart recordEnd base done finalQueue finalFired final ∧
          EnabledComplete clauses finalQueue finalFired ∧
          FiredMeaning clauses finalQueue finalFired ∧ QueueForced clauses finalQueue)) ∧
      PrefixFrame prefixSize state.heap final.heap := by
  induction budget generalizing head queue fired state with
  | zero =>
    have queueBound := Controller.Horn.WorklistMark.enqueue_bound queue initial.fifo.nodup
    have equal : head = queue.length := by have := initial.headBound; omega
    have atEnd : Ready clauses recordStart recordEnd base fetch queue queue.length fired state := by simpa only [equal] using initial
    obtain ⟨final, trace, finished, size, stack, output, retained⟩ := ForestZeroFIFORun.fifo_empty prefixSize clauses recordStart recordEnd base fetch done bucket program queue fired state atEnd fetchAt fetchCapacity prefixBound
    exact ⟨queue, fired, final, 6, Nat.le_refl _, initial.fifo.nodup, by omega, trace, size, stack, output,
      finished.running, Or.inr ⟨finished,
        empty_complete clauses recordStart queue fired (by simpa only [equal] using complete), meaning, forced⟩, retained⟩
  | succ budget ih =>
    by_cases equal : head = queue.length
    · have atEnd : Ready clauses recordStart recordEnd base fetch queue queue.length fired state := by simpa only [equal] using initial
      obtain ⟨final, trace, finished, size, stack, output, retained⟩ := ForestZeroFIFORun.fifo_empty prefixSize clauses recordStart recordEnd base fetch done bucket program queue fired state atEnd fetchAt fetchCapacity prefixBound
      exact ⟨queue, fired, final, 6, Nat.le_refl _, initial.fifo.nodup, by omega, trace, size, stack, output,
        finished.running, Or.inr ⟨finished,
        empty_complete clauses recordStart queue fired (by simpa only [equal] using complete), meaning, forced⟩, retained⟩
    · have nonempty : head < queue.length := by have := initial.headBound; omega
      obtain ⟨active, nextQueue, middle, firstTicks, activeValue, growth, unique, prefixEqual, firstBound, first,
          middleSize, middleStack, middleOutput, middleRunning, outcome, firstFrame⟩ := semantic_cycle prefixSize clauses recordStart recordEnd base
        fetch done bucket advance ready skip conflict program queue head fired state initial complete meaning forced nonempty separated fetchAt advanceAt
        loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity prefixBound prefixBelow
      have fresh : active ∉ queue.take head := by
        have taken : (queue.take (head + 1)).Nodup := initial.fifo.nodup.take
        rw [List.take_add_one, activeValue] at taken
        have disjoint := (List.nodup_append.mp taken).2.2
        intro member
        exact disjoint active member active (by simp) rfl
      have partition := incidence_partition (IndexScan.occurrences clauses recordStart) (queue.take head) active fresh
      rcases outcome with conflictPC | ⟨nextFired, nextReady, promoted, nextComplete, nextMeaning, nextForced⟩
      · exact ⟨nextQueue, fired, middle, firstTicks, growth, unique, by omega, first,
          middleSize, middleStack, middleOutput, middleRunning, Or.inl conflictPC, firstFrame⟩
      · obtain ⟨finalQueue, finalFired, final, lastTicks, lastGrowth, finalUnique, lastBound, last,
          finalSize, finalStack, finalOutput, finalRunning, result, lastFrame⟩ := ih (head + 1) nextQueue nextFired middle (by omega) nextReady nextComplete nextMeaning nextForced (by simpa only [middleSize] using prefixBound)
        have potential : pendingIncidences (IndexScan.occurrences clauses recordStart) (nextQueue.take (head + 1)) +
            matching (IndexScan.occurrences clauses recordStart) active (IndexScan.occurrences clauses recordStart).length =
            pendingIncidences (IndexScan.occurrences clauses recordStart) (queue.take head) := by
          rw [promoted]
          exact partition.symm
        have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, finalFired, final, firstTicks + lastTicks, by omega, finalUnique, by omega, ?_,
          finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, finalRunning, result,
          Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame⟩
        simpa only [middleLive, Nat.max_self] using first.append last

theorem semantic_linear_execution (prefixSize : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
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
    (complete : ProcessedComplete clauses recordStart queue head none [] fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ finalQueue finalFired final ticks,
      finalQueue.Nodup ∧ ticks ≤ 32 * (IndexScan.occurrences clauses recordStart).length + 23 * n + 6 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      ((final.pc = word width conflict ∧
        ¬ ∃ assignment : Fin n → Bool, ∀ other : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment) ∨
        (Done clauses recordStart recordEnd base done finalQueue finalFired final ∧
          EnabledComplete clauses finalQueue finalFired ∧
          FiredMeaning clauses finalQueue finalFired ∧ QueueForced clauses finalQueue)) ∧
      PrefixFrame prefixSize state.heap final.heap := by
  have queueBound := Controller.Horn.WorklistMark.enqueue_bound queue initial.fifo.nodup
  have headBound : head ≤ n := by have := initial.headBound; omega
  obtain ⟨finalQueue, finalFired, final, ticks, growth, unique, charged, trace, size, stack, output, running, result, frame⟩ :=
    semantic_runtime prefixSize clauses recordStart recordEnd base fetch done bucket advance ready skip conflict program separated fetchAt advanceAt loopAt readyAt
      fetchCapacity advanceCapacity bucketCapacity readyCapacity (n - head) head queue fired state (by omega) initial complete meaning forced prefixBound prefixBelow
  have finalBound := Controller.Horn.WorklistMark.enqueue_bound finalQueue unique
  have incidences := incidence_bound (IndexScan.occurrences clauses recordStart) (queue.take head)
  exact ⟨finalQueue, finalFired, final, ticks, unique, by omega, trace, size, stack, output, running, result, frame⟩

theorem original_formula_execution (prefixSize : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordStart recordEnd base fetch done bucket advance ready skip conflict : Nat) (program : Program width 8)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (fetchAt : WorklistFIFO.FetchAt (n := n) program base fetch done bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := n) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := n) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (head : Nat) (queue : List (Fin n)) (fired : Fin (formula.clauses.toList).length → Bool) (state : State width 8)
    (initial : Ready (formula.clauses.toList) recordStart recordEnd base fetch queue head fired state)
    (complete : ProcessedComplete (formula.clauses.toList) recordStart queue head none [] fired)
    (meaning : FiredMeaning (formula.clauses.toList) queue fired) (forced : QueueForced (formula.clauses.toList) queue)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base) :
    ∃ finalQueue finalFired final ticks,
      finalQueue.Nodup ∧ ticks ≤ 32 * (IndexScan.occurrences (formula.clauses.toList) recordStart).length + 23 * n + 6 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      ((final.pc = word width conflict ∧
        ¬ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∨
        (Done formula.clauses.toList recordStart recordEnd base done finalQueue finalFired final ∧
          Controller.CNF.Satisfies (offAssignment finalQueue) formula ∧
          QueueForced formula.clauses.toList finalQueue)) ∧
      PrefixFrame prefixSize state.heap final.heap := by
  obtain ⟨finalQueue, finalFired, final, ticks, unique, charged, trace, size, stack, output, running, result, frame⟩ :=
    semantic_linear_execution prefixSize formula.clauses.toList recordStart recordEnd base fetch done bucket advance ready skip conflict
      program separated fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
      head queue fired state initial complete meaning forced prefixBound prefixBelow
  refine ⟨finalQueue, finalFired, final, ticks, unique, charged, trace, size, stack, output, running, ?_, frame⟩
  rcases result with ⟨pc, noModels⟩ | ⟨finished, finalComplete, finalMeaning, finalForced⟩
  · refine Or.inl ⟨pc, ?_⟩
    rintro ⟨assignment, model⟩
    exact noModels ⟨assignment, (original_models_iff formula dual assignment).mpr model⟩
  · exact Or.inr ⟨finished, (original_models_iff formula dual (offAssignment finalQueue)).mp
      (terminal_original_models formula.clauses.toList finalQueue finalFired finalComplete finalMeaning), finalForced⟩

theorem initialized_original_execution (prefixSize : Nat) (formula : Controller.CNF.Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Stored ([] : List (Fin n)) base state.heap)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := n) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := n) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : prefixSize ≤ state.heap.size) (prefixBelow : prefixSize ≤ base)
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
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width) :
    ∃ finalQueue final ticks,
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (IndexScan.occurrences formula.clauses.toList recordStart).length + 26 * n + 24 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      PrefixFrame prefixSize state.heap final.heap ∧
      ((final.pc = word width conflict ∧ final.halted = false ∧
        ¬ ∃ assignment : Fin n → Bool, Controller.CNF.Satisfies assignment formula) ∨
        (∃ finalFired, Done formula.clauses.toList recordStart recordEnd base fifoDone finalQueue finalFired final ∧
          Controller.CNF.Satisfies (offAssignment finalQueue) formula ∧
          QueueForced formula.clauses.toList finalQueue)) := by
  obtain ⟨queue, fired, middle, firstTicks, queueBound, firstBound, first, middleSize, middleStack, middleOutput, firstFrame, outcome⟩ :=
    ForestZeroSeedCaller.initialized_fifo_execution prefixSize formula.clauses.toList recordHeader recordStart recordEnd base entry scan seedDone conflict
      state program physical header fifo separated setupAt scanAt position running zero one room setupCapacity scanCapacity
      prefixBound prefixBelow fetch headAt headCapacity
  rcases outcome with ⟨pc, running, noModels⟩ | ⟨initial, complete, meaning, forced⟩
  · refine ⟨queue, middle, firstTicks, by omega, first, middleSize, middleStack, middleOutput, firstFrame,
      Or.inl ⟨pc, running, ?_⟩⟩
    rintro ⟨assignment, model⟩
    exact noModels ⟨assignment, (original_models_iff formula dual assignment).mpr model⟩
  · obtain ⟨finalQueue, finalFired, final, lastTicks, _, lastBound, last, finalSize, finalStack, finalOutput, finalRunning, result, lastFrame⟩ :=
      original_formula_execution prefixSize formula dual recordStart recordEnd base fetch fifoDone bucket advance ready skip conflict program
        separated fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
        0 queue fired middle initial complete meaning forced (by simpa only [middleSize] using prefixBound) prefixBelow
    have middleLive : middle.liveWords = state.liveWords := by
      unfold State.liveWords
      rw [middleSize, middleStack, middleOutput]
    refine ⟨finalQueue, final, firstTicks + lastTicks, by omega, ?_, finalSize.trans middleSize,
      finalStack.trans middleStack, finalOutput.trans middleOutput,
      Controller.Cost.ForestZeroBackendFrame.trans firstFrame lastFrame, ?_⟩
    · simpa only [middleLive, Nat.max_self] using first.append last
    · rcases result with ⟨pc, noModels⟩ | ⟨finished, model, finalForced⟩
      · exact Or.inl ⟨pc, finalRunning, noModels⟩
      · exact Or.inr ⟨finalFired, finished, model, finalForced⟩

end Controller.Cost.ForestZeroOutcome
