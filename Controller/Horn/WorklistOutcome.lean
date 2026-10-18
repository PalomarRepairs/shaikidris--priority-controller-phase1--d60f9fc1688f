module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistFIFORun
public import Controller.Horn.WorklistSeed
public import Controller.Horn.WorklistCorrect

@[expose] public section

/-! The physical FIFO's marked labels describe the returned assignment. Its
terminal rule counts use the processed queue, and its observable result is
compared to the exact normalized-row solver. -/
namespace Controller.Horn.WorklistOutcome
open Controller.CNF Controller.Horn.WorklistPropagation Controller.Horn.WorklistSeed
variable {n width : Nat}

/-- Every declared channel is present, including unused variables. -/
def offAssignment (queue : List (Fin n)) : Fin n → Bool :=
  fun label => decide (label ∉ queue)

/-- An enabled zero-count row has actually fired. This is distinct from the
converse fired-zero invariant carried by the physical bucket kernels. -/
def EnabledComplete (clauses : List (Clause (Fin n))) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) : Prop :=
  ∀ index : Fin clauses.length,
    (Controller.Horn.Worklist.compileClause clauses[index.val]).enabled = true →
    remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) queue = 0 →
    fired index = true

/-- Continuing fired rows are original negative rules whose head is already
marked; a positive zero-count firing follows the conflict branch. -/
def FiredMeaning (clauses : List (Clause (Fin n))) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) : Prop :=
  ∀ index : Fin clauses.length, fired index = true →
    ∃ head labels, Controller.Horn.Worklist.compileClause clauses[index.val] =
      .negative head labels ∧ head ∈ queue

/-- Completion follows processed FIFO labels and the current physical bucket
prefix. Newly enqueued labels do not enter this count. -/
def ProcessedComplete (clauses : List (Clause (Fin n))) (recordStart : Nat)
    (queue : List (Fin n)) (head : Nat) (active : Option (Fin n))
    (visited : List Nat) (fired : Fin clauses.length → Bool) : Prop :=
  ∀ index : Fin clauses.length,
    (Controller.Horn.Worklist.compileClause clauses[index.val]).enabled = true →
    remaining (Controller.Horn.Worklist.compileClause clauses[index.val])
      (processedForRow queue head active visited
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)) = 0 →
    fired index = true

/-- The actual nonzero count decrement preserves completion, using the original
occurrence successor equation checked for the physical linked prefix. -/
theorem nonzero_complete (clauses : List (Clause (Fin n))) (recordStart : Nat)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (index : Fin clauses.length)
    (complete : ProcessedComplete clauses recordStart queue head (some active) visited fired)
    (unvisited : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∉ visited)
    (incident : active ∈ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives)
    (fresh : active ∉ queue.take head)
    (nonzero : 1 < remaining (Controller.Horn.Worklist.compileClause clauses[index.val])
      (processedForRow queue head (some active) visited
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val))) :
    ProcessedComplete clauses recordStart queue head (some active)
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val]) fired := by
  intro other enabled zero
  have counts := Controller.Horn.WorklistBucketSuccessor.visited_count_successor
    clauses recordStart queue head active visited index unvisited incident fresh other
  rw [counts] at zero
  by_cases same : other = index
  · subst other
    rw [ite_eq_left (Eq.refl index)] at zero
    omega
  · rw [ite_eq_right same] at zero
    exact complete other enabled zero

/-- Writing the selected fired tag discharges the newly zero count; every other
original row retains its prior completion obligation. -/
theorem fired_complete (clauses : List (Clause (Fin n))) (recordStart : Nat)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (index : Fin clauses.length)
    (complete : ProcessedComplete clauses recordStart queue head (some active) visited fired)
    (unvisited : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∉ visited)
    (incident : active ∈ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives)
    (fresh : active ∉ queue.take head) :
    ProcessedComplete clauses recordStart queue head (some active)
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
      (fun other => if other = index then true else fired other) := by
  intro other enabled zero
  by_cases same : other = index
  · simp only [ite_eq_left same]
  · have counts := Controller.Horn.WorklistBucketSuccessor.visited_count_successor
      clauses recordStart queue head active visited index unvisited incident fresh other
    rw [counts, ite_eq_right same] at zero
    simp only [ite_eq_right same]
    exact complete other enabled zero

/-- Marking a pending head preserves processed completion because the actual
FIFO head has not advanced. -/
theorem enqueue_complete (clauses : List (Clause (Fin n))) (recordStart : Nat)
    (queue : List (Fin n)) (head : Nat) (active : Option (Fin n)) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (label : Fin n) (bound : head ≤ queue.length)
    (complete : ProcessedComplete clauses recordStart queue head active visited fired) :
    ProcessedComplete clauses recordStart
      (Controller.Horn.WorklistBucketReady.queueAfter queue label) head active visited fired := by
  intro index enabled zero
  rw [Controller.Horn.WorklistBucketNegative.queue_after_processed queue label head
    active visited _ bound] at zero
  exact complete index enabled zero

/-- The selected negative row's stored head becomes a marked label, while the
meaning of every earlier fired tag is preserved by FIFO queue inclusion. -/
theorem negative_fired_meaning (clauses : List (Clause (Fin n)))
    (queue : List (Fin n)) (fired : Fin clauses.length → Bool)
    (index : Fin clauses.length) (label : Fin n) (labels : List (Fin n))
    (original : Controller.Horn.Worklist.compileClause clauses[index.val] = .negative label labels)
    (meaning : FiredMeaning clauses queue fired) :
    FiredMeaning clauses (Controller.Horn.WorklistBucketReady.queueAfter queue label)
      (fun other => if other = index then true else fired other) := by
  intro other marked
  by_cases same : other = index
  · subst other
    refine ⟨label, labels, original, ?_⟩
    by_cases stale : label ∈ queue <;>
      simp [Controller.Horn.WorklistBucketReady.queueAfter, stale]
  · simp only [ite_eq_right same] at marked
    obtain ⟨oldHead, support, originalHead, queued⟩ := meaning other marked
    exact ⟨oldHead, support, originalHead,
      Controller.Horn.WorklistBucketNegative.queue_after_includes queue label oldHead queued⟩

/-- At the fetched empty-FIFO boundary every queued label has been processed,
so processed completion becomes the terminal original-row condition. -/
theorem empty_complete (clauses : List (Clause (Fin n))) (recordStart : Nat)
    (queue : List (Fin n)) (fired : Fin clauses.length → Bool)
    (complete : ProcessedComplete clauses recordStart queue queue.length none [] fired) :
    EnabledComplete clauses queue fired := by
  intro index enabled zero
  apply complete index enabled
  simpa [processedForRow] using zero

/-- A positive row whose actual processed count reaches zero contradicts every
original model once the marked queue is forced false. -/
theorem processed_positive_conflict (clauses : List (Clause (Fin n)))
    (recordStart : Nat) (queue : List (Fin n)) (head : Nat) (active : Option (Fin n))
    (visited : List Nat) (index : Fin clauses.length) (labels : List (Fin n))
    (original : Controller.Horn.Worklist.compileClause clauses[index.val] = .positive labels)
    (queued : ∀ label ∈ active.toList, label ∈ queue)
    (zero : remaining (Controller.Horn.Worklist.compileClause clauses[index.val])
      (processedForRow queue head active visited
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)) = 0)
    (forced : QueueForced clauses queue) :
    ¬ ∃ assignment : Fin n → Bool,
      ∀ other : Fin clauses.length,
        (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment := by
  rintro ⟨assignment, models⟩
  have model := models index
  rw [original] at model
  obtain ⟨label, incident, trueValue⟩ := model
  have marked := zero_support_queued
    (Controller.Horn.Worklist.compileClause clauses[index.val]) queue head active visited
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
    queued zero label (by simpa [original, Controller.Horn.Worklist.Rule.positives] using incident)
  have falseValue := forced assignment models label marked
  exact Bool.false_ne_true (falseValue.symm.trans trueValue)


open Controller.Cost Controller.Horn.WorklistFIFORun
open Controller.Horn.WorklistBucketSuccessor Controller.Horn.WorklistPropagationStep
open Controller.Horn.WorklistBucketRun Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketReady Controller.Horn.WorklistBucketFrame
open Controller.Horn.WorklistBucketNegative Controller.Horn.WorklistBucketCharge

theorem semantic_step (clauses : List (Controller.CNF.Clause (Fin n)))
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
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width) :
    (∃ nextQueue nextVisited nextFired nextBound final ticks,
      nextBound < bound ∧ matching (IndexScan.occurrences clauses recordStart) active bound =
        matching (IndexScan.occurrences clauses recordStart) active nextBound + 1 ∧
      queue.length ≤ nextQueue.length ∧ nextQueue.take head = queue.take head ∧ ticks ≤ 32 + 3 * (nextQueue.length - queue.length) ∧
      Execution program state final ticks state.liveWords ∧
      Snapshot clauses recordStart recordEnd base entry nextQueue head active nextVisited nextFired nextBound final ∧
      ProcessedComplete clauses recordStart nextQueue head (some active) nextVisited nextFired ∧
      FiredMeaning clauses nextQueue nextFired ∧ QueueForced clauses nextQueue ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]?) ∨
    (∃ final, Execution program state final 15 state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width conflict ∧ final.halted = false ∧
      ¬ ∃ assignment : Fin n → Bool, ∀ other : Fin clauses.length,
        (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment) := by
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
      obtain ⟨final, trace, _, size, stack, output, pc, running⟩ :=
        Controller.Horn.WorklistBucketCases.conflict_iteration program entry exit ready base skip conflict
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
          (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
          (recordEnd + 2 * current.val) labels state linked selected loopAt readyAt
          (by have := invariant.spine.positiveEnd; omega) held snapshot.one snapshot.zero snapshot.decrement
          snapshot.position snapshot.running capacity readyCapacity snapshot.room
      refine Or.inr ⟨final, trace, size, stack, output, pc, running, ?_⟩
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
          size, stack, output, pc, running, headForced, headFrame⟩ := negative_head_successor
        clauses recordStart recordEnd base entry exit ready skip conflict program queue head active forcedHead labels
        visited fired index current state invariant snapshot.firedZero ruleEq sourceRow label countZero separated loopAt readyAt
        tailBound tailValue held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running
        capacity readyCapacity snapshot.room
      refine Or.inl ⟨Controller.Horn.WorklistBucketReady.queueAfter queue forcedHead,
        visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
        (fun other => if other = index then true else fired other), current.val, final,
        (if forcedHead ∈ queue then 32 else 35), less, charged, (queue_growth queue forcedHead).1,
        queue_after_take queue forcedHead head invariant.headBound, ?_, trace, ?_, ?_, ?_, ?_, size, stack, output, headFrame⟩
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
    refine Or.inl ⟨queue, visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
      fired, current.val, final, 12, less, charged, Nat.le_refl _, rfl, by omega, trace, ?_, ?_, ?_, ?_, size, stack, output, headFrame⟩
    · exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
      decrement, pc, running, by simpa only [size] using snapshot.room⟩
    · apply nonzero_complete clauses recordStart queue head active visited fired index
        complete unvisited sourceIncident fresh
      change 1 < rowCounts clauses recordStart queue head active visited index
      omega
    · exact meaning
    · exact forced

theorem semantic_bucket (clauses : List (Controller.CNF.Clause (Fin n)))
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
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue) :
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
          FiredMeaning clauses finalQueue finalFired ∧ QueueForced clauses finalQueue) := by
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
        Or.inr ⟨visited, fired, pc, finalInvariant, finalFired, ?_, ?_, ?_, ?_, ?_, complete, meaning, forced⟩⟩
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
      rcases semantic_step clauses recordStart recordEnd base entry exit ready skip conflict program queue head active
        visited fired bound state snapshot complete meaning forced nil separated loopAt readyAt capacity readyCapacity with continued | failed
      · obtain ⟨nextQueue, nextVisited, nextFired, nextBound, middle, firstTicks,
          smaller, matchingStep, growth, middlePrefix, firstBound, first, middleSnapshot, middleComplete, middleMeaning, middleForced, middleSize, middleStack, middleOutput, middleHead⟩ := continued
        obtain ⟨finalQueue, final, lastTicks, lastGrowth, unique, finalPrefix, lastBound, last,
            finalSize, finalStack, finalOutput, running, outcome⟩ :=
          ih nextBound smaller nextQueue nextVisited nextFired middle middleSnapshot middleComplete middleMeaning middleForced
        have middleLive : middle.liveWords = state.liveWords := by
          unfold State.liveWords
          rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, final, firstTicks + lastTicks, by omega, unique, finalPrefix.trans middlePrefix, by omega,
          ?_, finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, running, ?_⟩
        · simpa only [middleLive, Nat.max_self] using first.append last
        · rcases outcome with failed | ⟨finalVisited, finalFired, pc, invariant, firedZero, tail, zero, one, decrement, header, finalComplete, finalMeaning, finalForced⟩
          · exact Or.inl failed
          · exact Or.inr ⟨finalVisited, finalFired, pc, invariant, firedZero, tail, zero, one, decrement, header.trans middleHead, finalComplete, finalMeaning, finalForced⟩
      · obtain ⟨final, trace, size, stack, output, pc, running, noModels⟩ := failed
        exact ⟨queue, final, 15, Nat.le_refl _, snapshot.invariant.fifo.nodup, rfl,
          by omega, trace, size, stack, output, running, Or.inl ⟨pc, noModels⟩⟩

theorem semantic_cycle (clauses : List (Controller.CNF.Clause (Fin n)))
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
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width) :
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
          FiredMeaning clauses finalQueue finalFired ∧ QueueForced clauses finalQueue) := by
  obtain ⟨active, fetchedState, activeValue, first, snapshot, fetchedSize, fetchedStack, fetchedOutput, fetchedHead⟩ :=
    WorklistFIFO.fetch_execution clauses recordStart recordEnd base fetch done bucket program queue head fired state
      initial.spine initial.fifo initial.rows initial.firedZero nonempty initial.headValue initial.tailValue separated fetchAt
      initial.zero initial.one initial.decrement initial.position initial.running fetchCapacity initial.room
  obtain ⟨finalQueue, bucketState, bucketTicks, growth, unique, processedPrefix, charged, middle, bucketSize, bucketStack,
      bucketOutput, bucketRunning, outcome⟩ := semantic_bucket clauses recordStart recordEnd base bucket advance ready skip conflict program
        head active separated loopAt readyAt bucketCapacity readyCapacity (IndexScan.occurrences clauses recordStart).length
        queue [] fired fetchedState snapshot
        (by simpa [ProcessedComplete, processedForRow] using complete) meaning forced
  have fetchedLive : fetchedState.liveWords = state.liveWords := by
    unfold State.liveWords; rw [fetchedSize, fetchedStack, fetchedOutput]
  have bucketLive : bucketState.liveWords = state.liveWords := by
    unfold State.liveWords; rw [bucketSize, bucketStack, bucketOutput, fetchedSize, fetchedStack, fetchedOutput]
  rcases outcome with conflictPC | ⟨visited, finalFired, advancePC, invariant, firedZero, tail, zero, one, decrement, header, bucketComplete, finalMeaning, finalForced⟩
  · refine ⟨active, finalQueue, bucketState, 14 + bucketTicks, activeValue, growth, unique, processedPrefix, by omega, ?_,
      bucketSize.trans fetchedSize, bucketStack.trans fetchedStack, bucketOutput.trans fetchedOutput, bucketRunning, Or.inl conflictPC⟩
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
      output.trans (bucketOutput.trans fetchedOutput), running, Or.inr ⟨finalFired, finalReady, ?_, ?_, finalMeaning, finalForced⟩⟩
    · simpa only [fetchedLive, bucketLive, Nat.max_self] using (first.append middle).append last
    · rw [List.take_add_one, ← invariant.activeCurrent, processedPrefix]
      rfl
    · intro index enabled countZero
      apply bucketComplete index enabled
      rw [WorklistBucketComplete.completed_counts clauses recordStart recordEnd base finalQueue head active
        visited finalFired bucketState.heap invariant index]
      simpa [processedForRow] using countZero

theorem semantic_runtime (clauses : List (Controller.CNF.Clause (Fin n)))
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
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue) :
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
          FiredMeaning clauses finalQueue finalFired ∧ QueueForced clauses finalQueue)) := by
  induction budget generalizing head queue fired state with
  | zero =>
    have queueBound := Controller.Horn.WorklistMark.enqueue_bound queue initial.fifo.nodup
    have equal : head = queue.length := by have := initial.headBound; omega
    have atEnd : Ready clauses recordStart recordEnd base fetch queue queue.length fired state := by simpa only [equal] using initial
    obtain ⟨final, trace, finished, size, stack, output⟩ := fifo_empty clauses recordStart recordEnd base fetch done bucket program queue fired state atEnd fetchAt fetchCapacity
    exact ⟨queue, fired, final, 6, Nat.le_refl _, initial.fifo.nodup, by omega, trace, size, stack, output,
      finished.running, Or.inr ⟨finished,
        empty_complete clauses recordStart queue fired (by simpa only [equal] using complete), meaning, forced⟩⟩
  | succ budget ih =>
    by_cases equal : head = queue.length
    · have atEnd : Ready clauses recordStart recordEnd base fetch queue queue.length fired state := by simpa only [equal] using initial
      obtain ⟨final, trace, finished, size, stack, output⟩ := fifo_empty clauses recordStart recordEnd base fetch done bucket program queue fired state atEnd fetchAt fetchCapacity
      exact ⟨queue, fired, final, 6, Nat.le_refl _, initial.fifo.nodup, by omega, trace, size, stack, output,
        finished.running, Or.inr ⟨finished,
        empty_complete clauses recordStart queue fired (by simpa only [equal] using complete), meaning, forced⟩⟩
    · have nonempty : head < queue.length := by have := initial.headBound; omega
      obtain ⟨active, nextQueue, middle, firstTicks, activeValue, growth, unique, prefixEqual, firstBound, first,
          middleSize, middleStack, middleOutput, middleRunning, outcome⟩ := semantic_cycle clauses recordStart recordEnd base
        fetch done bucket advance ready skip conflict program queue head fired state initial complete meaning forced nonempty separated fetchAt advanceAt
        loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
      have fresh : active ∉ queue.take head := by
        have taken : (queue.take (head + 1)).Nodup := initial.fifo.nodup.take
        rw [List.take_add_one, activeValue] at taken
        have disjoint := (List.nodup_append.mp taken).2.2
        intro member
        exact disjoint active member active (by simp) rfl
      have partition := incidence_partition (IndexScan.occurrences clauses recordStart) (queue.take head) active fresh
      rcases outcome with conflictPC | ⟨nextFired, nextReady, promoted, nextComplete, nextMeaning, nextForced⟩
      · exact ⟨nextQueue, fired, middle, firstTicks, growth, unique, by omega, first,
          middleSize, middleStack, middleOutput, middleRunning, Or.inl conflictPC⟩
      · obtain ⟨finalQueue, finalFired, final, lastTicks, lastGrowth, finalUnique, lastBound, last,
          finalSize, finalStack, finalOutput, finalRunning, result⟩ := ih (head + 1) nextQueue nextFired middle (by omega) nextReady nextComplete nextMeaning nextForced
        have potential : pendingIncidences (IndexScan.occurrences clauses recordStart) (nextQueue.take (head + 1)) +
            matching (IndexScan.occurrences clauses recordStart) active (IndexScan.occurrences clauses recordStart).length =
            pendingIncidences (IndexScan.occurrences clauses recordStart) (queue.take head) := by
          rw [promoted]
          exact partition.symm
        have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, finalFired, final, firstTicks + lastTicks, by omega, finalUnique, by omega, ?_,
          finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, finalRunning, result⟩
        simpa only [middleLive, Nat.max_self] using first.append last

/-- A positive remaining count exposes an original support label not yet off. -/
theorem positive_remaining_witness (rule : Controller.Horn.Worklist.Rule (Fin n))
    (queue : List (Fin n)) (positive : 0 < remaining rule queue) :
    ∃ label ∈ rule.positives, offAssignment queue label = true := by
  obtain ⟨label, member⟩ := List.length_pos_iff_exists_mem.mp positive
  have selected : label ∈ rule.positives ∧ label ∉ queue := by
    simpa only [List.mem_filter, decide_eq_true_eq] using member
  exact ⟨label, selected.1, by simp [offAssignment, selected.2]⟩

/-- Completed physical counts and continuing fired tags imply original rule
satisfaction. Pending marks have become the full processed queue at this boundary. -/
theorem terminal_original_models (clauses : List (Clause (Fin n))) (queue : List (Fin n))
    (fired : Fin clauses.length → Bool) (complete : EnabledComplete clauses queue fired)
    (meaning : FiredMeaning clauses queue fired) :
    ∀ index : Fin clauses.length,
      (Controller.Horn.Worklist.compileClause clauses[index.val]).Holds (offAssignment queue) := by
  intro index
  by_cases zero : remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) queue = 0
  · cases original : Controller.Horn.Worklist.compileClause clauses[index.val] with
    | skip => simp [Controller.Horn.Worklist.Rule.Holds]
    | positive labels =>
      have enabled : (Controller.Horn.Worklist.compileClause clauses[index.val]).enabled = true := by
        simp [original, Controller.Horn.Worklist.Rule.enabled]
      obtain ⟨head, support, impossible, _⟩ := meaning index (complete index enabled zero)
      simp [original] at impossible
    | negative head labels =>
      have enabled : (Controller.Horn.Worklist.compileClause clauses[index.val]).enabled = true := by
        simp [original, Controller.Horn.Worklist.Rule.enabled]
      obtain ⟨actualHead, support, same, queued⟩ := meaning index (complete index enabled zero)
      have heads : head = actualHead := by simpa [original, Controller.Horn.Worklist.Rule.head?] using congrArg Controller.Horn.Worklist.Rule.head? same
      left
      simp [offAssignment, heads, queued]
  · have positive : 0 < remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) queue := by omega
    obtain ⟨label, incident, trueValue⟩ := positive_remaining_witness _ queue positive
    cases original : Controller.Horn.Worklist.compileClause clauses[index.val] with
    | skip => simp [Controller.Horn.Worklist.Rule.Holds]
    | positive labels => exact ⟨label, by simpa [original, Controller.Horn.Worklist.Rule.positives] using incident, trueValue⟩
    | negative head labels => exact Or.inr ⟨label, by simpa [original, Controller.Horn.Worklist.Rule.positives] using incident, trueValue⟩

/-- Original row semantics, with input row positions preserved, are the source
formula semantics. -/
theorem original_models_iff (formula : Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (assignment : Fin n → Bool) :
    (∀ index : Fin formula.clauses.toList.length,
      (Controller.Horn.Worklist.compileClause formula.clauses.toList[index.val]).Holds assignment) ↔
    Satisfies assignment formula := by
  rw [Controller.CNF.satisfies_iff_rows]
  constructor
  · intro models index
    apply (Controller.Horn.Worklist.compileClause_holds_iff _
      (dual _ (Array.getElem_mem ..)) assignment).mp
    simpa using models ⟨index.val, by simpa using index.isLt⟩
  · intro models index
    apply (Controller.Horn.Worklist.compileClause_holds_iff _
      (dual _ (by simpa using List.getElem_mem index.isLt)) assignment).mpr
    simpa using models ⟨index.val, by simpa using index.isLt⟩

/-- The exact D04 solver returns the same greatest assignment once the physical
trace has established its terminal model and original-model forcing invariant. -/
theorem d04_observable (formula : Formula (Fin n)) (dual : Controller.Horn.DualHorn formula)
    (queue : List (Fin n)) (fired : Fin formula.clauses.toList.length → Bool)
    (complete : EnabledComplete formula.clauses.toList queue fired)
    (meaning : FiredMeaning formula.clauses.toList queue fired)
    (forced : QueueForced formula.clauses.toList queue) :
    offAssignment queue = Controller.Horn.greatestCandidate formula ∧
      ∃ values, Controller.Horn.Worklist.solveFormula formula = some values ∧
        (fun label : Fin n => values[label.val]) = offAssignment queue := by
  have model : Satisfies (offAssignment queue) formula :=
    (original_models_iff formula dual _).mp (terminal_original_models _ queue fired complete meaning)
  have upper : ∀ assignment, Satisfies assignment formula →
      Controller.Horn.Below assignment (offAssignment queue) := by
    intro assignment satisfied label trueValue
    by_cases queued : label ∈ queue
    · have falseValue := forced assignment ((original_models_iff formula dual assignment).mpr satisfied) label queued
      exact False.elim (Bool.false_ne_true (falseValue.symm.trans trueValue))
    · simp [offAssignment, queued]
  have greatest := Controller.Horn.terminal_state_eq_greatest
    (Controller.Horn.Worklist.satisfies_rulesClosed dual model) upper
  obtain ⟨values, returned⟩ := (Controller.Horn.Worklist.solveFormula_some_iff_satisfiable formula dual).mpr
    ⟨offAssignment queue, model⟩
  exact ⟨greatest, values, returned,
    (Controller.Horn.Worklist.solveFormula_some_greatest formula dual values returned).trans greatest.symm⟩

end Controller.Horn.WorklistOutcome
