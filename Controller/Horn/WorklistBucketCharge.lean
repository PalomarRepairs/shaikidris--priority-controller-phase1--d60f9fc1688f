module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucketRun

@[expose] public section

/-! Costs are charged to original matching occurrences and actual FIFO growth.
Pending marks retain the processed-prefix count semantics. -/
namespace Controller.Horn.WorklistBucketCharge
open Controller.Cost Controller.Horn.WorklistPropagation
open Controller.Horn.WorklistBucketSuccessor Controller.Horn.WorklistPropagationStep
open Controller.Horn.WorklistBucketRun
variable {width n : Nat}

/-- Number of original active-label occurrences in one chronological prefix. -/
def matching (edges : List (Nat × Fin n)) (active : Fin n) (bound : Nat) : Nat :=
  ((edges.take bound).filter fun edge => decide (edge.2 = active)).length

/-- The real predecessor removes exactly the last matching original node. -/
theorem matching_predecessor (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (bound : Nat)
    (within : bound ≤ edges.length) (index : Fin edges.length)
    (inside : index.val < bound) (label : edges[index.val].2 = active)
    (pointer : IndexScan.heads recordEnd (edges.take bound) active = recordEnd + 2 * index.val) :
    matching edges active bound = matching edges active index.val + 1 := by
  induction bound generalizing index with
  | zero => omega
  | succ bound ih =>
      have valid : bound < edges.length := by omega
      have headEquation := IndexScan.heads_append recordEnd positive (edges.take bound)
        edges[bound].1 edges[bound].2 active
      have countEquation : matching edges active (bound + 1) =
          matching edges active bound + if edges[bound].2 = active then 1 else 0 := by
        unfold matching
        rw [List.take_succ_eq_append_getElem valid]
        simp only [List.filter_append, List.length_append]
        by_cases same : edges[bound].2 = active <;> simp [same]
      rw [List.take_succ_eq_append_getElem valid, headEquation,
        List.length_take_of_le (by omega)] at pointer
      by_cases same : edges[bound].2 = active
      · have indexEqual : index.val = bound := by
          simp only [ite_eq_left same.symm] at pointer
          omega
        simpa only [countEquation, ite_eq_left same, indexEqual]
      · have smaller : index.val < bound := by
          have different : index.val ≠ bound := by
            intro equal
            exact same (by simpa only [equal] using label)
          omega
        have oldPointer : IndexScan.heads recordEnd (edges.take bound) active = recordEnd + 2 * index.val := by
          simpa only [ite_eq_right (Ne.symm same)] using pointer
        have oldCount := ih (by omega) index smaller label oldPointer
        simpa only [countEquation, ite_eq_right same, Nat.add_zero] using oldCount

/-- A nil original pointer has no matching original occurrences to charge. -/
theorem matching_nil (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (bound : Nat)
    (within : bound ≤ edges.length)
    (nil : IndexScan.heads recordEnd (edges.take bound) active = 0) : matching edges active bound = 0 := by
  unfold matching
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro edge member
  obtain ⟨position, positionBound, value⟩ := List.mem_iff_getElem.mp member
  have originalBound : position < edges.length := by
    have : position < min bound edges.length := by simpa only [List.length_take] using positionBound
    omega
  have prefixBound : position < bound := by
    have : position < min bound edges.length := by simpa only [List.length_take] using positionBound
    omega
  have sourceValue : edges[position] = edge := by
    simpa using value
  have absent := (head_nil_iff edges recordEnd positive active bound within).mp nil ⟨position, originalBound⟩ prefixBound
  simpa only [sourceValue, decide_eq_true_eq] using absent

/-- The two checked negative branches differ only by one new pending label. -/
theorem negative_cost (queue : List (Fin n)) (label : Fin n) :
    (if label ∈ queue then 32 else 35) =
      32 + 3 * ((Controller.Horn.WorklistBucketReady.queueAfter queue label).length - queue.length) := by
  by_cases stale : label ∈ queue
  · simp [Controller.Horn.WorklistBucketReady.queueAfter, stale]
  · simp [Controller.Horn.WorklistBucketReady.queueAfter, stale]

/-- Enqueue grows the real FIFO by zero or one without removing prior labels. -/
theorem queue_growth (queue : List (Fin n)) (label : Fin n) :
    queue.length ≤ (Controller.Horn.WorklistBucketReady.queueAfter queue label).length ∧
      (Controller.Horn.WorklistBucketReady.queueAfter queue label).length ≤ queue.length + 1 := by
  by_cases stale : label ∈ queue <;> simp [Controller.Horn.WorklistBucketReady.queueAfter, stale]

/-- Actual per-node branches charged to one original matching occurrence and
zero or one freshly enqueued pending label. -/
theorem step_charged (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (bound : Nat) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state)
    (nonnil : IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take bound) active ≠ 0)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width) :
    (∃ nextQueue nextVisited nextFired nextBound final ticks,
      nextBound < bound ∧ matching (IndexScan.occurrences clauses recordStart) active bound =
        matching (IndexScan.occurrences clauses recordStart) active nextBound + 1 ∧
      queue.length ≤ nextQueue.length ∧ ticks ≤ 32 + 3 * (nextQueue.length - queue.length) ∧
      Execution program state final ticks state.liveWords ∧
      Snapshot clauses recordStart recordEnd base entry nextQueue head active nextVisited nextFired nextBound final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output) ∨
    (∃ final, Execution program state final 15 state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width conflict ∧ final.halted = false) := by
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
      obtain ⟨final, trace, _, size, stack, output, pc, running⟩ :=
        Controller.Horn.WorklistBucketCases.conflict_iteration program entry exit ready base skip conflict
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
          (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active)
          (recordEnd + 2 * current.val) labels state linked selected loopAt readyAt
          (by have := invariant.spine.positiveEnd; omega) held snapshot.one snapshot.zero snapshot.decrement
          snapshot.position snapshot.running capacity readyCapacity snapshot.room
      exact Or.inr ⟨final, trace, size, stack, output, pc, running⟩
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
          size, stack, output, pc, running, _⟩ := Controller.Horn.WorklistBucketNegative.negative_successor
        clauses recordStart recordEnd base entry exit ready skip conflict program queue head active forcedHead labels
        visited fired index current state invariant snapshot.firedZero ruleEq sourceRow label countZero separated loopAt readyAt
        tailBound tailValue held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running
        capacity readyCapacity snapshot.room
      refine Or.inl ⟨Controller.Horn.WorklistBucketReady.queueAfter queue forcedHead,
        visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
        (fun other => if other = index then true else fired other), current.val, final,
        (if forcedHead ∈ queue then 32 else 35), less, charged, (queue_growth queue forcedHead).1,
        ?_, trace, ?_, size, stack, output⟩
      · exact (negative_cost queue forcedHead).le
      · exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
          decrement, pc, running, by simpa only [size] using snapshot.room⟩
  · have positiveCount : 0 < rowCounts clauses recordStart queue head active visited index - 1 := by omega
    obtain ⟨final, trace, nextInvariant, nextFired, next, zero, one, decrement, tail,
        size, stack, output, pc, running⟩ := nonzero_tail clauses recordStart recordEnd base entry exit ready program
      queue head active visited fired index current state invariant snapshot.firedZero sourceRow label positiveCount
      separated loopAt snapshot.tail held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running capacity snapshot.room
    refine Or.inl ⟨queue, visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
      fired, current.val, final, 12, less, charged, Nat.le_refl _, by omega, trace, ?_, size, stack, output⟩
    exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
      decrement, pc, running, by simpa only [size] using snapshot.room⟩

/-- A complete actual linked bucket is charged once per original matching
occurrence and three ticks per new pending FIFO label, with one terminal test. -/
theorem bucket_charged (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (head : Nat) (active : Fin n)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (bound : Nat) (queue : List (Fin n)) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state) :
    ∃ finalQueue final ticks,
      queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧
      ticks ≤ 32 * matching (IndexScan.occurrences clauses recordStart) active bound +
        3 * (finalQueue.length - queue.length) + 1 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      (final.pc = word width conflict ∨
        ∃ finalVisited finalFired,
          final.pc = word width exit ∧
          Invariant clauses recordStart recordEnd base finalQueue head (some active) finalVisited 0 finalFired final.heap ∧
          FiredZero clauses recordStart finalQueue head (some active) finalVisited finalFired ∧
          final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
            some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + finalQueue.length)) ∧
          final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1)) := by
  induction bound using Nat.strong_induction_on generalizing queue visited fired state with
  | h bound ih =>
    by_cases nil : IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take bound) active = 0
    · have invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired state.heap := by
        simpa only [nil] using snapshot.invariant
      have held : state.reg 0 = word width 0 := by simpa only [nil] using snapshot.held
      obtain ⟨final, trace, finalInvariant, finalFired, registers, heap, stack, output, pc, running⟩ :=
        nil_endpoint clauses recordStart recordEnd base entry exit ready program queue head active visited fired state
          invariant snapshot.firedZero loopAt held snapshot.position snapshot.running capacity
      refine ⟨queue, final, 1, Nat.le_refl _, invariant.fifo.nodup, by omega, trace,
        by simpa only [heap], stack, output, running,
        Or.inr ⟨visited, fired, pc, finalInvariant, finalFired, ?_, ?_, ?_, ?_⟩⟩
      · simpa only [heap] using snapshot.tail
      · exact (congrFun registers 2).trans snapshot.zero
      · exact (congrFun registers 5).trans snapshot.one
      · exact (congrFun registers 6).trans snapshot.decrement
    · have matchingPositive : 0 < matching (IndexScan.occurrences clauses recordStart) active bound := by
        rcases head_frontier (IndexScan.occurrences clauses recordStart) recordEnd
          snapshot.invariant.spine.positiveEnd active bound snapshot.within with zero | ⟨index, less, label, pointer⟩
        · contradiction
        · have charged := matching_predecessor (IndexScan.occurrences clauses recordStart) recordEnd
            snapshot.invariant.spine.positiveEnd active bound snapshot.within index less label pointer
          omega
      rcases step_charged clauses recordStart recordEnd base entry exit ready skip conflict program queue head active
        visited fired bound state snapshot nil separated loopAt readyAt capacity readyCapacity with continued | failed
      · obtain ⟨nextQueue, nextVisited, nextFired, nextBound, middle, firstTicks,
          smaller, matchingStep, growth, firstBound, first, middleSnapshot, middleSize, middleStack, middleOutput⟩ := continued
        obtain ⟨finalQueue, final, lastTicks, lastGrowth, unique, lastBound, last,
            finalSize, finalStack, finalOutput, running, outcome⟩ :=
          ih nextBound smaller nextQueue nextVisited nextFired middle middleSnapshot
        have middleLive : middle.liveWords = state.liveWords := by
          unfold State.liveWords
          rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, final, firstTicks + lastTicks, by omega, unique, by omega,
          ?_, finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, running, outcome⟩
        simpa only [middleLive, Nat.max_self] using first.append last
      · obtain ⟨final, trace, size, stack, output, pc, running⟩ := failed
        exact ⟨queue, final, 15, Nat.le_refl _, snapshot.invariant.fifo.nodup,
          by omega, trace, size, stack, output, running, Or.inl pc⟩

/-- Off-before-enqueue bounds the extra actual enqueue ticks by the remaining
preallocated positive scratch capacity, without counting pending labels as processed. -/
theorem bucket_capacity_charged (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (head : Nat) (active : Fin n)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (bound : Nat) (queue : List (Fin n)) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state) :
    ∃ final ticks,
      ticks ≤ 32 * matching (IndexScan.occurrences clauses recordStart) active bound + 3 * (n - queue.length) + 1 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false := by
  obtain ⟨finalQueue, final, ticks, growth, unique, charged, trace, size, stack, output, running, _⟩ :=
    bucket_charged clauses recordStart recordEnd base entry exit ready skip conflict program head active separated loopAt readyAt
      capacity readyCapacity bound queue visited fired state snapshot
  have finalBound := Controller.Horn.WorklistMark.enqueue_bound finalQueue unique
  exact ⟨final, ticks, by omega, trace, size, stack, output, running⟩

end Controller.Horn.WorklistBucketCharge
