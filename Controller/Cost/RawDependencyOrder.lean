module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Raw
public import Controller.Horn.WorklistOutcome

@[expose] public section

/-! Dependency-order certificates for the original node identifiers carried by
an indexed Horn FIFO. The positive support retains original child membership,
including repeated source occurrences, while propagation counts its distinct
labels. -/
namespace Controller.Cost.RawDependencyOrder
open Controller.Decoder Controller.Horn.Worklist
open Controller.Horn.WorklistPropagation Controller.Horn.WorklistBucketReady
variable {n width : Nat}

/-- A queue prefix has already placed every child before its parent. -/
def DependencyOrder (graph : UnorderedDAG n) (queue : List (Fin graph.nodeCount)) : Prop :=
  ∀ parent ∈ queue, ∀ child ∈ (graph.node parent).children,
    child ∈ queue ∧ queue.idxOf child < queue.idxOf parent

/-- The source dependency rule uses one head and the distinct original child labels. -/
def dependencyRule (graph : UnorderedDAG n) (parent : Fin graph.nodeCount) :
    Rule (Fin graph.nodeCount) :=
  .negative parent (graph.node parent).children.dedup

@[simp] theorem dependency_support (graph : UnorderedDAG n) (parent child : Fin graph.nodeCount) :
    child ∈ (dependencyRule graph parent).positives ↔ child ∈ (graph.node parent).children := by
  simp only [dependencyRule, Rule.positives, List.mem_dedup]

theorem empty_order (graph : UnorderedDAG n) : DependencyOrder graph [] := by
  intro parent member
  exact False.elim (List.not_mem_nil member)

theorem append_order (graph : UnorderedDAG n) (queue : List (Fin graph.nodeCount))
    (parent : Fin graph.nodeCount) (ordered : DependencyOrder graph queue)
    (fresh : parent ∉ queue)
    (children : ∀ child ∈ (graph.node parent).children, child ∈ queue) :
    DependencyOrder graph (queue ++ [parent]) := by
  intro query member child incident
  rcases List.mem_append.mp member with old | added
  · obtain ⟨present, earlier⟩ := ordered query old child incident
    refine ⟨List.mem_append.mpr (Or.inl present), ?_⟩
    rw [List.idxOf_append_of_mem present, List.idxOf_append_of_mem old]
    exact earlier
  · have equal : query = parent := by simpa only [List.mem_singleton] using added
    subst query
    have present := children child incident
    refine ⟨List.mem_append.mpr (Or.inl present), ?_⟩
    rw [List.idxOf_append_of_mem present, List.idxOf_append_of_notMem fresh]
    simpa using List.idxOf_lt_length_of_mem present

theorem queue_after_order (graph : UnorderedDAG n) (queue : List (Fin graph.nodeCount))
    (parent : Fin graph.nodeCount) (ordered : DependencyOrder graph queue)
    (children : ∀ child ∈ (graph.node parent).children, child ∈ queue) :
    DependencyOrder graph (queueAfter queue parent) := by
  by_cases stale : parent ∈ queue
  · simpa only [queueAfter, ite_eq_left stale] using ordered
  · simpa only [queueAfter, ite_eq_right stale] using append_order graph queue parent ordered stale children

/-- A ready count is relative to processed FIFO labels and visited original
bucket nodes. It supplies the old-queue membership needed for a fresh append. -/
theorem zero_enqueue_order (graph : UnorderedDAG n) (queue : List (Fin graph.nodeCount))
    (head : Nat) (active : Option (Fin graph.nodeCount)) (visited : List Nat) (row : Nat)
    (parent : Fin graph.nodeCount) (ordered : DependencyOrder graph queue)
    (queued : ∀ label ∈ active.toList, label ∈ queue)
    (zero : remaining (dependencyRule graph parent)
      (processedForRow queue head active visited row) = 0) :
    DependencyOrder graph (queueAfter queue parent) := by
  apply queue_after_order graph queue parent ordered
  intro child incident
  exact zero_support_queued (dependencyRule graph parent) queue head active visited row
    queued zero child ((dependency_support graph parent child).mpr incident)

/-- A complete distinct actual queue is an original-ID topological numbering. -/
def numbering (graph : UnorderedDAG n) (queue : List (Fin graph.nodeCount))
    (distinct : queue.Nodup) (complete : ∀ node, node ∈ queue)
    (ordered : DependencyOrder graph queue) : graph.Numbering where
  order := queue
  distinct := distinct
  complete := complete
  earlier := fun parent child incident => (ordered parent (complete parent) child incident).2

/-- Acyclic dependencies force every node false in every model of their rules. -/
theorem acyclic_models_false (graph : UnorderedDAG n) (acyclic : graph.Acyclic)
    (assignment : Fin graph.nodeCount → Bool)
    (models : ∀ parent, (dependencyRule graph parent).Holds assignment) :
    ∀ parent, assignment parent = false := by
  intro parent
  apply acyclic.induction parent
  intro current ih
  rcases models current with forced | ⟨child, incident, trueValue⟩
  · exact forced
  · have source : graph.Child child current := by
      exact (dependency_support graph current child).mp incident
    have falseValue := ih child source
    rw [falseValue] at trueValue
    contradiction

open Controller.Horn Controller.Horn.WorklistSeed
open Controller.Cost Controller.Horn.WorklistOutcome Controller.Horn.WorklistFIFORun
open Controller.Horn.WorklistBucketSuccessor Controller.Horn.WorklistPropagationStep
open Controller.Horn.WorklistBucketRun Controller.Horn.WorklistFIFO
open Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketNegative Controller.Horn.WorklistBucketCharge
open Controller.Horn.WorklistBucketFrame

/-- Original selected heads retain every original child in their normalized support. -/
def ClauseDependencies (graph : UnorderedDAG n)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount))) : Prop :=
  ∀ index : Fin clauses.length, ∀ parent labels,
    compileClause clauses[index.val] = .negative parent labels →
    ∀ child ∈ (graph.node parent).children, child ∈ labels

theorem ordered_semantic_step (graph : UnorderedDAG n) (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (queue : List (Fin graph.nodeCount)) (head : Nat) (active : Fin graph.nodeCount) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (bound : Nat) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state)
    (complete : ProcessedComplete clauses recordStart queue head (some active) visited fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
    (dependencies : ClauseDependencies graph clauses)
    (ordered : DependencyOrder graph queue)
    (nonnil : IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take bound) active ≠ 0)
    (separated : base + 5 * graph.nodeCount + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := graph.nodeCount) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width) :
    (∃ nextQueue nextVisited nextFired nextBound final ticks,
      nextBound < bound ∧ matching (IndexScan.occurrences clauses recordStart) active bound =
        matching (IndexScan.occurrences clauses recordStart) active nextBound + 1 ∧
      queue.length ≤ nextQueue.length ∧ nextQueue.take head = queue.take head ∧ ticks ≤ 32 + 3 * (nextQueue.length - queue.length) ∧
      Execution program state final ticks state.liveWords ∧
      Snapshot clauses recordStart recordEnd base entry nextQueue head active nextVisited nextFired nextBound final ∧
      ProcessedComplete clauses recordStart nextQueue head (some active) nextVisited nextFired ∧
      FiredMeaning clauses nextQueue nextFired ∧ QueueForced clauses nextQueue ∧
      DependencyOrder graph nextQueue ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.heap[headSlot (n := graph.nodeCount) base]? = state.heap[headSlot (n := graph.nodeCount) base]?) ∨
    (∃ final, Execution program state final 15 state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width conflict ∧ final.halted = false ∧
      ¬ ∃ assignment : Fin graph.nodeCount → Bool, ∀ other : Fin clauses.length,
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
      have tailBound : Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount) base < state.heap.size := by
        have := invariant.fifo.fits
        unfold Controller.Horn.WorklistBucketReady.tailSlot
        omega
      have tailValue : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount) base]'tailBound =
          word width (Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount) base + queue.length) := by
        have value := snapshot.tail
        simpa only [Array.getElem?_eq_getElem tailBound, Option.some.injEq] using value
      obtain ⟨final, trace, nextInvariant, nextFired, next, zero, one, decrement, tail,
          size, stack, output, pc, running, headForced, headFrame⟩ := negative_head_successor
        clauses recordStart recordEnd base entry exit ready skip conflict program queue head active forcedHead labels
        visited fired index current state invariant snapshot.firedZero ruleEq sourceRow label countZero separated loopAt readyAt
        tailBound tailValue held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running
        capacity readyCapacity snapshot.room
      have selectedZero : remaining (.negative forcedHead labels)
          (processedForRow queue head (some active)
            (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
            (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)) = 0 := by
        have counts := visited_count_successor clauses recordStart queue head active visited index
          unvisited sourceIncident fresh index
        have actualZero : rowCounts clauses recordStart queue head active
            (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val]) index = 0 := by
          dsimp only [rowCounts]
          rw [counts, ite_eq_left rfl]
          exact countZero
        simpa only [rowCounts, ruleEq] using actualZero
      have nextOrder : DependencyOrder graph (queueAfter queue forcedHead) := by
        apply queue_after_order graph queue forcedHead ordered
        intro child original
        exact zero_support_queued (.negative forcedHead labels) queue head (some active)
          (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
          invariant.activeQueued selectedZero child
          (dependencies index forcedHead labels ruleEq child original)
      refine Or.inl ⟨Controller.Horn.WorklistBucketReady.queueAfter queue forcedHead,
        visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
        (fun other => if other = index then true else fired other), current.val, final,
        (if forcedHead ∈ queue then 32 else 35), less, charged, (queue_growth queue forcedHead).1,
        queue_after_take queue forcedHead head invariant.headBound, ?_, trace, ?_, ?_, ?_, ?_, nextOrder, size, stack, output, headFrame⟩
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
      fired, current.val, final, 12, less, charged, Nat.le_refl _, rfl, by omega, trace, ?_, ?_, ?_, ?_, ordered, size, stack, output, headFrame⟩
    · exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
      decrement, pc, running, by simpa only [size] using snapshot.room⟩
    · apply nonzero_complete clauses recordStart queue head active visited fired index
        complete unvisited sourceIncident fresh
      change 1 < rowCounts clauses recordStart queue head active visited index
      omega
    · exact meaning
    · exact forced


theorem ordered_semantic_bucket (graph : UnorderedDAG n) (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (head : Nat) (active : Fin graph.nodeCount)
    (separated : base + 5 * graph.nodeCount + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := graph.nodeCount) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (bound : Nat) (queue : List (Fin graph.nodeCount)) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state)
    (complete : ProcessedComplete clauses recordStart queue head (some active) visited fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
    (dependencies : ClauseDependencies graph clauses) (ordered : DependencyOrder graph queue) :
    ∃ finalQueue final ticks,
      queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧ finalQueue.take head = queue.take head ∧ DependencyOrder graph finalQueue ∧
      ticks ≤ 32 * matching (IndexScan.occurrences clauses recordStart) active bound +
        3 * (finalQueue.length - queue.length) + 1 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      ((final.pc = word width conflict ∧
        ¬ ∃ assignment : Fin graph.nodeCount → Bool, ∀ other : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment) ∨
        ∃ finalVisited finalFired,
          final.pc = word width exit ∧
          Invariant clauses recordStart recordEnd base finalQueue head (some active) finalVisited 0 finalFired final.heap ∧
          FiredZero clauses recordStart finalQueue head (some active) finalVisited finalFired ∧
          final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount) base]? =
            some (word width (Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount) base + finalQueue.length)) ∧
          final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
          final.heap[headSlot (n := graph.nodeCount) base]? = state.heap[headSlot (n := graph.nodeCount) base]? ∧
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
      refine ⟨queue, final, 1, Nat.le_refl _, invariant.fifo.nodup, rfl, ordered, by omega, trace,
        by simpa only [heap], stack, output, running,
        Or.inr ⟨visited, fired, pc, finalInvariant, finalFired, ?_, ?_, ?_, ?_, ?_, complete, meaning, forced⟩⟩
      · simpa only [heap] using snapshot.tail
      · exact (congrFun registers 2).trans snapshot.zero
      · exact (congrFun registers 5).trans snapshot.one
      · exact (congrFun registers 6).trans snapshot.decrement
      · exact congrArg (fun heap : Array (Word width) => heap[headSlot (n := graph.nodeCount) base]?) heap
    · have matchingPositive : 0 < matching (IndexScan.occurrences clauses recordStart) active bound := by
        rcases head_frontier (IndexScan.occurrences clauses recordStart) recordEnd
          snapshot.invariant.spine.positiveEnd active bound snapshot.within with zero | ⟨index, less, label, pointer⟩
        · contradiction
        · have charged := matching_predecessor (IndexScan.occurrences clauses recordStart) recordEnd
            snapshot.invariant.spine.positiveEnd active bound snapshot.within index less label pointer
          omega
      rcases ordered_semantic_step graph clauses recordStart recordEnd base entry exit ready skip conflict program queue head active
        visited fired bound state snapshot complete meaning forced dependencies ordered nil separated loopAt readyAt capacity readyCapacity with continued | failed
      · obtain ⟨nextQueue, nextVisited, nextFired, nextBound, middle, firstTicks,
          smaller, matchingStep, growth, middlePrefix, firstBound, first, middleSnapshot, middleComplete, middleMeaning, middleForced, middleOrdered, middleSize, middleStack, middleOutput, middleHead⟩ := continued
        obtain ⟨finalQueue, final, lastTicks, lastGrowth, unique, finalPrefix, finalOrdered, lastBound, last,
            finalSize, finalStack, finalOutput, running, outcome⟩ :=
          ih nextBound smaller nextQueue nextVisited nextFired middle middleSnapshot middleComplete middleMeaning middleForced middleOrdered
        have middleLive : middle.liveWords = state.liveWords := by
          unfold State.liveWords
          rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, final, firstTicks + lastTicks, by omega, unique, finalPrefix.trans middlePrefix, finalOrdered, by omega,
          ?_, finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, running, ?_⟩
        · simpa only [middleLive, Nat.max_self] using first.append last
        · rcases outcome with failed | ⟨finalVisited, finalFired, pc, invariant, firedZero, tail, zero, one, decrement, header, finalComplete, finalMeaning, finalForced⟩
          · exact Or.inl failed
          · exact Or.inr ⟨finalVisited, finalFired, pc, invariant, firedZero, tail, zero, one, decrement, header.trans middleHead, finalComplete, finalMeaning, finalForced⟩
      · obtain ⟨final, trace, size, stack, output, pc, running, noModels⟩ := failed
        exact ⟨queue, final, 15, Nat.le_refl _, snapshot.invariant.fifo.nodup, rfl, ordered,
          by omega, trace, size, stack, output, running, Or.inl ⟨pc, noModels⟩⟩

theorem ordered_semantic_cycle (graph : UnorderedDAG n) (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (recordStart recordEnd base fetch done bucket advance ready skip conflict : Nat) (program : Program width 8)
    (queue : List (Fin graph.nodeCount)) (head : Nat) (fired : Fin clauses.length → Bool) (state : State width 8)
    (initial : Ready clauses recordStart recordEnd base fetch queue head fired state)
    (complete : ProcessedComplete clauses recordStart queue head none [] fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
    (dependencies : ClauseDependencies graph clauses) (ordered : DependencyOrder graph queue)
    (nonempty : head < queue.length)
    (separated : base + 5 * graph.nodeCount + 4 ≤ recordStart)
    (fetchAt : WorklistFIFO.FetchAt (n := graph.nodeCount) program base fetch done bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := graph.nodeCount) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := graph.nodeCount) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width) :
    ∃ active finalQueue final ticks,
      queue[head]? = some active ∧ queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧ finalQueue.take head = queue.take head ∧ DependencyOrder graph finalQueue ∧
      ticks ≤ 32 * matching (IndexScan.occurrences clauses recordStart) active (IndexScan.occurrences clauses recordStart).length +
        3 * (finalQueue.length - queue.length) + 20 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      ((final.pc = word width conflict ∧
        ¬ ∃ assignment : Fin graph.nodeCount → Bool, ∀ other : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[other.val]).Holds assignment) ∨
        ∃ finalFired, Ready clauses recordStart recordEnd base fetch finalQueue (head + 1) finalFired final ∧
          finalQueue.take (head + 1) = queue.take head ++ [active] ∧
          ProcessedComplete clauses recordStart finalQueue (head + 1) none [] finalFired ∧
          FiredMeaning clauses finalQueue finalFired ∧ QueueForced clauses finalQueue) := by
  obtain ⟨active, fetchedState, activeValue, first, snapshot, fetchedSize, fetchedStack, fetchedOutput, fetchedHead⟩ :=
    WorklistFIFO.fetch_execution clauses recordStart recordEnd base fetch done bucket program queue head fired state
      initial.spine initial.fifo initial.rows initial.firedZero nonempty initial.headValue initial.tailValue separated fetchAt
      initial.zero initial.one initial.decrement initial.position initial.running fetchCapacity initial.room
  obtain ⟨finalQueue, bucketState, bucketTicks, growth, unique, processedPrefix, bucketOrdered, charged, middle, bucketSize, bucketStack,
      bucketOutput, bucketRunning, outcome⟩ := ordered_semantic_bucket graph clauses recordStart recordEnd base bucket advance ready skip conflict program
        head active separated loopAt readyAt bucketCapacity readyCapacity (IndexScan.occurrences clauses recordStart).length
        queue [] fired fetchedState snapshot
        (by simpa [ProcessedComplete, processedForRow] using complete) meaning forced dependencies ordered
  have fetchedLive : fetchedState.liveWords = state.liveWords := by
    unfold State.liveWords; rw [fetchedSize, fetchedStack, fetchedOutput]
  have bucketLive : bucketState.liveWords = state.liveWords := by
    unfold State.liveWords; rw [bucketSize, bucketStack, bucketOutput, fetchedSize, fetchedStack, fetchedOutput]
  rcases outcome with conflictPC | ⟨visited, finalFired, advancePC, invariant, firedZero, tail, zero, one, decrement, header, bucketComplete, finalMeaning, finalForced⟩
  · refine ⟨active, finalQueue, bucketState, 14 + bucketTicks, activeValue, growth, unique, processedPrefix, bucketOrdered, by omega, ?_,
      bucketSize.trans fetchedSize, bucketStack.trans fetchedStack, bucketOutput.trans fetchedOutput, bucketRunning, Or.inl conflictPC⟩
    simpa only [fetchedLive, Nat.max_self] using first.append middle
  · have nextHead : head + 1 ≤ finalQueue.length := by
      obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp invariant.activeCurrent.symm
      omega
    have headBound : headSlot (n := graph.nodeCount) base < bucketState.heap.size := by have := invariant.fifo.fits; unfold headSlot; omega
    have currentHead : bucketState.heap[headSlot (n := graph.nodeCount) base]? = some (word width (queueStart (n := graph.nodeCount) base + head)) := header.trans fetchedHead
    have headCell : bucketState.heap[headSlot (n := graph.nodeCount) base]'headBound = word width (queueStart (n := graph.nodeCount) base + head) := by
      simpa only [Array.getElem?_eq_getElem headBound, Option.some.injEq] using currentHead
    have nextFits : queueStart (n := graph.nodeCount) base + head + 1 < 2 ^ width := by
      have := invariant.fifo.queue.fits
      have bucketRoom : bucketState.heap.size < 2 ^ width := by simpa only [bucketSize, fetchedSize] using initial.room
      omega
    obtain ⟨final, last, heap, _, regs, size, stack, output, pc, running⟩ := WorklistFIFO.head_advance_execution
      program base advance fetch (queueStart (n := graph.nodeCount) base + head) bucketState advanceAt headBound headCell one zero
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
      finalFired bucketState.heap (word width (queueStart (n := graph.nodeCount) base + head + 1)) invariant.spine invariant.fifo baselineRows separated
    have finalHead : final.heap[headSlot (n := graph.nodeCount) base]? = some (word width (queueStart (n := graph.nodeCount) base + (head + 1))) := by
      rw [heap]
      simp only [Array.getElem?_set_self, Nat.add_assoc]
    have finalTail : final.heap[tailSlot (n := graph.nodeCount) base]? = some (word width (queueStart (n := graph.nodeCount) base + finalQueue.length)) := by
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
    refine ⟨active, finalQueue, final, 14 + bucketTicks + 5, activeValue, growth, unique, processedPrefix, bucketOrdered, by omega, ?_,
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

theorem ordered_semantic_runtime (graph : UnorderedDAG n) (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (recordStart recordEnd base fetch done bucket advance ready skip conflict : Nat) (program : Program width 8)
    (separated : base + 5 * graph.nodeCount + 4 ≤ recordStart)
    (fetchAt : WorklistFIFO.FetchAt (n := graph.nodeCount) program base fetch done bucket)
    (advanceAt : WorklistFIFO.AdvanceAt (n := graph.nodeCount) program base advance fetch)
    (loopAt : WorklistBucketLoop.At program bucket advance ready)
    (readyAt : WorklistBucketReady.At (n := graph.nodeCount) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (budget head : Nat) (queue : List (Fin graph.nodeCount)) (fired : Fin clauses.length → Bool) (state : State width 8)
    (capacityLedger : head + budget = graph.nodeCount)
    (initial : Ready clauses recordStart recordEnd base fetch queue head fired state)
    (complete : ProcessedComplete clauses recordStart queue head none [] fired)
    (meaning : FiredMeaning clauses queue fired) (forced : QueueForced clauses queue)
    (dependencies : ClauseDependencies graph clauses) (ordered : DependencyOrder graph queue) :
    ∃ finalQueue finalFired final ticks,
      queue.length ≤ finalQueue.length ∧ finalQueue.Nodup ∧ DependencyOrder graph finalQueue ∧
      ticks ≤ 32 * pendingIncidences (IndexScan.occurrences clauses recordStart) (queue.take head) +
        20 * budget + 3 * (finalQueue.length - queue.length) + 6 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      ((final.pc = word width conflict ∧
        ¬ ∃ assignment : Fin graph.nodeCount → Bool, ∀ other : Fin clauses.length,
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
    exact ⟨queue, fired, final, 6, Nat.le_refl _, initial.fifo.nodup, ordered, by omega, trace, size, stack, output,
      finished.running, Or.inr ⟨finished,
        empty_complete clauses recordStart queue fired (by simpa only [equal] using complete), meaning, forced⟩⟩
  | succ budget ih =>
    by_cases equal : head = queue.length
    · have atEnd : Ready clauses recordStart recordEnd base fetch queue queue.length fired state := by simpa only [equal] using initial
      obtain ⟨final, trace, finished, size, stack, output⟩ := fifo_empty clauses recordStart recordEnd base fetch done bucket program queue fired state atEnd fetchAt fetchCapacity
      exact ⟨queue, fired, final, 6, Nat.le_refl _, initial.fifo.nodup, ordered, by omega, trace, size, stack, output,
        finished.running, Or.inr ⟨finished,
        empty_complete clauses recordStart queue fired (by simpa only [equal] using complete), meaning, forced⟩⟩
    · have nonempty : head < queue.length := by have := initial.headBound; omega
      obtain ⟨active, nextQueue, middle, firstTicks, activeValue, growth, unique, prefixEqual, middleOrdered, firstBound, first,
          middleSize, middleStack, middleOutput, middleRunning, outcome⟩ := ordered_semantic_cycle graph clauses recordStart recordEnd base
        fetch done bucket advance ready skip conflict program queue head fired state initial complete meaning forced dependencies ordered nonempty separated fetchAt advanceAt
        loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
      have fresh : active ∉ queue.take head := by
        have taken : (queue.take (head + 1)).Nodup := initial.fifo.nodup.take
        rw [List.take_add_one, activeValue] at taken
        have disjoint := (List.nodup_append.mp taken).2.2
        intro member
        exact disjoint active member active (by simp) rfl
      have partition := incidence_partition (IndexScan.occurrences clauses recordStart) (queue.take head) active fresh
      rcases outcome with conflictPC | ⟨nextFired, nextReady, promoted, nextComplete, nextMeaning, nextForced⟩
      · exact ⟨nextQueue, fired, middle, firstTicks, growth, unique, middleOrdered, by omega, first,
          middleSize, middleStack, middleOutput, middleRunning, Or.inl conflictPC⟩
      · obtain ⟨finalQueue, finalFired, final, lastTicks, lastGrowth, finalUnique, finalOrdered, lastBound, last,
          finalSize, finalStack, finalOutput, finalRunning, result⟩ := ih (head + 1) nextQueue nextFired middle (by omega) nextReady nextComplete nextMeaning nextForced middleOrdered
        have potential : pendingIncidences (IndexScan.occurrences clauses recordStart) (nextQueue.take (head + 1)) +
            matching (IndexScan.occurrences clauses recordStart) active (IndexScan.occurrences clauses recordStart).length =
            pendingIncidences (IndexScan.occurrences clauses recordStart) (queue.take head) := by
          rw [promoted]
          exact partition.symm
        have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [middleSize, middleStack, middleOutput]
        refine ⟨finalQueue, finalFired, final, firstTicks + lastTicks, by omega, finalUnique, finalOrdered, by omega, ?_,
          finalSize.trans middleSize, finalStack.trans middleStack, finalOutput.trans middleOutput, finalRunning, result⟩
        simpa only [middleLive, Nat.max_self] using first.append last


/-- One original parent row, with every ordered child occurrence retained. -/
def dependencyClause (parent : Fin count) (children : List (Fin count)) :
    Controller.CNF.Clause (Fin count) :=
  (parent, false) :: children.map (fun child => (child, true))

@[simp] theorem dependency_false_mem (parent label : Fin count) (children : List (Fin count)) :
    (label, false) ∈ dependencyClause parent children ↔ label = parent := by
  simp [dependencyClause]

@[simp] theorem dependency_true_mem (parent label : Fin count) (children : List (Fin count)) :
    (label, true) ∈ dependencyClause parent children ↔ label ∈ children := by
  simp [dependencyClause]

theorem dependency_dual (parent : Fin count) (children : List (Fin count)) :
    Controller.Horn.DualHornClause (dependencyClause parent children) := by
  apply Or.inr
  intro left leftMem right rightMem leftSign rightSign
  obtain ⟨leftLabel, leftPolarity⟩ := left
  obtain ⟨rightLabel, rightPolarity⟩ := right
  dsimp at leftSign rightSign
  subst leftPolarity
  subst rightPolarity
  exact (dependency_false_mem parent leftLabel children).mp leftMem |>.trans
    ((dependency_false_mem parent rightLabel children).mp rightMem).symm

theorem dependency_not_tautological (parent : Fin count) (children : List (Fin count))
    (noSelf : parent ∉ children) :
    ¬ Controller.Horn.Tautological (dependencyClause parent children) := by
  rintro ⟨⟨label, sign⟩, member, opposite⟩
  cases sign with
  | false =>
    have own := (dependency_false_mem parent label children).mp member
    have child : label ∈ children := (dependency_true_mem parent label children).mp (by
      change (label, true) ∈ dependencyClause parent children at opposite
      exact opposite)
    exact noSelf (own ▸ child)
  | true =>
    have own := (dependency_false_mem parent label children).mp (by
      change (label, false) ∈ dependencyClause parent children at opposite
      exact opposite)
    have child := (dependency_true_mem parent label children).mp member
    exact noSelf (own ▸ child)

private theorem signed_dependencies (parent : Fin count) (children : List (Fin count)) :
    signedLabels (dependencyClause parent children) false = [parent] ∧
    signedLabels (dependencyClause parent children) true = children.dedup := by
  simp [signedLabels, dependencyClause, List.filter_map, Function.comp_def]

theorem compile_dependency (parent : Fin count) (children : List (Fin count))
    (noSelf : parent ∉ children) :
    compileClause (dependencyClause parent children) = .negative parent children.dedup := by
  have test : tautologyCheck (dependencyClause parent children) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    exact dependency_not_tautological parent children noSelf
      ((tautologyCheck_eq_true _).mp yes)
  simp only [compileClause, test, Bool.false_eq_true, ite_false,
    (signed_dependencies parent children).1, (signed_dependencies parent children).2]

/-- The row array follows the original node identifiers; no schedule is supplied. -/
def dependencyClauses (graph : UnorderedDAG n) :
    List (Controller.CNF.Clause (Fin graph.nodeCount)) :=
  List.ofFn (fun parent : Fin graph.nodeCount => dependencyClause parent (graph.node parent).children)

theorem dependency_compile_at (graph : UnorderedDAG n) (acyclic : graph.Acyclic)
    (parent : Fin graph.nodeCount) :
    compileClause ((dependencyClauses graph)[parent.val]'(by
      simp only [dependencyClauses, List.length_ofFn]; exact parent.isLt)) = dependencyRule graph parent := by
  simp only [dependencyClauses, List.getElem_ofFn]
  apply compile_dependency
  exact acyclic.irrefl.irrefl parent


/-- The dependency relation is derived from the original row encoder. -/
theorem dependency_source (graph : UnorderedDAG n) (acyclic : graph.Acyclic) :
    ClauseDependencies graph (dependencyClauses graph) := by
  intro index parent labels selected child incident
  have size : (dependencyClauses graph).length = graph.nodeCount := by
    simp only [dependencyClauses, List.length_ofFn]
  let original : Fin graph.nodeCount := ⟨index.val, by simpa only [size] using index.isLt⟩
  have compiled : compileClause (dependencyClauses graph)[index.val] =
      dependencyRule graph original := dependency_compile_at graph acyclic original
  have same : Rule.negative original (graph.node original).children.dedup =
      Rule.negative parent labels := compiled.symm.trans selected
  injection same with parentEq labelsEq
  have source : child ∈ (graph.node original).children := by
    simpa only [parentEq] using incident
  rw [← labelsEq]
  exact List.mem_dedup.mpr source


/-- The actual terminal model makes the ordered queue complete on an acyclic
source, so its original-ID order is a numbering of every stored node. -/
def terminal_numbering (graph : UnorderedDAG n) (acyclic : graph.Acyclic)
    (queue : List (Fin graph.nodeCount))
    (fired : Fin (dependencyClauses graph).length → Bool)
    (complete : EnabledComplete (dependencyClauses graph) queue fired)
    (meaning : FiredMeaning (dependencyClauses graph) queue fired)
    (distinct : queue.Nodup) (ordered : DependencyOrder graph queue) : graph.Numbering := by
  have models : ∀ parent, (dependencyRule graph parent).Holds (offAssignment queue) := by
    intro parent
    have source := terminal_original_models (dependencyClauses graph) queue fired complete meaning
      ⟨parent.val, by simp only [dependencyClauses, List.length_ofFn]; exact parent.isLt⟩
    rw [dependency_compile_at graph acyclic parent] at source
    exact source
  have falseAll := acyclic_models_false graph acyclic (offAssignment queue) models
  apply numbering graph queue distinct
  · intro parent
    have falseValue := falseAll parent
    simpa only [offAssignment, decide_eq_false_iff_not, not_not] using falseValue
  · exact ordered

end Controller.Cost.RawDependencyOrder
