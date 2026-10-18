module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucketNegative

@[expose] public section

/-! Traversal bounds use prefixes of the original chronological occurrence list.
Each stored predecessor belongs to a smaller prefix of that same list. -/
namespace Controller.Horn.WorklistBucketRun
open Controller.Cost Controller.Horn.WorklistPropagation
open Controller.Horn.WorklistBucketSuccessor Controller.Horn.WorklistPropagationStep
variable {width n : Nat}

/-- A nonempty physical bucket supplies an original occurrence below its
prefix bound, with the active label and the exact stored predecessor. -/
theorem head_frontier (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (bound : Nat)
    (within : bound ≤ edges.length) :
    IndexScan.heads recordEnd (edges.take bound) active = 0 ∨
      ∃ index : Fin edges.length, index.val < bound ∧
        edges[index.val].2 = active ∧
        IndexScan.heads recordEnd (edges.take bound) active = recordEnd + 2 * index.val := by
  induction bound with
  | zero => exact Or.inl (by simp [IndexScan.heads])
  | succ bound ih =>
      have valid : bound < edges.length := by omega
      have previous := ih (by omega)
      have equation := IndexScan.heads_append recordEnd positive (edges.take bound)
        edges[bound].1 edges[bound].2 active
      rw [List.take_succ_eq_append_getElem valid] 
      rw [equation, List.length_take_of_le (by omega)]
      by_cases matchLabel : active = edges[bound].2
      · exact Or.inr ⟨⟨bound, valid⟩, by change bound < bound + 1; omega, matchLabel.symm, by simp [matchLabel]⟩
      · rcases previous with nil | ⟨index, less, label, pointer⟩
        · exact Or.inl (by simpa only [ite_eq_right matchLabel] using nil)
        · exact Or.inr ⟨index, by omega, label, by simpa only [ite_eq_right matchLabel] using pointer⟩

/-- Nil is characterized by the absence of the active label in the exact
original occurrence prefix, rather than a supplied incidence table. -/
theorem head_nil_iff (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (bound : Nat)
    (within : bound ≤ edges.length) :
    IndexScan.heads recordEnd (edges.take bound) active = 0 ↔
      ∀ index : Fin edges.length, index.val < bound → edges[index.val].2 ≠ active := by
  induction bound with
  | zero => simp [IndexScan.heads]
  | succ bound ih =>
      have valid : bound < edges.length := by omega
      have equation := IndexScan.heads_append recordEnd positive (edges.take bound)
        edges[bound].1 edges[bound].2 active
      have old := ih (by omega)
      rw [List.take_succ_eq_append_getElem valid, equation,
        List.length_take_of_le (by omega)]
      constructor
      · intro nil index less
        by_cases same : active = edges[bound].2
        · simp only [ite_eq_left same] at nil
          omega
        · have oldNil : IndexScan.heads recordEnd (edges.take bound) active = 0 := by
            simpa only [ite_eq_right same] using nil
          by_cases equal : index.val = bound
          · simpa only [equal] using Ne.symm same
          · exact old.mp oldNil index (by omega)
      · intro absent
        have distinct := absent ⟨bound, valid⟩ (by change bound < bound + 1; omega)
        have oldNil := old.mpr (fun index less => absent index (by omega))
        simp only [ite_eq_right (Ne.symm distinct), oldNil]

/-- The current stored head is the last matching original occurrence in its
prefix; every other active occurrence belongs to the stored predecessor prefix. -/
theorem head_frontier_last (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (bound : Nat)
    (within : bound ≤ edges.length) :
    IndexScan.heads recordEnd (edges.take bound) active = 0 ∨
      ∃ index : Fin edges.length, index.val < bound ∧ edges[index.val].2 = active ∧
        IndexScan.heads recordEnd (edges.take bound) active = recordEnd + 2 * index.val ∧
        ∀ query : Fin edges.length, query.val < bound → edges[query.val].2 = active → query.val ≤ index.val := by
  induction bound with
  | zero => exact Or.inl (by simp [IndexScan.heads])
  | succ bound ih =>
      have valid : bound < edges.length := by omega
      have previous := ih (by omega)
      have equation := IndexScan.heads_append recordEnd positive (edges.take bound)
        edges[bound].1 edges[bound].2 active
      rw [List.take_succ_eq_append_getElem valid, equation,
        List.length_take_of_le (by omega)]
      by_cases matchLabel : active = edges[bound].2
      · refine Or.inr ⟨⟨bound, valid⟩, by change bound < bound + 1; omega, matchLabel.symm, by simp [matchLabel], ?_⟩
        intro query less _
        change query.val ≤ bound
        omega
      · rcases previous with nil | ⟨index, less, label, pointer, last⟩
        · exact Or.inl (by simpa only [ite_eq_right matchLabel] using nil)
        · refine Or.inr ⟨index, by omega, label, by simpa only [ite_eq_right matchLabel] using pointer, ?_⟩
          intro query queryLess queryLabel
          have different : query.val ≠ bound := by
            intro equal
            have same : active = edges[bound].2 := by simpa only [equal] using queryLabel.symm
            exact matchLabel same
          exact last query (by omega) queryLabel

/-- Coverage follows from actual last-matching pointers, including every
original occurrence of the active label exactly once. -/
theorem complete_path_coverage (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (bound : Nat)
    (within : bound ≤ edges.length) :
    ∃ indices : List (Fin edges.length),
      LinkPrefix edges recordEnd active (IndexScan.heads recordEnd (edges.take bound) active) indices 0 ∧
      indices.length ≤ bound ∧
      ∀ query : Fin edges.length, query ∈ indices ↔ query.val < bound ∧ edges[query.val].2 = active := by
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
      rcases head_frontier_last edges recordEnd positive active bound within with nil | ⟨index, less, label, pointer, last⟩
      · refine ⟨[], ?_, by simp, ?_⟩
        · simpa only [nil] using LinkPrefix.nil (edges := edges) (recordEnd := recordEnd) (active := active) 0
        · intro query
          simp only [List.not_mem_nil, false_iff]
          intro matchNode
          exact (head_nil_iff edges recordEnd positive active bound within).mp nil query matchNode.1 matchNode.2
      · obtain ⟨rest, path, length, covered⟩ := ih index.val less (by have := index.isLt; omega)
        refine ⟨index :: rest, ?_, ?_, ?_⟩
        · simpa only [pointer] using LinkPrefix.cons index rest 0 label path
        · simp only [List.length_cons]; omega
        · intro query
          constructor
          · intro member
            rcases List.mem_cons.mp member with equal | member
            · subst query; exact ⟨less, label⟩
            · have retained := (covered query).mp member
              exact ⟨by omega, retained.2⟩
          · intro retained
            have upper := last query retained.1 retained.2
            by_cases equal : query = index
            · exact List.mem_cons.mpr (Or.inl equal)
            · have different : query.val ≠ index.val := fun same => equal (Fin.ext same)
              exact List.mem_cons.mpr (Or.inr ((covered query).mpr ⟨by omega, retained.2⟩))

/-- Finite original-prefix descent constructs the entire physical chain. -/
theorem complete_path (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (bound : Nat)
    (within : bound ≤ edges.length) :
    ∃ indices : List (Fin edges.length),
      LinkPrefix edges recordEnd active (IndexScan.heads recordEnd (edges.take bound) active) indices 0 ∧
      indices.length ≤ bound := by
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
      rcases head_frontier edges recordEnd positive active bound within with nil | ⟨index, less, label, pointer⟩
      · exact ⟨[], by simpa only [nil] using LinkPrefix.nil (edges := edges) (recordEnd := recordEnd) (active := active) 0, by simp⟩
      · obtain ⟨rest, path, length⟩ := ih index.val less (by have := index.isLt; omega)
        refine ⟨index :: rest, ?_, ?_⟩
        · simpa only [pointer] using LinkPrefix.cons index rest 0 label path
        · simp only [List.length_cons]; omega

/-- The actual fetched nil test returns to the fixed caller exit while
preserving the original spine, all rows, FIFO, and live storage. -/
theorem nil_endpoint (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (state : State width 8)
    (invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired state.heap)
    (firedZero : FiredZero clauses recordStart queue head (some active) visited fired)
    (present : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (held : state.reg 0 = word width 0) (position : state.pc = word width entry)
    (running : state.halted = false) (capacity : entry + 12 < 2 ^ width) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired final.heap ∧
      FiredZero clauses recordStart queue head (some active) visited fired ∧
      final.reg = state.reg ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.pc = word width exit ∧ final.halted = false := by
  obtain ⟨trace, pc⟩ := Controller.Horn.WorklistBucketLoop.nil_execution program entry exit ready state present held position running capacity
  obtain ⟨registers, heap, stack, output, halted, live⟩ := Controller.Horn.RuleDispatch.branchFinished_frame state 0 exit
  refine ⟨Controller.Horn.RuleDispatch.branchFinished state 0 exit, trace, ?_, firedZero,
    registers, heap, stack, output, pc, halted.trans running⟩
  simpa only [heap] using invariant

/-- The checked nonzero successor preserves the actual FIFO tail header.
The heap projection is recovered from the same twelve fetched instructions. -/
theorem nonzero_tail (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (index : Fin clauses.length)
    (current : Fin (IndexScan.occurrences clauses recordStart).length) (state : State width 8)
    (invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited
      (recordEnd + 2 * current.val) fired state.heap)
    (firedZero : FiredZero clauses recordStart queue head (some active) visited fired)
    (sourceRow : (IndexScan.occurrences clauses recordStart)[current.val].1 =
      Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
    (sourceLabel : (IndexScan.occurrences clauses recordStart)[current.val].2 = active)
    (nonzero : 0 < rowCounts clauses recordStart queue head active visited index - 1)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (tail : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
      some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + queue.length)))
    (held : state.reg 0 = word width (recordEnd + 2 * current.val))
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 12 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 12 state.liveWords ∧
      Invariant clauses recordStart recordEnd base queue head (some active)
        (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
        (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active) fired final.heap ∧
      FiredZero clauses recordStart queue head (some active)
        (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val]) fired ∧
      final.reg 0 = word width (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1) ∧
      final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
        some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + queue.length)) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false := by
  obtain ⟨final, trace, nextInvariant, nextFired, next, nextZero, nextOne, nextDecrement,
    size, stack, output, pc, live⟩ := nonzero_successor clauses recordStart recordEnd base entry exit ready
      program queue head active visited fired index current state invariant firedZero sourceRow sourceLabel
      nonzero separated present held one zero decrement position running capacity room
  have countPositive : 0 < rowCounts clauses recordStart queue head active visited index := by omega
  have stored : Controller.Horn.WorklistStorage.MutableStored
      (Controller.Horn.Worklist.compileClause clauses[index.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
      (rowCounts clauses recordStart queue head active visited index - 1 + 1) (fired index) state.heap := by
    have original := invariant.rows index
    have count : rowCounts clauses recordStart queue head active visited index =
        rowCounts clauses recordStart queue head active visited index - 1 + 1 := by omega
    change Controller.Horn.WorklistStorage.MutableStored
      (Controller.Horn.Worklist.compileClause clauses[index.val])
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
  have equal := Controller.Horn.JoinedRuleFrame.execution_endpoint_unique trace sameTrace
  have rowLower : recordStart ≤ Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val := by
    unfold Controller.Horn.NormalizeLoop.recordOffset
    omega
  have unchanged : same.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
      state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? := by
    rw [heap]
    exact Array.getElem?_set_ne (by have := stored.fits; omega)
      (by unfold Controller.Horn.WorklistBucketReady.tailSlot; omega)
  refine ⟨final, trace, nextInvariant, nextFired, next, nextZero, nextOne, nextDecrement,
    ?_, size, stack, output, pc, live⟩
  simpa only [equal] using unchanged.trans tail

/-- Machine state at a physical bucket loop entry. Pending queue additions do
not alter the processed head or the original active occurrence prefix. -/
structure Snapshot (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry : Nat) (queue : List (Fin n)) (head : Nat)
    (active : Fin n) (visited : List Nat) (fired : Fin clauses.length → Bool)
    (bound : Nat) (state : State width 8) : Prop where
  within : bound ≤ (IndexScan.occurrences clauses recordStart).length
  invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited
    (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take bound) active) fired state.heap
  firedZero : FiredZero clauses recordStart queue head (some active) visited fired
  tail : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
    some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + queue.length))
  held : state.reg 0 = word width (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take bound) active)
  zero : state.reg 2 = word width 0
  one : state.reg 5 = word width 1
  decrement : state.reg 6 = word width (2 ^ width - 1)
  position : state.pc = word width entry
  running : state.halted = false
  room : state.heap.size < 2 ^ width

/-- One nonnil fetched iteration either follows the real predecessor with the
complete processed-count invariant, or reaches the original positive conflict.
The source row is inverted from the stored occurrence itself. -/
theorem step_runtime (clauses : List (Controller.CNF.Clause (Fin n)))
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
      nextBound < bound ∧ 12 ≤ ticks ∧ ticks ≤ 35 ∧
      Execution program state final ticks state.liveWords ∧
      Snapshot clauses recordStart recordEnd base entry nextQueue head active nextVisited nextFired nextBound final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output) ∨
    (∃ final, Execution program state final 15 state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width conflict ∧ final.halted = false) := by
  rcases head_frontier (IndexScan.occurrences clauses recordStart) recordEnd
    snapshot.invariant.spine.positiveEnd active bound snapshot.within with nil | ⟨current, less, label, pointer⟩
  · exact False.elim (nonnil nil)
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
        (if forcedHead ∈ queue then 32 else 35), less, ?_, ?_, trace, ?_, size, stack, output⟩
      · split <;> omega
      · split <;> omega
      · exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
          decrement, pc, running, by simpa only [size] using snapshot.room⟩
  · have positiveCount : 0 < rowCounts clauses recordStart queue head active visited index - 1 := by omega
    obtain ⟨final, trace, nextInvariant, nextFired, next, zero, one, decrement, tail,
        size, stack, output, pc, running⟩ := nonzero_tail clauses recordStart recordEnd base entry exit ready program
      queue head active visited fired index current state invariant snapshot.firedZero sourceRow label positiveCount
      separated loopAt snapshot.tail held snapshot.one snapshot.zero snapshot.decrement snapshot.position snapshot.running capacity snapshot.room
    refine Or.inl ⟨queue, visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val],
      fired, current.val, final, 12, less, by omega, by omega, trace, ?_, size, stack, output⟩
    exact ⟨by have := current.isLt; omega, nextInvariant, nextFired, tail, next, zero, one,
      decrement, pc, running, by simpa only [size] using snapshot.room⟩

/-- Complete execution of the original physical linked bucket. The induction
uses the stored predecessor's smaller original prefix and actual fetched
branch endpoints; no traversal or successor oracle is assumed. -/
theorem bucket_runtime (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry exit ready skip conflict : Nat) (program : Program width 8)
    (head : Nat) (active : Fin n)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program entry exit ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := n) program base ready skip conflict entry)
    (capacity : entry + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (bound : Nat) (queue : List (Fin n)) (visited : List Nat)
    (fired : Fin clauses.length → Bool) (state : State width 8)
    (snapshot : Snapshot clauses recordStart recordEnd base entry queue head active visited fired bound state) :
    ∃ final ticks, ticks ≤ 35 * bound + 1 ∧ Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      (final.pc = word width conflict ∨
        ∃ finalQueue finalVisited finalFired,
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
      refine ⟨final, 1, by omega, trace, by simpa only [heap], stack, output, running,
        Or.inr ⟨queue, visited, fired, pc, finalInvariant, finalFired, ?_, ?_, ?_, ?_⟩⟩
      · simpa only [heap] using snapshot.tail
      · exact (congrFun registers 2).trans snapshot.zero
      · exact (congrFun registers 5).trans snapshot.one
      · exact (congrFun registers 6).trans snapshot.decrement
    · have positiveBound : 0 < bound := by
        by_contra notPositive
        have empty : bound = 0 := by omega
        simp [empty, IndexScan.heads] at nil
      rcases step_runtime clauses recordStart recordEnd base entry exit ready skip conflict program queue head active
        visited fired bound state snapshot nil separated loopAt readyAt capacity readyCapacity with continued | failed
      · obtain ⟨nextQueue, nextVisited, nextFired, nextBound, middle, firstTicks,
          smaller, _, firstBound, first, middleSnapshot, middleSize, middleStack, middleOutput⟩ := continued
        obtain ⟨final, lastTicks, lastBound, last, finalSize, finalStack, finalOutput, running, outcome⟩ :=
          ih nextBound smaller nextQueue nextVisited nextFired middle middleSnapshot
        have middleLive : middle.liveWords = state.liveWords := by
          unfold State.liveWords
          rw [middleSize, middleStack, middleOutput]
        refine ⟨final, firstTicks + lastTicks, by omega, ?_, finalSize.trans middleSize,
          finalStack.trans middleStack, finalOutput.trans middleOutput, running, outcome⟩
        simpa only [middleLive, Nat.max_self] using first.append last
      · obtain ⟨final, trace, size, stack, output, pc, running⟩ := failed
        exact ⟨final, 15, by omega, trace, size, stack, output, running, Or.inl pc⟩

end Controller.Horn.WorklistBucketRun
