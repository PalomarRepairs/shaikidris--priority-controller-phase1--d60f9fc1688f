module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucketCharge

@[expose] public section

/-! Completing a physical original bucket promotes its active FIFO label to
the processed prefix. Pending marks remain excluded from physical row counts. -/
namespace Controller.Horn.WorklistBucketComplete
open Controller.Cost Controller.Horn.WorklistPropagation
open Controller.Horn.WorklistBucketSuccessor Controller.Horn.WorklistPropagationStep
open Controller.Horn.WorklistBucketRun
variable {width n : Nat}

/-- Every physical path ending at nil covers exactly the matching original
occurrences below its starting prefix, independent of existential path choice. -/
theorem terminal_coverage (edges : List (Nat × Fin n)) (recordEnd : Nat)
    (positive : 0 < recordEnd) (active : Fin n) (bound : Nat)
    (within : bound ≤ edges.length) (pointer : Nat) (indices : List (Fin edges.length))
    (pointerEqual : pointer = IndexScan.heads recordEnd (edges.take bound) active)
    (path : LinkPrefix edges recordEnd active pointer indices 0) :
    ∀ query : Fin edges.length, query ∈ indices ↔ query.val < bound ∧ edges[query.val].2 = active := by
  induction bound using Nat.strong_induction_on generalizing pointer indices with
  | h bound ih =>
    cases path with
    | nil =>
      have absent := (head_nil_iff edges recordEnd positive active bound within).mp pointerEqual.symm
      intro query
      simp only [List.not_mem_nil, false_iff]
      intro retained
      exact absent query retained.1 retained.2
    | cons current rest finish label tail =>
      have upper := IndexScan.heads_bound recordEnd positive (edges.take bound) active
      rw [List.length_take_of_le within] at upper
      have smaller : current.val < bound := by omega
      rcases head_frontier_last edges recordEnd positive active bound within with nil | ⟨last, lastInside, lastLabel, head, latest⟩
      · have impossible : recordEnd + 2 * current.val = 0 := pointerEqual.trans nil
        omega
      · have same : last = current := by apply Fin.ext; omega
        subst last
        have covered := ih current.val smaller (by have := current.isLt; omega)
          (IndexScan.heads recordEnd (edges.take current.val) active) rest rfl tail
        intro query
        constructor
        · intro member
          rcases List.mem_cons.mp member with equal | member
          · subst query; exact ⟨smaller, label⟩
          · have retained := (covered query).mp member
            exact ⟨by omega, retained.2⟩
        · intro retained
          have lower := latest query retained.1 retained.2
          by_cases equal : query = current
          · exact List.mem_cons.mpr (Or.inl equal)
          · have different : query.val ≠ current.val := fun same => equal (Fin.ext same)
            exact List.mem_cons.mpr (Or.inr ((covered query).mpr ⟨by omega, retained.2⟩))

/-- Original positive support supplies its actual chronological occurrence. -/
theorem support_occurrence (clauses : List (Controller.CNF.Clause (Fin n))) (recordStart : Nat)
    (index : Fin clauses.length) (active : Fin n)
    (incident : active ∈ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives) :
    ∃ current : Fin (IndexScan.occurrences clauses recordStart).length,
      (IndexScan.occurrences clauses recordStart)[current.val].1 =
        Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∧
      (IndexScan.occurrences clauses recordStart)[current.val].2 = active := by
  obtain ⟨consumed, inside, value⟩ := List.mem_iff_getElem.mp incident
  have actual := Controller.Horn.IndexScanRefinement.occurrence_at_row clauses recordStart index.val consumed index.isLt inside
  rw [value] at actual
  obtain ⟨bound, pair⟩ := List.getElem?_eq_some_iff.mp actual
  refine ⟨⟨(IndexScan.occurrences (clauses.take index.val) recordStart).length + consumed, bound⟩, ?_, ?_⟩
  · exact congrArg Prod.fst pair
  · exact congrArg Prod.snd pair

/-- Nil endpoint coverage identifies visited rows with original active support. -/
theorem visited_support (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (queue : List (Fin n)) (head : Nat) (active : Fin n)
    (visited : List Nat) (fired : Fin clauses.length → Bool) (heap : Array (Word width))
    (invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired heap)
    (index : Fin clauses.length) :
    Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∈ visited ↔
      active ∈ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives := by
  obtain ⟨indices, visitedMap, path⟩ := invariant.path active (by simp)
  have coverage := terminal_coverage (IndexScan.occurrences clauses recordStart) recordEnd
    invariant.spine.positiveEnd active (IndexScan.occurrences clauses recordStart).length (Nat.le_refl _)
    (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) active) indices
    (by simp only [List.take_length]) path
  constructor
  · intro member
    rw [visitedMap] at member
    obtain ⟨current, retained, row⟩ := List.mem_map.mp member
    have label := ((coverage current).mp retained).2
    exact occurrence_incident clauses recordStart current index active row label
  · intro incident
    obtain ⟨current, row, label⟩ := support_occurrence clauses recordStart index active incident
    rw [visitedMap]
    exact List.mem_map.mpr ⟨current, (coverage current).mpr ⟨current.isLt, label⟩, row⟩

/-- Only the completed active bucket adds the FIFO head to the processed prefix. -/
theorem completed_counts (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (queue : List (Fin n)) (head : Nat) (active : Fin n)
    (visited : List Nat) (fired : Fin clauses.length → Bool) (heap : Array (Word width))
    (invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired heap)
    (index : Fin clauses.length) :
    remaining (Controller.Horn.Worklist.compileClause clauses[index.val])
      (processedForRow queue head (some active) visited (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)) =
    remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take (head + 1)) := by
  have nextPrefix : queue.take (head + 1) = queue.take head ++ [active] := by
    rw [List.take_add_one, ← invariant.activeCurrent]
    rfl
  have incident := visited_support clauses recordStart recordEnd base queue head active visited fired heap invariant index
  unfold remaining
  apply congrArg List.length
  apply List.filter_congr
  intro label member
  have membership : label ∈ processedForRow queue head (some active) visited
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) ↔ label ∈ queue.take (head + 1) := by
    by_cases visitedRow : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∈ visited
    · simp only [processedForRow, ite_eq_left visitedRow, Option.toList_some, nextPrefix]
    · have outside : active ∉ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives :=
        fun retained => visitedRow (incident.mpr retained)
      have distinct : label ≠ active := by intro equal; subst label; exact outside member
      simp only [processedForRow, ite_eq_right visitedRow, List.append_nil, nextPrefix,
        List.mem_append, List.mem_singleton, distinct, or_false]
  simp only [membership]

/-- Every original mutable row now stores the next processed-prefix count,
for any next active label before any of its physical occurrences are visited. -/
theorem rows_after_head (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (queue : List (Fin n)) (head : Nat) (active : Fin n)
    (visited : List Nat) (fired : Fin clauses.length → Bool) (heap : Array (Word width))
    (invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired heap)
    (nextActive : Option (Fin n)) :
    ∀ index : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
        (remaining (Controller.Horn.Worklist.compileClause clauses[index.val])
          (processedForRow queue (head + 1) nextActive [] (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)))
        (fired index) heap := by
  intro index
  have count := completed_counts clauses recordStart recordEnd base queue head active visited fired heap invariant index
  have stored := invariant.rows index
  change Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
    (remaining (Controller.Horn.Worklist.compileClause clauses[index.val])
      (processedForRow queue head (some active) visited (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)))
    (fired index) heap at stored
  rw [count] at stored
  simpa only [processedForRow, List.not_mem_nil, ite_false, List.append_nil] using stored

/-- Firing remains sound after the same head promotion, without promoting
other pending marked labels into physical counts. -/
theorem fired_after_head (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (queue : List (Fin n)) (head : Nat) (active : Fin n)
    (visited : List Nat) (fired : Fin clauses.length → Bool) (heap : Array (Word width))
    (invariant : Invariant clauses recordStart recordEnd base queue head (some active) visited 0 fired heap)
    (firedZero : FiredZero clauses recordStart queue head (some active) visited fired)
    (nextActive : Option (Fin n)) :
    FiredZero clauses recordStart queue (head + 1) nextActive [] fired := by
  intro index wasFired
  have old := firedZero index wasFired
  have count := completed_counts clauses recordStart recordEnd base queue head active visited fired heap invariant index
  rw [count] at old
  simpa only [processedForRow, List.not_mem_nil, ite_false, List.append_nil] using old

/-- The full fetched bucket execution supplies next-head physical counts and
fired-zero directly from its own original nil endpoint. -/
theorem bucket_processed_execution (clauses : List (Controller.CNF.Clause (Fin n)))
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
      ticks ≤ 32 * Controller.Horn.WorklistBucketCharge.matching (IndexScan.occurrences clauses recordStart) active bound +
        3 * (finalQueue.length - queue.length) + 1 ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      (final.pc = word width conflict ∨
        ∃ finalFired,
          final.pc = word width exit ∧ head + 1 ≤ finalQueue.length ∧
          Spine clauses recordStart recordEnd base final.heap ∧
          Controller.Horn.WorklistMark.Stored finalQueue base final.heap ∧
          (∀ index : Fin clauses.length,
            Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
              (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
              (remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (finalQueue.take (head + 1)))
              (finalFired index) final.heap) ∧
          FiredZero clauses recordStart finalQueue (head + 1) none [] finalFired ∧
          final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
            some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + finalQueue.length)) ∧
          final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = word width (2 ^ width - 1)) := by
  obtain ⟨finalQueue, final, ticks, growth, unique, charged, trace, size, stack, output, running, outcome⟩ :=
    Controller.Horn.WorklistBucketCharge.bucket_charged clauses recordStart recordEnd base entry exit ready skip conflict program
      head active separated loopAt readyAt capacity readyCapacity bound queue visited fired state snapshot
  refine ⟨finalQueue, final, ticks, growth, unique, charged, trace, size, stack, output, running, ?_⟩
  rcases outcome with conflictPC | ⟨finalVisited, finalFired, exitPC, invariant, firedZero, tail, zero, one, decrement⟩
  · exact Or.inl conflictPC
  · obtain ⟨headBound, _⟩ := List.getElem?_eq_some_iff.mp invariant.activeCurrent.symm
    have rows := rows_after_head clauses recordStart recordEnd base finalQueue head active finalVisited finalFired final.heap invariant none
    have zeroFired := fired_after_head clauses recordStart recordEnd base finalQueue head active finalVisited finalFired final.heap
      invariant firedZero none
    refine Or.inr ⟨finalFired, exitPC, by omega, invariant.spine, invariant.fifo, ?_, zeroFired, tail, zero, one, decrement⟩
    simpa only [processedForRow, List.not_mem_nil, ite_false, List.append_nil] using rows

end Controller.Horn.WorklistBucketComplete
