module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucketFrame

@[expose] public section

/-! Original physical bucket successors refine processed-prefix counts. Ghost
indices name the unchanged source occurrence list, never a rebuilt incidence table. -/
namespace Controller.Horn.WorklistBucketSuccessor
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.WorklistPropagation
open Controller.Horn.WorklistPropagationStep
variable {width n : Nat}

/-- Every original occurrence lies at or above the source record start. -/
theorem occurrence_row_lower (clauses : List (Controller.CNF.Clause (Fin n))) (start row : Nat)
    (label : Fin n) (member : (row, label) ∈ IndexScan.occurrences clauses start) : start ≤ row := by
  induction clauses generalizing start with
  | nil => simp [IndexScan.occurrences] at member
  | cons clause rest ih =>
      simp only [IndexScan.occurrences, List.mem_append] at member
      rcases member with first | tail
      · obtain ⟨channel, _, equal⟩ := List.mem_map.mp first
        have rowEqual := congrArg Prod.fst equal
        simpa using Nat.le_of_eq rowEqual
      · have lower := ih _ tail
        omega

/-- Source normalization gives one physical occurrence for each row/label pair. -/
theorem occurrences_nodup (clauses : List (Controller.CNF.Clause (Fin n))) (start : Nat) :
    (IndexScan.occurrences clauses start).Nodup := by
  induction clauses generalizing start with
  | nil => simp [IndexScan.occurrences]
  | cons clause rest ih =>
      rw [IndexScan.occurrences, List.nodup_append]
      refine ⟨?_, ih _, ?_⟩
      · apply (Controller.Horn.Worklist.compileClause_positives_nodup clause).map
        intro left right equal
        exact congrArg Prod.snd equal
      · intro first firstMember second secondMember equal
        obtain ⟨label, _, firstEqual⟩ := List.mem_map.mp firstMember
        have firstRow : first.1 = start := (congrArg Prod.fst firstEqual).symm
        have lower := occurrence_row_lower rest _ second.1 second.2 secondMember
        have same := congrArg Prod.fst equal
        omega

/-- A physical predecessor traversal may append its actual next linked node. -/
theorem prefix_append (edges : List (Nat × Fin n)) (recordEnd : Nat) (active : Fin n)
    (start middle finish : Nat) (before after : List (Fin edges.length))
    (first : LinkPrefix edges recordEnd active start before middle)
    (second : LinkPrefix edges recordEnd active middle after finish) :
    LinkPrefix edges recordEnd active start (before ++ after) finish := by
  induction first with
  | nil => simpa using second
  | cons index rest terminal label tail ih =>
      exact LinkPrefix.cons index (rest ++ after) finish label (ih second)

/-- Every node on an actual bucket path carries its active label. -/
theorem prefix_labels (edges : List (Nat × Fin n)) (recordEnd : Nat) (active : Fin n)
    (start finish : Nat) (indices : List (Fin edges.length))
    (path : LinkPrefix edges recordEnd active start indices finish) :
    ∀ index ∈ indices, edges[index.val].2 = active := by
  induction path with
  | nil => simp
  | cons index rest finish label tail ih =>
      intro query member
      rcases List.mem_cons.mp member with equal | member
      · subst query; exact label
      · exact ih query member

/-- Unique original pairs and descending physical links exclude a repeated row
in the active bucket, even when different source clauses have equal contents. -/
theorem current_row_unvisited (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd : Nat) (active : Fin n)
    (indices : List (Fin (IndexScan.occurrences clauses recordStart).length))
    (current : Fin (IndexScan.occurrences clauses recordStart).length)
    (path : LinkPrefix (IndexScan.occurrences clauses recordStart) recordEnd active
      (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) active) indices
      (recordEnd + 2 * current.val))
    (label : (IndexScan.occurrences clauses recordStart)[current.val].2 = active)
    (positive : 0 < recordEnd) :
    (IndexScan.occurrences clauses recordStart)[current.val].1 ∉
      indices.map (fun index => (IndexScan.occurrences clauses recordStart)[index.val].1) := by
  let next := IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active
  have complete := prefix_append _ recordEnd active _ _ next indices [current] path
    (LinkPrefix.cons current [] next label (LinkPrefix.nil next))
  have unique := prefix_nodup _ recordEnd positive active _ next _ complete
  have currentFresh : current ∉ indices := by
    have separated := (List.nodup_append.mp unique).2.2
    intro member
    exact separated current member current (by simp) rfl
  intro rowMember
  obtain ⟨earlier, member, rowEqual⟩ := List.mem_map.mp rowMember
  have earlierLabel := prefix_labels _ recordEnd active _ _ indices path earlier member
  have pairEqual : (IndexScan.occurrences clauses recordStart)[earlier.val] =
      (IndexScan.occurrences clauses recordStart)[current.val] := by
    apply Prod.ext
    · exact rowEqual
    · exact earlierLabel.trans label.symm
  have indexEqual : earlier = current := Fin.ext ((List.getElem_inj (occurrences_nodup clauses recordStart)).mp pairEqual)
  exact currentFresh (indexEqual ▸ member)

/-- Appending a visited row has exactly the same processed membership as consing it. -/
theorem processed_visit (queue : List (Fin n)) (head : Nat) (active : Fin n)
    (visited : List Nat) (row query : Nat) :
    processedForRow queue head (some active) (visited ++ [row]) query =
      processedForRow queue head (some active) (row :: visited) query := by
  by_cases equal : query = row <;> by_cases old : query ∈ visited <;>
    simp [processedForRow, equal, old]

/-- A fresh visit changes only its original row's remaining count. -/
theorem visited_count_successor (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart : Nat) (queue : List (Fin n)) (head : Nat) (active : Fin n)
    (visited : List Nat) (index : Fin clauses.length)
    (unvisited : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∉ visited)
    (incident : active ∈ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives)
    (fresh : active ∉ queue.take head) :
    ∀ other : Fin clauses.length,
      remaining (Controller.Horn.Worklist.compileClause clauses[other.val])
        (processedForRow queue head (some active)
          (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)) =
      if other = index then
        remaining (Controller.Horn.Worklist.compileClause clauses[other.val])
          (processedForRow queue head (some active) visited
            (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)) - 1
      else remaining (Controller.Horn.Worklist.compileClause clauses[other.val])
        (processedForRow queue head (some active) visited
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)) := by
  intro other
  by_cases equal : other = index
  · subst other
    rw [processed_visit]
    simpa using fresh_visit_count (Controller.Horn.Worklist.compileClause clauses[index.val])
      (Controller.Horn.Worklist.compileClause_positives_nodup clauses[index.val]) queue head active visited
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) unvisited incident fresh
  · have outside := Controller.Horn.WorklistBucketFrame.original_record_disjoint clauses recordStart index other equal
    have different : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val ≠
        Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val := by
      rcases outside with before | after <;> omega
    simp [processedForRow, List.mem_append, different, equal]


/-- Each original physical pair identifies an original clause and retained support label. -/
theorem occurrence_source (clauses : List (Controller.CNF.Clause (Fin n))) (start row : Nat)
    (label : Fin n) (member : (row, label) ∈ IndexScan.occurrences clauses start) :
    ∃ index : Fin clauses.length, row = Controller.Horn.NormalizeLoop.recordOffset clauses start index.val ∧
      label ∈ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives := by
  induction clauses generalizing start with
  | nil => simp [IndexScan.occurrences] at member
  | cons clause rest ih =>
      simp only [IndexScan.occurrences, List.mem_append] at member
      rcases member with first | tail
      · obtain ⟨channel, retained, equal⟩ := List.mem_map.mp first
        refine ⟨⟨0, by simp⟩, ?_, ?_⟩
        · simpa [Controller.Horn.NormalizeLoop.recordOffset] using (congrArg Prod.fst equal).symm
        · have channelEqual : channel = label := congrArg Prod.snd equal
          simpa only [List.getElem_cons_zero, channelEqual] using retained
      · obtain ⟨index, rowEqual, retained⟩ := ih _ tail
        refine ⟨⟨index.val + 1, by have := index.isLt; simp only [List.length_cons]; omega⟩, ?_, ?_⟩
        · simpa [Controller.Horn.NormalizeLoop.recordOffset, List.take_succ_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rowEqual
        · simpa only [List.getElem_cons_succ] using retained

/-- Incident support is derived from the unchanged original occurrence pair. -/
theorem occurrence_incident (clauses : List (Controller.CNF.Clause (Fin n))) (start : Nat)
    (edge : Fin (IndexScan.occurrences clauses start).length) (index : Fin clauses.length) (active : Fin n)
    (sourceRow : (IndexScan.occurrences clauses start)[edge.val].1 =
      Controller.Horn.NormalizeLoop.recordOffset clauses start index.val)
    (sourceLabel : (IndexScan.occurrences clauses start)[edge.val].2 = active) :
    active ∈ (Controller.Horn.Worklist.compileClause clauses[index.val]).positives := by
  obtain ⟨other, rowEqual, retained⟩ := occurrence_source clauses start
    (IndexScan.occurrences clauses start)[edge.val].1 (IndexScan.occurrences clauses start)[edge.val].2
    (List.getElem_mem edge.isLt)
  have equal : other = index := by
    by_contra different
    have outside := Controller.Horn.WorklistBucketFrame.original_record_disjoint clauses start index other different
    rcases outside with before | after <;> omega
  subst other
  simpa only [sourceLabel] using retained


theorem processed_visit_subset (queue : List (Fin n)) (head : Nat) (active : Fin n)
    (visited : List Nat) (row query : Nat) :
    ∀ label ∈ processedForRow queue head (some active) visited query,
      label ∈ processedForRow queue head (some active) (visited ++ [row]) query := by
  intro label member
  simp only [processedForRow, List.mem_append] at member ⊢
  rcases member with processedPrefix | current
  · exact Or.inl processedPrefix
  · by_cases old : query ∈ visited
    · have extended : query ∈ visited ∨ query ∈ [row] := Or.inl old
      exact Or.inr (by simpa only [ite_eq_left extended] using (by simpa only [ite_eq_left old] using current))
    · simp only [ite_eq_right old, List.not_mem_nil] at current

def rowCounts (clauses : List (Controller.CNF.Clause (Fin n))) (start : Nat)
    (queue : List (Fin n)) (head : Nat) (active : Fin n) (visited : List Nat) : Fin clauses.length → Nat :=
  fun index => remaining (Controller.Horn.Worklist.compileClause clauses[index.val])
    (processedForRow queue head (some active) visited (Controller.Horn.NormalizeLoop.recordOffset clauses start index.val))

/-- A complete fetched nonzero iteration advances the actual original linked
prefix and preserves the full processed-count and fired-zero invariants. -/
theorem nonzero_successor (clauses : List (Controller.CNF.Clause (Fin n)))
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
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false := by
  obtain ⟨indices, visitedMap, path⟩ := invariant.path active (by simp)
  have fresh := invariant.activeFresh active (by simp)
  have unvisited : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val ∉ visited := by
    simpa only [sourceRow, ← visitedMap] using current_row_unvisited clauses recordStart recordEnd active indices current
      path sourceLabel invariant.spine.positiveEnd
  have incident := occurrence_incident clauses recordStart current index active sourceRow sourceLabel
  have predecessorPositive := fresh_visit_positive (Controller.Horn.Worklist.compileClause clauses[index.val]) queue head active visited
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) unvisited incident fresh
  have notFired := fresh_row_not_fired clauses recordStart queue head active visited fired firedZero index unvisited incident fresh
  have countAt : rowCounts clauses recordStart queue head active visited index =
      (rowCounts clauses recordStart queue head active visited index - 1) + 1 := by
    unfold rowCounts
    omega
  obtain ⟨final, trace, finalSpine, finalFifo, finalRows, finalNext, finalZero, finalOne, finalDecrement,
      size, stack, output, pc, live⟩ := Controller.Horn.WorklistBucketChain.nonzero_original_iteration clauses
        recordStart recordEnd base entry exit ready program queue (rowCounts clauses recordStart queue head active visited) fired
        index current (rowCounts clauses recordStart queue head active visited index - 1) state invariant.spine invariant.fifo
        invariant.rows sourceRow countAt nonzero separated present held one zero decrement position running capacity room
  have extendedPath := prefix_append _ recordEnd active _ _ _ indices [current] path
    (LinkPrefix.cons current [] _ sourceLabel (LinkPrefix.nil _))
  have finalInvariant : Invariant clauses recordStart recordEnd base queue head (some active)
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
      (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take current.val) active) fired final.heap := by
    refine ⟨finalSpine, finalFifo, invariant.headBound, invariant.activeCurrent, ?_, ?_, invariant.activeQueued,
      invariant.activeFresh, ?_⟩
    · simp
    · intro label member
      have equal : label = active := by simpa using member
      subst label
      refine ⟨indices ++ [current], ?_, extendedPath⟩
      simp only [List.map_append, List.map_cons, List.map_nil, sourceRow, ← visitedMap]
    · intro other
      have countEqual := visited_count_successor clauses recordStart queue head active visited index unvisited incident fresh other
      have values : remaining (Controller.Horn.Worklist.compileClause clauses[other.val])
          (processedForRow queue head (some active)
            (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val])
            (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)) =
          if other = index then rowCounts clauses recordStart queue head active visited index - 1
          else rowCounts clauses recordStart queue head active visited other := by
        by_cases equal : other = index <;> simpa [rowCounts, equal] using countEqual
      simpa only [← values] using finalRows other
  have finalFiredZero : FiredZero clauses recordStart queue head (some active)
      (visited ++ [Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val]) fired := by
    intro other wasFired
    apply zero_monotone _ _ _
      (processed_visit_subset queue head active visited
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val))
      (firedZero other wasFired)
  refine ⟨final, trace, finalInvariant, finalFiredZero, ?_, finalZero, finalOne, finalDecrement, size, stack, output, pc, live⟩
  simpa only [sourceLabel] using finalNext

end Controller.Horn.WorklistBucketSuccessor
