module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucket

@[expose] public section

/-! Propagation retains the original linked incidence spine while mutating rule
counts and fired tags. The physical off flags cover all FIFO history, whereas
counts exclude only its processed prefix and the current visited bucket prefix. -/
namespace Controller.Horn.WorklistPropagation
open Controller.Cost Controller.Horn.WorklistStorage
variable {width n : Nat}

/-- The immutable part of the actual completed index, excluding mutable rows. -/
structure Spine (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (heap : Array (Word width)) : Prop where
  endpoint : heap.size = recordEnd + 2 * (IndexScan.occurrences clauses recordStart).length
  heads : ∀ label : Fin n, heap[headAddress base label]? = some (word width
    (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) label))
  nodes : ∀ index : Fin (IndexScan.occurrences clauses recordStart).length,
    NodeStored ((IndexScan.occurrences clauses recordStart)[index.val]).1
      (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take index.val)
        (IndexScan.occurrences clauses recordStart)[index.val].2)
      (recordEnd + 2 * index.val) heap
  originalEnd : recordEnd = Controller.Horn.NormalizeLoop.recordOffset clauses recordStart clauses.length
  separation : base + 2 * n + 1 ≤ recordStart
  positiveEnd : 0 < recordEnd

/-- The completed cold scan supplies the spine without constructing a new index. -/
theorem spine_of_index (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (heap : Array (Word width))
    (physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base
      (IndexScan.occurrences clauses recordStart).length heap) :
    Spine clauses recordStart recordEnd base heap := by
  refine ⟨physical.endpoint, ?_, physical.nodes, physical.originalEnd,
    physical.separation, physical.positiveEnd⟩
  intro label
  simpa only [List.take_length] using physical.headValues label

/-- A traversal prefix follows actual original predecessor pointers. Its list
contains original occurrence indices, rather than a supplied row incidence table. -/
inductive LinkPrefix (edges : List (Nat × Fin n)) (recordEnd : Nat) (active : Fin n) :
    Nat → List (Fin edges.length) → Nat → Prop where
  | nil (pointer : Nat) : LinkPrefix edges recordEnd active pointer [] pointer
  | cons (index : Fin edges.length) (rest : List (Fin edges.length)) (finish : Nat)
      (label : edges[index.val].2 = active)
      (tail : LinkPrefix edges recordEnd active
        (IndexScan.heads recordEnd (edges.take index.val) active) rest finish) :
      LinkPrefix edges recordEnd active (recordEnd + 2 * index.val) (index :: rest) finish

/-- Completed FIFO labels plus the active label only after this row's physical
node has been visited. Pending FIFO labels are deliberately excluded. -/
def processedForRow (queue : List (Fin n)) (head : Nat) (active : Option (Fin n))
    (visitedRows : List Nat) (row : Nat) : List (Fin n) :=
  queue.take head ++ if row ∈ visitedRows then active.toList else []

def remaining (rule : Controller.Horn.Worklist.Rule (Fin n))
    (processed : List (Fin n)) : Nat :=
  (rule.positives.filter fun label => decide (label ∉ processed)).length

/-- Count zero is meaningful only relative to physically processed labels. -/
theorem remaining_zero (rule : Controller.Horn.Worklist.Rule (Fin n))
    (processed : List (Fin n)) (zero : remaining rule processed = 0) :
    ∀ label ∈ rule.positives, label ∈ processed := by
  have empty : (rule.positives.filter fun label => decide (label ∉ processed)) = [] :=
    List.length_eq_zero_iff.mp zero
  intro label member
  by_contra outside
  have kept : label ∈ rule.positives.filter (fun label => decide (label ∉ processed)) := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨member, outside⟩
  rw [empty] at kept
  exact List.not_mem_nil kept

theorem remaining_le (rule : Controller.Horn.Worklist.Rule (Fin n))
    (processed : List (Fin n)) : remaining rule processed ≤ rule.positives.length :=
  List.length_filter_le _ _

/-- Only the completed prefix and a queued active label justify decrements. -/
theorem processed_subset_queue (queue : List (Fin n)) (head : Nat) (active : Option (Fin n))
    (visitedRows : List Nat) (row : Nat)
    (queued : ∀ label ∈ active.toList, label ∈ queue) :
    ∀ label ∈ processedForRow queue head active visitedRows row, label ∈ queue := by
  intro label member
  unfold processedForRow at member
  rcases List.mem_append.mp member with old | current
  · exact List.mem_of_mem_take old
  · split at current
    · exact queued label current
    · exact False.elim (List.not_mem_nil current)

/-- A zero physical count makes firing sound for the all-marked assignment,
although pending marked labels have not yet changed any stored counts. -/
theorem zero_support_queued (rule : Controller.Horn.Worklist.Rule (Fin n))
    (queue : List (Fin n)) (head : Nat) (active : Option (Fin n))
    (visitedRows : List Nat) (row : Nat)
    (queued : ∀ label ∈ active.toList, label ∈ queue)
    (zero : remaining rule (processedForRow queue head active visitedRows row) = 0) :
    ∀ label ∈ rule.positives, label ∈ queue := by
  intro label member
  exact processed_subset_queue queue head active visitedRows row queued label
    (remaining_zero rule _ zero label member)

/-- Mutable rows are related to the same original source compilation throughout. -/
structure Invariant (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (queue : List (Fin n)) (head : Nat)
    (active : Option (Fin n)) (visitedRows : List Nat) (pointer : Nat) (fired : Fin clauses.length → Bool)
    (heap : Array (Word width)) : Prop where
  spine : Spine clauses recordStart recordEnd base heap
  fifo : Controller.Horn.WorklistMark.Stored queue base heap
  headBound : head ≤ queue.length
  activeCurrent : active = queue[head]?
  idle : active = none → visitedRows = []
  path : ∀ label ∈ active.toList,
    ∃ indices : List (Fin (IndexScan.occurrences clauses recordStart).length),
      visitedRows = indices.map (fun index => (IndexScan.occurrences clauses recordStart)[index.val].1) ∧
      LinkPrefix (IndexScan.occurrences clauses recordStart) recordEnd label
        (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) label) indices pointer
  activeQueued : ∀ label ∈ active.toList, label ∈ queue
  activeFresh : ∀ label ∈ active.toList, label ∉ queue.take head
  rows : ∀ index : Fin clauses.length,
    let row := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val
    let rule := Controller.Horn.Worklist.compileClause clauses[index.val]
    MutableStored rule row (remaining rule (processedForRow queue head active visitedRows row))
      (fired index) heap

end Controller.Horn.WorklistPropagation
