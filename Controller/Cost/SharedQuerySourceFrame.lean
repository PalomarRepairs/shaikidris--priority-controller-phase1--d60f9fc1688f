module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQueryReuseCode

@[expose] public section

namespace Controller.Cost.SharedQuerySourceFrame
open Controller.Cost.GateProgram Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroBackendFrame
open Controller.Cost.ForestZeroEmit Controller.Native Controller.Native.SourceController
open Controller.Cost.SharedZeroResidentConditions

def layout (before after : State width 8) (original : Layout ambient before.heap.size)
    (sameSize : after.heap.size = before.heap.size) : Layout ambient after.heap.size where
  tableBase := original.tableBase
  inverseBase := original.inverseBase
  tableBound := by rw [sameSize]; exact original.tableBound
  inverseBound := by rw [sameSize]; exact original.inverseBound
  disjoint := original.disjoint

theorem transport (parameters : Parameters) (before after : State width 8)
    (original : Layout ambient before.heap.size) (references : List (List (Reference ambient)))
    (sourceEnd nodes : Nat)
    (source : SourceConditions parameters before original references sourceEnd nodes)
    (sameSize : after.heap.size = before.heap.size)
    (frame : PrefixFrame sourceEnd before.heap after.heap) :
    SourceConditions parameters after (layout before after original sameSize) references sourceEnd nodes := by
  refine {
    sourceReferences := fun reference member => stored_reference_prefix (source.sourceReferences reference member) frame
    sourceBeforeTable := source.sourceBeforeTable
    sourceBeforeInverse := source.sourceBeforeInverse
    sourceBound := by rw [sameSize]; exact source.sourceBound
    sourcePositive := source.sourcePositive
    sourceChannel := (frame.2.2 0 source.sourcePositive).trans source.sourceChannel
    sourceNodes := (frame.2.2 1 source.sourceHeaderRoom).trans source.sourceNodes
    ambientEq := source.ambientEq
    adjacent := source.adjacent
    tablePositive := source.tablePositive
    sourceHeaderRoom := source.sourceHeaderRoom
    sourceDual := source.sourceDual
    sourceEndpoint := by
      change after.heap.size = original.inverseBase + ambient
      rw [sameSize]
      exact source.sourceEndpoint
  }

theorem between_ready (sourceHeap : Array (Word width)) (before after : State width 8)
    (tableBase inverseBase beforeEntry afterEntry : Nat) (rest : List (Word width))
    (beforeReady : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase beforeEntry rest before)
    (afterReady : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase afterEntry rest after)
    (sourceBefore : sourceEnd ≤ tableBase) :
    after.heap.size = before.heap.size ∧ PrefixFrame sourceEnd before.heap after.heap := by
  refine ⟨afterReady.heapSize.trans beforeReady.heapSize.symm, ?_⟩
  refine ⟨by have := beforeReady.sourceFrame.2.1; omega,
    by have := afterReady.sourceFrame.2.1; omega, ?_⟩
  intro index below
  exact (afterReady.sourceFrame.2.2 index (by omega)).trans
    (beforeReady.sourceFrame.2.2 index (by omega)).symm

theorem zero_dualHorn (graph : Controller.Decoder.DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Fin n) (T F : Finset (Fin n)) (root : Fin graph.nodeCount)
    (coordinateBase slot : Nat) :
    Controller.Horn.DualHorn (Controller.CNF.ofClauses
      (ForestZeroAssembly.originalRows (reservedReferences
        (SharedZeroSource.references graph b target T F coordinateBase slot root)))) := by
  have dual := SharedZeroTemplate.dualHorn graph guarded b target root T F
  intro clause member
  have rows : clause ∈ ForestZeroAssembly.originalRows
      (SharedZeroSource.references graph b target T F coordinateBase slot root) ++ [[]] := by
    simpa [Controller.CNF.ofClauses, reservedReferences, ForestZeroAssembly.originalRows] using member
  rcases List.mem_append.mp rows with original | empty
  · rw [SharedZeroSource.originalRows_eq] at original
    exact dual clause (by simpa using original)
  · have same : clause = [] := by simpa using empty
    subst clause
    simp [Controller.Horn.DualHornClause, Controller.Horn.NegativeUnique]

theorem rows_separate (clauses : List (Controller.CNF.Clause (Fin ambient)))
    (coordinateBase slot : Nat) (tableBefore : coordinateBase + ambient ≤ slot) :
    ∀ reference ∈ (SharedCoordinateTable.rows coordinateBase clauses).flatten, reference.slot ≠ slot := by
  intro reference member
  obtain ⟨row, rowMember, referenceMember⟩ := List.mem_flatten.mp member
  obtain ⟨clause, clauseMember, rowEq⟩ := List.mem_map.mp rowMember
  rw [← rowEq] at referenceMember
  obtain ⟨literal, literalMember, referenceEq⟩ := List.mem_map.mp referenceMember
  rw [← referenceEq]
  change coordinateBase + literal.1.val ≠ slot
  have := literal.1.isLt
  omega

theorem references_after_root (graph : Controller.Decoder.DAG n) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (oldRoot root : Fin graph.nodeCount)
    (heap : Array (Word width)) (coordinateBase slot sourceEnd : Nat)
    (sourceBound : sourceEnd ≤ heap.size) (slotBound : slot < sourceEnd) (positive : 0 < slot)
    (header : heap[0]? = some (word width n))
    (stored : ∀ reference ∈ (SharedZeroSource.references graph b target T F coordinateBase slot oldRoot).flatten,
      StoredReference heap n sourceEnd reference)
    (tableBefore : coordinateBase + (n + graph.nodeCount) ≤ slot) :
    ∀ reference ∈ (SharedZeroSource.references graph b target T F coordinateBase slot root).flatten,
      StoredReference (heap.set slot (word width root.val) (by omega)) n sourceEnd reference := by
  intro reference member
  simp only [SharedZeroSource.references, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with fixed | queried
  · have original : reference ∈ (SharedZeroSource.references graph b target T F coordinateBase slot oldRoot).flatten := by
      simp only [SharedZeroSource.references, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.mem_append]
      exact Or.inl fixed
    exact SharedZeroRootSelect.reference_preserved heap n slot sourceEnd (word width root.val) reference
      (stored reference original) (by omega) positive
      (rows_separate (SharedZeroSource.fixedRows graph b target T F) coordinateBase slot tableBefore reference fixed)
  · subst reference
    exact SharedZeroRootSelect.root_stored heap n graph.nodeCount slot sourceEnd root
      sourceBound slotBound positive header

end Controller.Cost.SharedQuerySourceFrame
