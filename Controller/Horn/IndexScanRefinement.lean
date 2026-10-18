module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexScanLoop

@[expose] public section

/-! The original normalized row bodies determine the index scan invariant.
Runtime labels and endpoints are read from physical storage; ghost source
prefixes only identify the exact rows and links produced by fetched execution. -/
namespace Controller.Horn.IndexScanRefinement
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.IndexScanLoop
variable {width n : Nat}

theorem labels_drop (labels : List (Fin n)) (offset consumed : Nat) (heap : Array (Word width))
    (stored : Controller.Horn.ResetTouched.LabelsStored labels offset heap)
    (bound : consumed ≤ labels.length) :
    Controller.Horn.ResetTouched.LabelsStored (labels.drop consumed) (offset + consumed) heap := by
  refine ⟨by have := stored.fits; simp only [List.length_drop]; omega, ?_⟩
  intro index
  have inside : consumed + index.val < labels.length := by
    have := index.isLt
    simp only [List.length_drop] at this
    omega
  simpa only [List.getElem_drop, Nat.add_assoc] using stored.entry ⟨consumed + index.val, inside⟩

/-- A row's consumed-prefix cursor identifies the next original occurrence,
including the distinct physical record offsets of repeated equal rows. -/
theorem occurrence_at_row (clauses : List (Controller.CNF.Clause (Fin n)))
    (start rowIndex consumed : Nat) (rowBound : rowIndex < clauses.length)
    (inside : consumed < (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(rowBound))).positives.length) :
    (IndexScan.occurrences clauses start)[(IndexScan.occurrences (clauses.take rowIndex) start).length + consumed]? =
        some (Controller.Horn.NormalizeLoop.recordOffset clauses start rowIndex,
          (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(rowBound))).positives[consumed]) := by
  rw [occurrences_split clauses start rowIndex, List.drop_eq_getElem_cons rowBound]
  simp only [IndexScan.occurrences]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using inside)]
  simp only [List.getElem?_map]
  rw [List.getElem?_eq_getElem inside]
  rfl

/-- The current literal comes from the original immutable physical row body. -/
theorem row_source (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (remaining : consumed < (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length) :
    let pointer := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex + 3 + consumed
    ∃ bound : pointer < state.heap.size,
      state.heap[pointer]'bound =
        word width ((Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives[consumed].val) := by
  have stored := invariant.physical.records ⟨rowIndex, invariant.rowBound⟩
  have pointerBound : Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex + 3 + consumed <
      state.heap.size := by have fits := stored.fits; simp only [Fin.val_mk] at fits; omega
  refine ⟨pointerBound, ?_⟩
  exact stored.body.entry ⟨consumed, remaining⟩

/-- Each actual insertion advances both physical cursors and the exact original
occurrence prefix. The source/record/header facts are derived from RowInvariant,
not separately supplied desired terminal data. -/
theorem indexed_body_step (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat) (state : State width 8)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (remaining : consumed < (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width) :
    ∃ final, Execution program state final 16 (state.liveWords + 2) ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex (consumed + 1) (processed + 1) final ∧
      final.heap.size = state.heap.size + 2 ∧ final.stack = state.stack ∧ final.output = state.output := by
  let rule := Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))
  let row := Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex
  let pointer := row + 3 + consumed
  let limit := row + 3 + rule.positives.length
  let label : Fin n := rule.positives[consumed]
  let previous := IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take processed) label
  have buckets := buckets_of_index clauses recordStart recordEnd base processed state.heap invariant.physical (by omega)
  have headBound := buckets.bound label
  have stored := invariant.physical.records ⟨rowIndex, invariant.rowBound⟩
  obtain ⟨bodyBound, source⟩ := row_source clauses recordStart recordEnd base entry rowIndex consumed processed state
    invariant remaining
  have head : state.heap[headAddress base label]'headBound = word width previous := by
    have cell := invariant.physical.headValues label
    rw [Array.getElem?_eq_getElem headBound] at cell
    exact Option.some.inj cell
  have previousBound : previous < state.heap.size := by
    have bound := IndexScan.heads_bound recordEnd invariant.physical.positiveEnd ((IndexScan.occurrences clauses recordStart).take processed)
      label
    rw [List.length_take_of_le invariant.physical.prefixBound, ← invariant.physical.endpoint] at bound
    exact bound
  have rowBound : row < state.heap.size := by have fits := stored.fits; simp only [Fin.val_mk] at fits; dsimp [row]; omega
  let final := bodyFinished state entry base pointer limit row previous label headBound
  have trace := body_execution program entry base recordStart pointer limit row previous state label present
    invariant.position invariant.running invariant.endpoint.bound invariant.endpoint.value bodyBound headBound source head
    previousBound rowBound invariant.sourceHeld invariant.rowHeld invariant.allocationHeld invariant.zero invariant.one
    (by dsimp [pointer, limit, rule]; omega) (by have fits := stored.fits; simp only [Fin.val_mk] at fits; dsimp [limit, row, rule]; omega)
    capacity room
  have frame := body_frame state entry base pointer limit row previous label headBound
  have heap := body_heap state entry base pointer limit row previous label headBound
  have fetched := occurrence_at_row clauses recordStart rowIndex consumed invariant.rowBound remaining
  rw [← invariant.processedEq] at fetched
  obtain ⟨available, original⟩ := List.getElem?_eq_some_iff.mp fetched
  have nextIndex := index_after clauses recordStart recordEnd base processed row state label
    invariant.physical available original room
  refine ⟨final, trace, ?_, frame.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1⟩
  refine ⟨invariant.rowBound, by omega, by have := invariant.processedEq; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show final.heap = IndexBuild.linkedHeap state base label row previous headBound from heap]
    exact nextIndex
  · simpa [final, pointer, row, Nat.add_assoc] using frame.2.1
  · exact frame.2.2.2.1.trans invariant.rowHeld
  · rw [show final.heap.size = state.heap.size + 2 from frame.1]
    exact frame.2.2.1
  · exact frame.2.2.2.2.1.trans invariant.zero
  · exact frame.2.2.2.2.2.1.trans invariant.one
  · rw [show final.heap = IndexBuild.linkedHeap state base label row previous headBound from heap]
    exact endpoint_frame state base row previous limit label headBound invariant.endpoint
  · exact body_position state entry base pointer limit row previous label headBound invariant.zero
  · exact frame.2.2.2.2.2.2.2.2

/-- Recursive fetched insertion preserves the original row and occurrence
prefix throughout execution, with exact storage growth and caller frames. -/
theorem indexed_body_prefix (program : Program width 8)
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (capacity : entry + 32 < 2 ^ width)
    (count consumed processed : Nat) (state : State width 8)
    (invariant : RowInvariant clauses recordStart recordEnd base entry rowIndex consumed processed state)
    (remaining : consumed + count ≤ (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(invariant.rowBound))).positives.length)
    (room : state.heap.size + 2 * count < 2 ^ width) :
    ∃ final, Execution program state final (16 * count) (state.liveWords + 2 * count) ∧
      RowInvariant clauses recordStart recordEnd base entry rowIndex (consumed + count) (processed + count) final ∧
      final.heap.size = state.heap.size + 2 * count ∧
      final.stack = state.stack ∧ final.output = state.output := by
  induction count generalizing consumed processed state with
  | zero =>
      exact ⟨state, by simpa using Execution.refl state, by simpa using invariant,
        by simp, rfl, rfl⟩
  | succ count ih =>
      obtain ⟨middle, first, next, growth, stack, output⟩ := indexed_body_step program clauses
        recordStart recordEnd base entry rowIndex consumed processed state present invariant
        (by omega) capacity (by omega)
      obtain ⟨final, tail, result, totalGrowth, finalStack, finalOutput⟩ :=
        ih (consumed + 1) (processed + 1) middle next (by omega) (by omega)
      have middleLive : middle.liveWords = state.liveWords + 2 := by
        unfold State.liveWords
        rw [growth, stack, output]
        omega
      refine ⟨final, ?_, ?_, by omega, finalStack.trans stack, finalOutput.trans output⟩
      · have trace := first.append tail
        rw [middleLive] at trace
        convert trace using 1 <;> omega
      · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using result

end Controller.Horn.IndexScanRefinement
