module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestIndexedOperands
public import Controller.Cost.UniformDAGScanLoop

@[expose] public section

/-! Stored incidence streams over the once-loaded source packet.
Identifiers are read from actual packet cells; Boolean values occupy a separate
appended table. The typed value function describes that table's contents and
is not a runtime operand list. Every repeated incidence remains a separate
Stored constructor and therefore a separate fetched loop iteration. -/
namespace Controller.Cost.ForestInputStored
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGScanLoop

/-- Value cells appended after the loaded input. Filling or evaluating this
table has its own execution proof; this definition states its exact layout. -/
def withValues (heap : Array (Word width)) (values : Fin m → Bool) : Array (Word width) :=
  heap ++ (List.ofFn (fun id => boolWord width (values id))).toArray

@[simp] theorem withValues_size (heap : Array (Word width)) (values : Fin m → Bool) :
    (withValues heap values).size = heap.size + m := by simp [withValues]

theorem source_preserved (heap : Array (Word width)) (values : Fin m → Bool)
    (index : ℕ) (valid : index < heap.size) :
    (withValues heap values)[index]'(by simp; omega) = heap[index]'valid := by
  exact Array.getElem_append_left valid

theorem value_cell (heap : Array (Word width)) (values : Fin m → Bool) (id : Fin m) :
    (withValues heap values)[heap.size + id.val]'(by simpa only [withValues_size, Nat.add_lt_add_iff_left] using id.isLt) =
      boolWord width (values id) := by
  simp only [withValues, Array.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem_toArray, List.getElem_ofFn]

/-- Actual source identifiers and the actual appended value cells derive the
loop's storage relation. No Boolean-list oracle is a machine input. -/
theorem stored_ids (heap : Array (Word width)) (values : Fin m → Bool)
    (ids : List (Fin m)) (cursor : ℕ)
    (fits : heap.size + m ≤ 2 ^ width)
    (sourceBounds : ∀ i, (valid : i < ids.length) → cursor + i < heap.size)
    (sourceCells : ∀ i, (valid : i < ids.length) →
      heap[cursor + i]'(sourceBounds i valid) = word width (ids[i]'valid).val) :
    Stored (withValues heap values) heap.size cursor (ids.map values) := by
  induction ids generalizing cursor with
  | nil => exact Stored.nil cursor
  | cons id rest ih =>
      have sourceBound : cursor < heap.size := by simpa using sourceBounds 0 (by simp)
      have sourceWord : heap[cursor]'sourceBound = word width id.val := by
        have first := sourceCells 0 (by simp)
        change heap[cursor + 0] = word width id.val at first
        simpa only [Nat.add_zero] using first
      have valueBound : heap.size + id.val < (withValues heap values).size := by simpa only [withValues_size, Nat.add_lt_add_iff_left] using id.isLt
      have valueFits : heap.size + id.val < 2 ^ width := by have bounded := id.isLt; omega
      have tail := ih (cursor + 1)
        (fun i valid => by have bounded := sourceBounds (i + 1) (by simpa using valid); omega)
        (fun i valid => by
          have validNext : i + 1 < (id :: rest).length := by simpa using valid
          have nextBound := sourceBounds (i + 1) validNext
          have next := sourceCells (i + 1) validNext
          change heap[cursor + (i + 1)]'nextBound = word width (rest[i]'valid).val at next
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next)
      apply Stored.cons (cursorBound := by simp; omega) (valueBound := valueBound)
        (valueFits := valueFits)
      · exact (source_preserved heap values cursor sourceBound).trans sourceWord
      · exact value_cell heap values id
      · exact tail

/-- The child-stream cell is physically allocated in the loaded packet. -/
theorem cache_child_cell (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (i : ℕ) (valid : i < (rowChildren rows).length) :
    (cacheHeap width heap rows roots)[heap.size + 6 * rows.length + i]'
      (by simp; omega) = word width ((rowChildren rows)[i]'valid) := by
  let before := rowHeaders rows ++ rowBases rows (heap.size + 6 * rows.length)
    (heap.size + 6 * rows.length + (rowChildren rows).length) ++ rowArities rows
  have length : before.length = 6 * rows.length := by simp [before]; omega
  have packet : serializedRows heap.size rows roots =
      before ++ rowChildren rows ++ (rowGuards rows ++ roots) := by
    simp only [serializedRows, before, List.append_assoc]
  have cell := allocated_segment_word heap before (rowChildren rows) (rowGuards rows ++ roots) i valid
  simpa only [cacheHeap, packet, length] using cell

/-- Guard occurrences have their own stored stream, including duplicates. -/
theorem cache_guard_cell (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (i : ℕ) (valid : i < (rowGuards rows).length) :
    (cacheHeap width heap rows roots)[heap.size + 6 * rows.length + (rowChildren rows).length + i]'
      (by simp; omega) = word width ((rowGuards rows)[i]'valid) := by
  let before := rowHeaders rows ++ rowBases rows (heap.size + 6 * rows.length)
    (heap.size + 6 * rows.length + (rowChildren rows).length) ++ rowArities rows ++ rowChildren rows
  have length : before.length = 6 * rows.length + (rowChildren rows).length := by simp [before]; omega
  have packet : serializedRows heap.size rows roots = before ++ rowGuards rows ++ roots := by
    simp only [serializedRows, before, List.append_assoc]
  have cell := allocated_segment_word heap before (rowGuards rows) roots i valid
  simpa only [cacheHeap, packet, length, Nat.add_assoc] using cell

/-- Raw row decomposition retains both incidence positions and their order. -/
theorem row_children_split (rows : List Row) (index : ℕ) (valid : index < rows.length) :
    rowChildren rows = rowChildren (rows.take index) ++ (rows[index]'valid).children ++
      rowChildren (rows.drop (index + 1)) := by
  have split := List.take_append_drop index rows
  rw [List.drop_eq_getElem_cons valid] at split
  have mapped := congrArg rowChildren split
  simpa only [rowChildren, List.flatMap_append, List.flatMap_cons, List.append_assoc] using mapped.symm

theorem row_guards_split (rows : List Row) (index : ℕ) (valid : index < rows.length) :
    rowGuards rows = rowGuards (rows.take index) ++ (rows[index]'valid).guards ++
      rowGuards (rows.drop (index + 1)) := by
  have split := List.take_append_drop index rows
  rw [List.drop_eq_getElem_cons valid] at split
  have mapped := congrArg rowGuards split
  simpa only [rowGuards, List.flatMap_append, List.flatMap_cons, List.append_assoc] using mapped.symm

/-- Per-row child slots follow the exact typed incidence list in the packet. -/
theorem typed_child_cell (heap : Array (Word width)) (graph : DAG n) (rows : List Row)
    (roots : List ℕ) (corresponds : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (slot : ℕ) (valid : slot < (graph.node node).children.length) :
    let cursor := heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length
    (cacheHeap width heap rows roots)[cursor + slot]'(by
      have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
      have split := row_children_split rows node.val rowValid
      have rowChildrenEq := (corresponds.node node).2.2.1
      have lengths := congrArg List.length split
      simp only [List.length_append, rowChildrenEq, List.length_map] at lengths
      simp only [cacheHeap_size]
      omega) = word width ((graph.node node).children[slot]'valid).val := by
  have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
  have split := row_children_split rows node.val rowValid
  have rowChildrenEq := (corresponds.node node).2.2.1
  let offset := (rowChildren (rows.take node.val)).length
  have bounded : offset + slot < (rowChildren rows).length := by
    have lengths := congrArg List.length split
    simp only [List.length_append, rowChildrenEq, List.length_map] at lengths
    omega
  have cell := cache_child_cell heap rows roots (offset + slot) bounded
  have item : (rowChildren rows)[offset + slot]'bounded = ((graph.node node).children[slot]'valid).val := by
    simp only [split, List.append_assoc, offset]
    rw [List.getElem_append_right (as := rowChildren (rows.take node.val))
      (bs := (rows[node.val]'rowValid).children ++ rowChildren (rows.drop (node.val + 1)))
      (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left, rowChildrenEq]
    rw [List.getElem_append_left (as := (graph.node node).children.map Fin.val)
      (bs := rowChildren (rows.drop (node.val + 1))) (by simpa only [List.length_map] using valid)]
    simp only [List.getElem_map]
  rw [item] at cell
  simpa only [offset, Nat.add_assoc] using cell

/-- The fixed scan's complete Stored premise is derived from the loaded typed
child packet and the actual appended node-value cells. The representation does
not evaluate the typed node function during the machine scan. -/
theorem typed_children_stored (heap : Array (Word width)) (graph : DAG n) (rows : List Row)
    (roots : List ℕ) (corresponds : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (values : Fin graph.nodeCount → Bool)
    (fits : (cacheHeap width heap rows roots).size + graph.nodeCount ≤ 2 ^ width) :
    Stored (withValues (cacheHeap width heap rows roots) values)
      (cacheHeap width heap rows roots).size
      (heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length)
      (((graph.node node).children.map (fun child => (⟨child.val, Nat.lt_trans child.isLt node.isLt⟩ : Fin graph.nodeCount))).map values) := by
  let ids : List (Fin graph.nodeCount) := (graph.node node).children.map
    (fun child => ⟨child.val, Nat.lt_trans child.isLt node.isLt⟩)
  change Stored _ _ _ (ids.map values)
  have bounds : ∀ slot, (valid : slot < ids.length) →
      heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length + slot < (cacheHeap width heap rows roots).size := by
    intro slot valid
    have childValid : slot < (graph.node node).children.length := by simpa [ids] using valid
    have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
    have split := row_children_split rows node.val rowValid
    have rowChildrenEq := (corresponds.node node).2.2.1
    have lengths := congrArg List.length split
    simp only [List.length_append, rowChildrenEq, List.length_map] at lengths
    simp only [cacheHeap_size]
    omega
  refine stored_ids (cacheHeap width heap rows roots) values ids _ fits bounds ?_
  · intro slot valid
    have childValid : slot < (graph.node node).children.length := by simpa [ids] using valid
    simpa only [ids, List.getElem_map] using typed_child_cell heap graph rows roots corresponds node slot childValid

/-- Per-row guard slots follow the exact typed incidence list in the packet. -/
theorem typed_guard_cell (heap : Array (Word width)) (graph : DAG n) (rows : List Row)
    (roots : List ℕ) (corresponds : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (slot : ℕ) (valid : slot < (graph.node node).guardLabels.length) :
    let cursor := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards (rows.take node.val)).length
    (cacheHeap width heap rows roots)[cursor + slot]'(by
      have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
      have split := row_guards_split rows node.val rowValid
      have rowGuardsEq := (corresponds.node node).2.2.2
      have lengths := congrArg List.length split
      simp only [List.length_append, rowGuardsEq, List.length_map] at lengths
      simp only [cacheHeap_size]
      omega) = word width ((graph.node node).guardLabels[slot]'valid).val := by
  have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
  have split := row_guards_split rows node.val rowValid
  have rowGuardsEq := (corresponds.node node).2.2.2
  let offset := (rowGuards (rows.take node.val)).length
  have bounded : offset + slot < (rowGuards rows).length := by
    have lengths := congrArg List.length split
    simp only [List.length_append, rowGuardsEq, List.length_map] at lengths
    omega
  have cell := cache_guard_cell heap rows roots (offset + slot) bounded
  have item : (rowGuards rows)[offset + slot]'bounded = ((graph.node node).guardLabels[slot]'valid).val := by
    simp only [split, List.append_assoc, offset]
    rw [List.getElem_append_right (as := rowGuards (rows.take node.val))
      (bs := (rows[node.val]'rowValid).guards ++ rowGuards (rows.drop (node.val + 1)))
      (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left, rowGuardsEq]
    rw [List.getElem_append_left (as := (graph.node node).guardLabels.map Fin.val)
      (bs := rowGuards (rows.drop (node.val + 1))) (by simpa only [List.length_map] using valid)]
    simp only [List.getElem_map]
  rw [item] at cell
  simpa only [offset, Nat.add_assoc] using cell

/-- The fixed scan's complete Stored premise is derived from the loaded typed
guard packet and the actual appended channel-value cells. The representation does
not evaluate the typed node function during the machine scan. -/
theorem typed_guards_stored (heap : Array (Word width)) (graph : DAG n) (rows : List Row)
    (roots : List ℕ) (corresponds : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (values : Channel n → Bool)
    (fits : (cacheHeap width heap rows roots).size + n ≤ 2 ^ width) :
    Stored (withValues (cacheHeap width heap rows roots) values)
      (cacheHeap width heap rows roots).size
      (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards (rows.take node.val)).length)
      ((graph.node node).guardLabels.map values) := by
  have bounds : ∀ slot, (valid : slot < ((graph.node node).guardLabels).length) →
      heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards (rows.take node.val)).length + slot < (cacheHeap width heap rows roots).size := by
    intro slot valid
    have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
    have split := row_guards_split rows node.val rowValid
    have rowGuardsEq := (corresponds.node node).2.2.2
    have lengths := congrArg List.length split
    simp only [List.length_append, rowGuardsEq, List.length_map] at lengths
    simp only [cacheHeap_size]
    omega
  refine stored_ids (cacheHeap width heap rows roots) values (graph.node node).guardLabels _ fits bounds ?_
  · intro slot valid
    exact typed_guard_cell heap graph rows roots corresponds node slot valid

end Controller.Cost.ForestInputStored
