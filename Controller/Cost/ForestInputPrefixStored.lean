module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestInputStored

@[expose] public section

/-! One source packet, a channel-value table, and a growing node-value prefix.
The source cells and existing Boolean cells are preserved by real array append.
The typed decoder's strict-earlier child indices read the current prefix,
while guard indices continue to read the shared channel table. Allocation and
evaluation ticks are supplied by the caller's executed node-finish routine. -/
namespace Controller.Cost.ForestInputPrefixStored
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.UniformDAGScanLoop

/-- Extending the heap preserves every fetched source/value cell of a stored
stream; no identifier or Boolean occurrence is removed. -/
theorem stored_append (heap extra : Array (Word width)) (valueBase cursor : ℕ)
    (values : List Bool) (cells : Stored heap valueBase cursor values) :
    Stored (heap ++ extra) valueBase cursor values := by
  induction cells with
  | nil cursor => exact Stored.nil cursor
  | cons sourceBound valueBound valueFits source cell rest ih =>
      apply Stored.cons (cursorBound := by simp; omega) (valueBound := by simp; omega)
        (valueFits := valueFits)
      · exact (Array.getElem_append_left sourceBound).trans source
      · exact (Array.getElem_append_left valueBound).trans cell
      · exact ih

def channelHeap (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (channels : Channel n → Bool) : Array (Word width) :=
  withValues (cacheHeap width heap rows roots) channels

def evaluationHeap (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (channels : Channel n → Bool) (nodes : Fin k → Bool) : Array (Word width) :=
  withValues (channelHeap heap rows roots channels) nodes

@[simp] theorem channelHeap_size (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (channels : Channel n → Bool) :
    (channelHeap heap rows roots channels).size = (cacheHeap width heap rows roots).size + n := by
  simp [channelHeap]

@[simp] theorem evaluationHeap_size (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (channels : Channel n → Bool) (nodes : Fin k → Bool) :
    (evaluationHeap heap rows roots channels nodes).size = (cacheHeap width heap rows roots).size + n + k := by
  simp [evaluationHeap]

/-- The growing node prefix uses child identifiers without coercing them into
uncomputed future nodes. Every source cell is derived from the loaded packet. -/
theorem prefix_children_stored (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (corresponds : RowsMatch graph rows)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (nodes : Fin node.val → Bool)
    (fits : (evaluationHeap heap rows roots channels nodes).size ≤ 2 ^ width) :
    Stored (evaluationHeap heap rows roots channels nodes)
      (channelHeap heap rows roots channels).size
      (heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length)
      ((graph.node node).children.map nodes) := by
  let sourceHeap := channelHeap heap rows roots channels
  let cursor := heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length
  have cacheBounds : ∀ slot, (valid : slot < (graph.node node).children.length) →
      cursor + slot < (cacheHeap width heap rows roots).size := by
    intro slot valid
    have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
    have split := row_children_split rows node.val rowValid
    have matched := (corresponds.node node).2.2.1
    have lengths := congrArg List.length split
    simp only [List.length_append, matched, List.length_map] at lengths
    simp only [cursor, cacheHeap_size]
    omega
  have bounds : ∀ slot, (valid : slot < (graph.node node).children.length) →
      cursor + slot < sourceHeap.size := by
    intro slot valid
    have small := cacheBounds slot valid
    simp only [sourceHeap, channelHeap_size]
    omega
  have tableFits : sourceHeap.size + node.val ≤ 2 ^ width := by
    simpa only [evaluationHeap, withValues_size] using fits
  refine stored_ids sourceHeap nodes (graph.node node).children cursor tableFits bounds ?_
  intro slot valid
  have preserved := source_preserved (cacheHeap width heap rows roots) channels
    (cursor + slot) (cacheBounds slot valid)
  exact preserved.trans (typed_child_cell heap graph rows roots corresponds node slot valid)

/-- Node allocation never relocates the one channel table or source packet. -/
theorem prefix_guards_stored (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (corresponds : RowsMatch graph rows)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (nodes : Fin k → Bool)
    (fits : (evaluationHeap heap rows roots channels nodes).size ≤ 2 ^ width) :
    Stored (evaluationHeap heap rows roots channels nodes)
      (cacheHeap width heap rows roots).size
      (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards (rows.take node.val)).length)
      ((graph.node node).guardLabels.map channels) := by
  have tableFits : (cacheHeap width heap rows roots).size + n ≤ 2 ^ width := by
    have size := evaluationHeap_size heap rows roots channels nodes
    omega
  have stored := typed_guards_stored heap graph rows roots corresponds node channels tableFits
  exact stored_append (channelHeap heap rows roots channels)
    (List.ofFn (fun id => boolWord width (nodes id))).toArray _ _ _ stored

/-- Appending one computed Boolean gives the exact extended finite table. -/
theorem append_value (heap : Array (Word width)) (values : Fin k → Bool) (fresh : Bool) :
    withValues heap (Fin.lastCases fresh values) = (withValues heap values).push (boolWord width fresh) := by
  simp only [withValues, List.ofFn_succ_last, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [← List.append_toArray]
  simp only [List.toArray_ofFn, Array.push_append]
  rfl

/-- All earlier source and channel streams survive the actual one-cell append.
The equality above connects this array operation to the typed extended table. -/
theorem stored_push (heap : Array (Word width)) (fresh : Word width) (valueBase cursor : ℕ)
    (values : List Bool) (cells : Stored heap valueBase cursor values) :
    Stored (heap.push fresh) valueBase cursor values := by
  simpa using stored_append heap #[fresh] valueBase cursor values cells

end Controller.Cost.ForestInputPrefixStored
