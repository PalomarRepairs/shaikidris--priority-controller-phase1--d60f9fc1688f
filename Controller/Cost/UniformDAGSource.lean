module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGNode
public import Controller.Cost.ForestInputPrefixStored

@[expose] public section

/-! Physical source cells retained across channel initialization and the growing
node-value prefix. The typed graph describes the loaded packet; it is not an
extra runtime input. -/
namespace Controller.Cost.UniformDAGSource
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored

/-- Both appended value tables preserve every cell of the original cache. -/
theorem cache_cell (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (channels : Channel n → Bool) (nodes : Fin k → Bool)
    (address : ℕ) (valid : address < (cacheHeap width heap rows roots).size) :
    (evaluationHeap heap rows roots channels nodes)[address]'(by
      simp only [evaluationHeap_size]; omega) =
      (cacheHeap width heap rows roots)[address]'valid := by
  have channelValid : address < (channelHeap heap rows roots channels).size := by
    simp only [channelHeap_size]; omega
  exact (source_preserved (channelHeap heap rows roots channels) nodes address channelValid).trans
    (source_preserved (cacheHeap width heap rows roots) channels address valid)

/-- The dispatcher reads the tag of the exact typed source node. -/
theorem tag_cell (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (nodes : Fin k → Bool) :
    (evaluationHeap heap rows roots channels nodes)[heap.size + 2 * node.val]'(by
      simp only [evaluationHeap_size, cacheHeap_size];
      have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
      omega) = word width (tagValue graph node) := by
  have bounded : heap.size + 2 * node.val < (cacheHeap width heap rows roots).size := by
    simp only [cacheHeap_size]
    have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    omega
  exact (cache_cell heap rows roots channels nodes _ bounded).trans
    (cache_tag_word heap graph rows roots matched node)

/-- The typed gate basis has exactly the five physical dispatcher tags. -/
theorem tag_lt_five (graph : DAG n) (node : Fin graph.nodeCount) :
    tagValue graph node < 5 := by
  cases gateEq : graph.node node <;> simp [tagValue, gateEq]

/-- A primary-input head is fetched from its actual source header. -/
theorem input_head_cell (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (node : Fin graph.nodeCount) (channel : Channel n)
    (inputNode : graph.node node = .input channel)
    (channels : Channel n → Bool) (nodes : Fin k → Bool) :
    (evaluationHeap heap rows roots channels nodes)[heap.size + 2 * node.val + 1]'(by
      simp only [evaluationHeap_size, cacheHeap_size]
      have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
      omega) = word width channel.val := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have bounded : heap.size + (2 * node.val + 1) < (cacheHeap width heap rows roots).size := by
    simp only [cacheHeap_size]; omega
  have loaded := cache_header_word heap rows roots (2 * node.val + 1)
    (by rw [rowHeaders_length]; omega)
  rw [header_head_value rows node.val rowBound] at loaded
  have head := (matched.node node).2.1 channel inputNode
  rw [head] at loaded
  simpa only [Nat.add_assoc] using
    (cache_cell heap rows roots channels nodes _ bounded).trans loaded

/-- Channel values remain at their once-allocated addresses after node growth. -/
theorem channel_cell (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (channels : Channel n → Bool) (nodes : Fin k → Bool) (channel : Channel n) :
    (evaluationHeap heap rows roots channels nodes)[(cacheHeap width heap rows roots).size + channel.val]'(by
      simp only [evaluationHeap_size]; have bounded := channel.isLt; omega) =
      boolWord width (channels channel) := by
  have bounded : (cacheHeap width heap rows roots).size + channel.val <
      (channelHeap heap rows roots channels).size := by
    simp only [channelHeap_size]; exact Nat.add_lt_add_left channel.isLt _
  exact (source_preserved (channelHeap heap rows roots channels) nodes _ bounded).trans
    (value_cell (cacheHeap width heap rows roots) channels channel)

/-- The fixed guard and AND handlers fetch their first child from the header.
This is an additional checked packet condition: `RowsMatch` alone deliberately
constrains the head column only at primary-input nodes. -/
def typedHead (gate : Gate n available) : ℕ :=
  match gate with
  | .input channel => channel.val
  | .guard child _ => child.val
  | .liveAnd left _ => left.val
  | _ => 0

structure HeadsMatch (graph : DAG n) (rows : List Row)
    (matched : RowsMatch graph rows) : Prop where
  head : ∀ node : Fin graph.nodeCount,
    (rows[node.val]'(by rw [matched.length_eq]; exact node.isLt)).head =
      typedHead (graph.node node)

/-- The checked head column remains available in every growing prefix. -/
theorem typed_head_cell (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (heads : HeadsMatch graph rows matched) (node : Fin graph.nodeCount)
    (channels : Channel n → Bool) (nodes : Fin k → Bool) :
    (evaluationHeap heap rows roots channels nodes)[heap.size + 2 * node.val + 1]'(by
      simp only [evaluationHeap_size, cacheHeap_size]
      have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
      omega) = word width (typedHead (graph.node node)) := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have bounded : heap.size + (2 * node.val + 1) < (cacheHeap width heap rows roots).size := by
    simp only [cacheHeap_size]; omega
  have loaded := cache_header_word heap rows roots (2 * node.val + 1)
    (by rw [rowHeaders_length]; omega)
  rw [header_head_value rows node.val rowBound, heads.head node] at loaded
  simpa only [Nat.add_assoc] using
    (cache_cell heap rows roots channels nodes _ bounded).trans loaded

/-- Original loaded metadata is preserved throughout prefix evaluation. -/
theorem child_arity_cell (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (nodes : Fin k → Bool) :
    (evaluationHeap heap rows roots channels nodes)[heap.size + 4 * rows.length + 2 * node.val]'(by
      simp only [evaluationHeap_size, cacheHeap_size]
      have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
      omega) = word width ((graph.node node).children.length) := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have bounded : heap.size + 4 * rows.length + 2 * node.val < (cacheHeap width heap rows roots).size := by
    simp only [cacheHeap_size]; omega
  exact (cache_cell heap rows roots channels nodes _ bounded).trans
    (cache_child_arity_word heap graph rows roots matched node)

/-- Original loaded metadata is preserved throughout prefix evaluation. -/
theorem guard_arity_cell (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (nodes : Fin k → Bool) :
    (evaluationHeap heap rows roots channels nodes)[heap.size + 4 * rows.length + (2 * node.val + 1)]'(by
      simp only [evaluationHeap_size, cacheHeap_size]
      have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
      omega) = word width ((graph.node node).guardLabels.length) := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have bounded : heap.size + 4 * rows.length + (2 * node.val + 1) < (cacheHeap width heap rows roots).size := by
    simp only [cacheHeap_size]; omega
  exact (cache_cell heap rows roots channels nodes _ bounded).trans
    (cache_guard_arity_word heap graph rows roots matched node)

/-- Original loaded metadata is preserved throughout prefix evaluation. -/
theorem child_cursor_cell (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (nodes : Fin k → Bool) :
    (evaluationHeap heap rows roots channels nodes)[heap.size + 2 * rows.length + 2 * node.val]'(by
      simp only [evaluationHeap_size, cacheHeap_size]
      have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
      omega) = word width (heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length) := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have bounded : heap.size + 2 * rows.length + 2 * node.val < (cacheHeap width heap rows roots).size := by
    simp only [cacheHeap_size]; omega
  exact (cache_cell heap rows roots channels nodes _ bounded).trans
    ((cache_base_words heap rows roots node.val rowBound).1)

/-- Original loaded metadata is preserved throughout prefix evaluation. -/
theorem guard_cursor_cell (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (nodes : Fin k → Bool) :
    (evaluationHeap heap rows roots channels nodes)[heap.size + 2 * rows.length + (2 * node.val + 1)]'(by
      simp only [evaluationHeap_size, cacheHeap_size]
      have bounded : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
      omega) = word width (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards (rows.take node.val)).length) := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have bounded : heap.size + 2 * rows.length + (2 * node.val + 1) < (cacheHeap width heap rows roots).size := by
    simp only [cacheHeap_size]; omega
  exact (cache_cell heap rows roots channels nodes _ bounded).trans
    ((cache_base_words heap rows roots node.val rowBound).2)

end Controller.Cost.UniformDAGSource
