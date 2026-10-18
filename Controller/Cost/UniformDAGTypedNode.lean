module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGSource

@[expose] public section

/-! The fixed node executor runs on the original loaded packet followed by one
channel table and the already-computed strict-earlier node prefix. -/
namespace Controller.Cost.UniformDAGTypedNode
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored
open Controller.Cost.UniformDAGSource

def layout (heap : Array (Word width)) (rows : List Row) (roots : List ℕ)
    (channels : Channel n → Bool) : UniformDAGNode.Layout where
  tagBase := heap.size
  headBase := heap.size + 1
  channelBase := (cacheHeap width heap rows roots).size
  nodeBase := (channelHeap heap rows roots channels).size
  childArityBase := heap.size + 4 * rows.length
  childSourceBase := heap.size + 2 * rows.length
  guardArityBase := heap.size + 4 * rows.length + 1
  guardSourceBase := heap.size + 2 * rows.length + 1

/-- The zero case derives its fetched tag from the typed packet itself. -/
theorem zero_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (zeroNode : graph.node node = .zero)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base
      (UniformDAGNode.code width base (layout heap rows roots channels))) :
    ∃ final, Execution program state final 8 (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width false) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have tagBound : heap.size + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have tagFits : heap.size + 2 * node.val < 2 ^ width := by omega
  have tag := tag_cell heap graph rows roots matched node channels earlier
  have tagWord : state.heap[heap.size + 2 * node.val]'tagBound = word width 0 := by
    simpa only [physical, tagValue, zeroNode] using tag
  exact UniformDAGNode.execution_zero program state base (2 * node.val)
    (layout heap rows roots channels) offset tagFits tagBound tagWord pc running fits room block

/-- Input evaluation reads both the original head and its shared channel cell. -/
theorem input_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (channel : Channel n) (inputNode : graph.node node = .input channel)
    (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base
      (UniformDAGNode.code width base (layout heap rows roots channels))) :
    ∃ final, Execution program state final 16 (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width (channels channel)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have tagBound : heap.size + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have headBound : heap.size + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have valueBound : (cacheHeap width heap rows roots).size + channel.val < state.heap.size := by
    rw [physical, evaluationHeap_size]; have valid := channel.isLt; omega
  have tagFits : heap.size + 2 * node.val < 2 ^ width := by omega
  have headFits : heap.size + 1 + 2 * node.val < 2 ^ width := by omega
  have valueFits : (cacheHeap width heap rows roots).size + channel.val < 2 ^ width := by omega
  have tagWord : state.heap[heap.size + 2 * node.val]'tagBound = word width 1 := by
    simpa only [physical, tagValue, inputNode] using
      tag_cell heap graph rows roots matched node channels earlier
  have headWord : state.heap[heap.size + 1 + 2 * node.val]'headBound = word width channel.val := by
    simpa only [physical, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      input_head_cell heap graph rows roots matched node channel inputNode channels earlier
  have valueWord : state.heap[(cacheHeap width heap rows roots).size + channel.val]'valueBound =
      boolWord width (channels channel) := by
    simpa only [physical] using channel_cell heap rows roots channels earlier channel
  exact UniformDAGNode.execution_input program state base (2 * node.val) channel.val
    (layout heap rows roots channels) (channels channel) offset tagFits headFits valueFits
    tagBound headBound valueBound tagWord headWord valueWord pc running fits room block

private theorem children_end (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (node : Fin graph.nodeCount) :
    heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length +
      (graph.node node).children.length ≤ (cacheHeap width heap rows roots).size := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have lengths := congrArg List.length (row_children_split rows node.val rowBound)
  simp only [List.length_append, (matched.node node).2.2.1, List.length_map] at lengths
  simp only [cacheHeap_size]; omega

private theorem guards_end (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (node : Fin graph.nodeCount) :
    heap.size + 6 * rows.length + (rowChildren rows).length +
      (rowGuards (rows.take node.val)).length + (graph.node node).guardLabels.length ≤
      (cacheHeap width heap rows roots).size := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have lengths := congrArg List.length (row_guards_split rows node.val rowBound)
  simp only [List.length_append, (matched.node node).2.2.2, List.length_map] at lengths
  simp only [cacheHeap_size]; omega

/-- OR scans every original child occurrence in the strict-earlier value table. -/
theorem or_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (children : List (Fin node.val)) (orNode : graph.node node = .disj children)
    (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base
      (UniformDAGNode.code width base (layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 18 * children.length + 23 ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width (children.any earlier)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  let cursor := heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have tagBound : heap.size + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have arityBound : heap.size + 4 * rows.length + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have sourceBound : heap.size + 2 * rows.length + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have tagFits : heap.size + 2 * node.val < 2 ^ width := by omega
  have arityFits : heap.size + 4 * rows.length + 2 * node.val < 2 ^ width := by omega
  have sourceFits : heap.size + 2 * rows.length + 2 * node.val < 2 ^ width := by omega
  have endBound : cursor + children.length < 2 ^ width := by
    have endLe := children_end heap graph rows roots matched node
    simp only [orNode, Gate.children] at endLe
    have cacheLe : (cacheHeap width heap rows roots).size ≤ state.heap.size := by
      rw [physical, evaluationHeap_size]; omega
    dsimp [cursor]; omega
  have countFits : (children.map earlier).length < 2 ^ width := by
    simp only [List.length_map]; omega
  have tagWord : state.heap[heap.size + 2 * node.val]'tagBound = word width 2 := by
    simpa only [physical, tagValue, orNode] using
      tag_cell heap graph rows roots matched node channels earlier
  have arityWord : state.heap[heap.size + 4 * rows.length + 2 * node.val]'arityBound =
      word width (children.map earlier).length := by
    simpa only [physical, orNode, Gate.children, List.length_map] using
      child_arity_cell heap graph rows roots matched node channels earlier
  have sourceWord : state.heap[heap.size + 2 * rows.length + 2 * node.val]'sourceBound =
      word width cursor := by
    simpa only [physical, cursor] using
      child_cursor_cell heap graph rows roots matched node channels earlier
  have stored : UniformDAGScanLoop.Stored state.heap
      (channelHeap heap rows roots channels).size cursor (children.map earlier) := by
    simpa only [physical, cursor, orNode, Gate.children] using
      prefix_children_stored heap graph rows roots matched node channels earlier
        (by rw [← physical]; omega)
  obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
    UniformDAGNode.execution_or program state base (2 * node.val) cursor
      (layout heap rows roots channels) (children.map earlier) offset tagFits tagBound tagWord
      arityFits sourceFits arityBound sourceBound arityWord sourceWord
      (by simpa only [List.length_map] using endBound) countFits stored pc running fits room block
  refine ⟨final, ticks, peak, trace, ?_, space, ?_, fs, fo, fp, fr⟩
  · simpa only [List.length_map] using time
  · simpa only [List.any_map, Function.comp_def] using fh

/-- Guard evaluation reads the original child header and all original labels. -/
theorem guard_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (node : Fin graph.nodeCount) (child : Fin node.val) (labels : List (Channel n))
    (guardNode : graph.node node = .guard child labels)
    (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base
      (UniformDAGNode.code width base (layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 18 * labels.length + 30 ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width (earlier child && !(labels.any channels))) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  let cursor := heap.size + 6 * rows.length + (rowChildren rows).length +
    (rowGuards (rows.take node.val)).length
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have tagBound : heap.size + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have headBound : heap.size + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have childBound : (channelHeap heap rows roots channels).size + child.val < state.heap.size := by
    rw [physical]; simp only [evaluationHeap, withValues_size]; exact Nat.add_lt_add_left child.isLt _
  have arityBound : heap.size + 4 * rows.length + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have sourceBound : heap.size + 2 * rows.length + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have tagFits : heap.size + 2 * node.val < 2 ^ width := by omega
  have headFits : heap.size + 1 + 2 * node.val < 2 ^ width := by omega
  have childFits : (channelHeap heap rows roots channels).size + child.val < 2 ^ width := by omega
  have arityFits : heap.size + 4 * rows.length + 1 + 2 * node.val < 2 ^ width := by omega
  have sourceFits : heap.size + 2 * rows.length + 1 + 2 * node.val < 2 ^ width := by omega
  have endBound : cursor + labels.length < 2 ^ width := by
    have endLe := guards_end heap graph rows roots matched node
    simp only [guardNode, Gate.guardLabels] at endLe
    have cacheLe : (cacheHeap width heap rows roots).size ≤ state.heap.size := by
      rw [physical, evaluationHeap_size]; omega
    dsimp [cursor]; omega
  have countFits : (labels.map channels).length < 2 ^ width := by
    simp only [List.length_map]; omega
  have tagWord : state.heap[heap.size + 2 * node.val]'tagBound = word width 3 := by
    simpa only [physical, tagValue, guardNode] using
      tag_cell heap graph rows roots matched node channels earlier
  have headWord : state.heap[heap.size + 1 + 2 * node.val]'headBound = word width child.val := by
    simpa only [physical, guardNode, typedHead, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      typed_head_cell heap graph rows roots matched heads node channels earlier
  have childWord : state.heap[(channelHeap heap rows roots channels).size + child.val]'childBound =
      boolWord width (earlier child) := by
    simpa only [physical, evaluationHeap] using value_cell (channelHeap heap rows roots channels) earlier child
  have arityWord : state.heap[heap.size + 4 * rows.length + 1 + 2 * node.val]'arityBound =
      word width (labels.map channels).length := by
    simpa only [physical, guardNode, Gate.guardLabels, List.length_map,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      guard_arity_cell heap graph rows roots matched node channels earlier
  have sourceWord : state.heap[heap.size + 2 * rows.length + 1 + 2 * node.val]'sourceBound =
      word width cursor := by
    simpa only [physical, cursor, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      guard_cursor_cell heap graph rows roots matched node channels earlier
  have stored : UniformDAGScanLoop.Stored state.heap
      (cacheHeap width heap rows roots).size cursor (labels.map channels) := by
    simpa only [physical, cursor, guardNode, Gate.guardLabels] using
      prefix_guards_stored heap graph rows roots matched node channels earlier
        (by rw [← physical]; omega)
  obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
    UniformDAGNode.execution_guard program state base (2 * node.val) child.val cursor
      (layout heap rows roots channels) (earlier child) (labels.map channels)
      offset tagFits tagBound tagWord headFits childFits headBound childBound headWord childWord
      arityFits sourceFits arityBound sourceBound arityWord sourceWord
      (by simpa only [List.length_map] using endBound) countFits stored pc running fits room block
  refine ⟨final, ticks, peak, trace, ?_, space, ?_, fs, fo, fp, fr⟩
  · simpa only [List.length_map] using time
  · simpa only [List.any_map, Function.comp_def] using fh

/-- AND fetches both strict-earlier values and the original second child slot. -/
theorem and_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (node : Fin graph.nodeCount) (left right : Fin node.val)
    (andNode : graph.node node = .liveAnd left right)
    (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base
      (UniformDAGNode.code width base (layout heap rows roots channels))) :
    ∃ final, Execution program state final (if earlier left then 30 else 29) (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width (earlier left && earlier right)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  let cursor := heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have tagBound : heap.size + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have headBound : heap.size + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have sourceBound : heap.size + 2 * rows.length + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have cursorCacheBound : cursor + 1 < (cacheHeap width heap rows roots).size := by
    have endLe := children_end heap graph rows roots matched node
    simp only [andNode, Gate.children, List.length_cons, List.length_nil] at endLe
    dsimp [cursor]; omega
  have cursorBound : cursor + 1 < state.heap.size := by
    rw [physical, evaluationHeap_size]; omega
  have leftBound : (channelHeap heap rows roots channels).size + left.val < state.heap.size := by
    rw [physical]; simp only [evaluationHeap, withValues_size]; exact Nat.add_lt_add_left left.isLt _
  have rightBound : (channelHeap heap rows roots channels).size + right.val < state.heap.size := by
    rw [physical]; simp only [evaluationHeap, withValues_size]; exact Nat.add_lt_add_left right.isLt _
  have tagWord : state.heap[heap.size + 2 * node.val]'tagBound = word width 4 := by
    simpa only [physical, tagValue, andNode] using
      tag_cell heap graph rows roots matched node channels earlier
  have headWord : state.heap[heap.size + 1 + 2 * node.val]'headBound = word width left.val := by
    simpa only [physical, andNode, typedHead, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      typed_head_cell heap graph rows roots matched heads node channels earlier
  have sourceWord : state.heap[heap.size + 2 * rows.length + 2 * node.val]'sourceBound =
      word width cursor := by
    simpa only [physical, cursor] using child_cursor_cell heap graph rows roots matched node channels earlier
  have rightWord : state.heap[cursor + 1]'cursorBound = word width right.val := by
    have loaded := typed_child_cell heap graph rows roots matched node 1
      (by simp only [andNode, Gate.children, List.length_cons, List.length_nil]; omega)
    have physicalCell := cache_cell heap rows roots channels earlier (cursor + 1) cursorCacheBound
    have result := physicalCell.trans (by simpa only [cursor, andNode, Gate.children,
      List.getElem_cons_succ, List.getElem_cons_zero] using loaded)
    simpa only [physical] using result
  have leftWord : state.heap[(channelHeap heap rows roots channels).size + left.val]'leftBound =
      boolWord width (earlier left) := by
    simpa only [physical, evaluationHeap] using value_cell (channelHeap heap rows roots channels) earlier left
  have rightValue : state.heap[(channelHeap heap rows roots channels).size + right.val]'rightBound =
      boolWord width (earlier right) := by
    simpa only [physical, evaluationHeap] using value_cell (channelHeap heap rows roots channels) earlier right
  exact UniformDAGNode.execution_and program state base (2 * node.val) cursor left.val right.val
    (layout heap rows roots channels) (earlier left) (earlier right) offset
    (by dsimp [layout]; omega) tagBound tagWord
    (by dsimp [layout]; omega) (by dsimp [layout]; omega) (by omega)
    (by dsimp [layout]; omega) (by dsimp [layout]; omega)
    headBound sourceBound cursorBound leftBound rightBound headWord sourceWord rightWord
    leftWord rightValue pc running fits room block

/-- Every typed gate is executed by the same fixed109-instruction node block.
All fetched fields are derived from the packet; only already-computed child
values are available. The cost charges every original incidence. -/
theorem execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base
      (UniformDAGNode.code width base (layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 30 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) ∧
      peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width ((graph.node node).eval channels earlier)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 109) ∧ final.halted = false := by
  cases gateEq : graph.node node with
  | zero =>
      obtain ⟨final, trace, fh, fs, fo, fp, fr⟩ := zero_execution program state heap graph rows roots
        matched node channels earlier gateEq physical offset base pc running fits room block
      refine ⟨final, 8, state.liveWords + 1, trace, ?_, by omega, ?_, fs, fo, fp, fr⟩
      · simp [gateEq, Gate.children, Gate.guardLabels]
      · simpa only [gateEq, Gate.eval] using fh
  | input channel =>
      obtain ⟨final, trace, fh, fs, fo, fp, fr⟩ := input_execution program state heap graph rows roots
        matched node channel gateEq channels earlier physical offset base pc running fits room block
      refine ⟨final, 16, state.liveWords + 1, trace, ?_, by omega, ?_, fs, fo, fp, fr⟩
      · simp [gateEq, Gate.children, Gate.guardLabels]
      · simpa only [gateEq, Gate.eval] using fh
  | disj children =>
      obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
        or_execution program state heap graph rows roots matched node children gateEq channels earlier
          physical offset base pc running fits room block
      refine ⟨final, ticks, peak, trace, ?_, space, ?_, fs, fo, fp, fr⟩
      · simp only [gateEq, Gate.children, Gate.guardLabels, List.length_nil, Nat.add_zero]; omega
      · simpa only [gateEq, Gate.eval] using fh
  | guard child labels =>
      obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
        guard_execution program state heap graph rows roots matched heads node child labels gateEq
          channels earlier physical offset base pc running fits room block
      refine ⟨final, ticks, peak, trace, ?_, space, ?_, fs, fo, fp, fr⟩
      · simp only [gateEq, Gate.children, Gate.guardLabels, List.length_cons, List.length_nil]; omega
      · simpa only [gateEq, Gate.eval] using fh
  | liveAnd left right =>
      obtain ⟨final, trace, fh, fs, fo, fp, fr⟩ := and_execution program state heap graph rows roots
        matched heads node left right gateEq channels earlier physical offset base pc running fits room block
      refine ⟨final, (if earlier left then 30 else 29), state.liveWords + 1,
        trace, ?_, by omega, ?_, fs, fo, fp, fr⟩
      · simp only [gateEq, Gate.children, Gate.guardLabels, List.length_cons, List.length_nil]
        split <;> omega
      · simpa only [gateEq, Gate.eval] using fh

end Controller.Cost.UniformDAGTypedNode
