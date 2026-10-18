module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralMachine
public import Controller.Cost.LiteralSourceNode

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Direct literal-sign propagation from the original stored DAG. A propagation
lane reads source tags, heads, child occurrences and primary guard labels;
the source packet is not a transformed decoder. -/
namespace Controller.Extensions.LiteralSource
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGTypedNode (layout)

def mode (probe : Fin (n + 1)) (lane : Fin 3) : LiteralSourceNode.Mode :=
  ⟨decide (lane.val = 0), decide (lane.val = 1), decide (lane.val = 2 ∧ probe.val = n)⟩

def gateValue (config : LiteralSourceNode.Mode) (gate : Gate n available)
    (channels : Assignment n) (earlier : Fin available → Bool) : Bool :=
  match gate with
  | .zero => config.empty
  | .input c => if config.positive then channels c else false
  | .disj [] => config.empty
  | .disj children => children.any earlier
  | .guard c labels => if config.negative then earlier c || labels.any channels else earlier c
  | .liveAnd l r => earlier l || earlier r

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

theorem input_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (channel : Channel n) (inputNode : graph.node node = .input channel)
    (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width (base + 22)) (running : state.halted = false)
    (fits : base + 100 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program (base + 22)
      (LiteralSourceNode.inputCode width base (layout heap rows roots channels))) :
    ∃ final, Execution program state final 9 (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width (channels channel)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have headBound : heap.size + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have valueBound : (cacheHeap width heap rows roots).size + channel.val < state.heap.size := by
    rw [physical, evaluationHeap_size]; have valid := channel.isLt; omega
  have headWord : state.heap[heap.size + 1 + 2 * node.val]'headBound = word width channel.val := by
    simpa only [physical, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      input_head_cell heap graph rows roots matched node channel inputNode channels earlier
  have valueWord : state.heap[(cacheHeap width heap rows roots).size + channel.val]'valueBound =
      boolWord width (channels channel) := by
    simpa only [physical] using channel_cell heap rows roots channels earlier channel
  exact LiteralSourceNode.input_return program state base (2 * node.val) channel.val
    (layout heap rows roots channels) (channels channel) offset headBound valueBound headWord valueWord
    pc running fits room block

theorem guard_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (node : Fin graph.nodeCount) (child : Fin node.val) (labels : List (Channel n))
    (guardNode : graph.node node = .guard child labels)
    (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width (base + 65)) (running : state.halted = false)
    (fits : base + 100 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program (base + 65)
      (LiteralSourceNode.guardCode width base (layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 18 * labels.length + 19 ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width (earlier child || labels.any channels)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
  let cursor := heap.size + 6 * rows.length + (rowChildren rows).length +
    (rowGuards (rows.take node.val)).length
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have headBound : heap.size + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have childBound : (channelHeap heap rows roots channels).size + child.val < state.heap.size := by
    rw [physical]; simp only [evaluationHeap, withValues_size]; exact Nat.add_lt_add_left child.isLt _
  have arityBound : heap.size + 4 * rows.length + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have sourceBound : heap.size + 2 * rows.length + 1 + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have endBound : cursor + labels.length < 2 ^ width := by
    have endLe := guards_end heap graph rows roots matched node
    simp only [guardNode, Gate.guardLabels] at endLe
    have cacheLe : (cacheHeap width heap rows roots).size ≤ state.heap.size := by
      rw [physical, evaluationHeap_size]; omega
    dsimp [cursor]; omega
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
    LiteralSourceNode.guard_return program state base (2 * node.val) child.val cursor
      (layout heap rows roots channels) (earlier child) (labels.map channels)
      offset headBound childBound headWord childWord arityBound sourceBound arityWord sourceWord
      (by simpa only [List.length_map] using endBound) stored pc running fits room block
  refine ⟨final, ticks, peak, trace, ?_, space, ?_, fs, fo, fp, fr⟩
  · simpa only [List.length_map] using time
  · simpa only [List.any_map, Function.comp_def] using fh

theorem children_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (node : Fin graph.nodeCount)
    (empty : Bool)
    (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : ℕ) (pc : state.pc = word width (base + 31)) (running : state.halted = false)
    (fits : base + 100 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program (base + 31)
      (LiteralSourceNode.childrenCode width base (layout heap rows roots channels)))
    (zeroBlock : BlockAt program (base + 14) (LiteralSourceNode.constantReturn width base empty)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 18 * (graph.node node).children.length + 18 ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width (if (graph.node node).children = [] then empty else (graph.node node).children.any earlier)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
  let cursor := heap.size + 6 * rows.length + (rowChildren (rows.take node.val)).length
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have arityBound : heap.size + 4 * rows.length + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have sourceBound : heap.size + 2 * rows.length + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  have endBound : cursor + (graph.node node).children.length < 2 ^ width := by
    have endLe := children_end heap graph rows roots matched node
    have cacheLe : (cacheHeap width heap rows roots).size ≤ state.heap.size := by
      rw [physical, evaluationHeap_size]; omega
    dsimp [cursor]; omega
  have arityWord : state.heap[heap.size + 4 * rows.length + 2 * node.val]'arityBound =
      word width ((graph.node node).children.map earlier).length := by
    simpa only [physical, List.length_map] using
      child_arity_cell heap graph rows roots matched node channels earlier
  have sourceWord : state.heap[heap.size + 2 * rows.length + 2 * node.val]'sourceBound =
      word width cursor := by
    simpa only [physical, cursor] using
      child_cursor_cell heap graph rows roots matched node channels earlier
  have stored : UniformDAGScanLoop.Stored state.heap
      (channelHeap heap rows roots channels).size cursor ((graph.node node).children.map earlier) := by
    simpa only [physical, cursor] using
      prefix_children_stored heap graph rows roots matched node channels earlier
        (by rw [← physical]; omega)
  obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
    LiteralSourceNode.children_return program state base (2 * node.val) cursor
      (layout heap rows roots channels) ((graph.node node).children.map earlier) empty offset
      arityBound sourceBound arityWord sourceWord
      (by simpa only [List.length_map] using endBound) stored pc running fits room block zeroBlock
  refine ⟨final, ticks, peak, trace, ?_, space, ?_, fs, fo, fp, fr⟩
  · simpa only [List.length_map] using time
  · simpa only [List.any_map, Function.comp_def, List.map_eq_nil_iff] using fh

theorem node_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (node : Fin graph.nodeCount) (channels : Assignment n) (earlier : Fin node.val → Bool)
    (config : LiteralSourceNode.Mode)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (base : Nat) (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 100 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base (LiteralSourceNode.code width base (layout heap rows roots channels) config)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 32 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) ∧
      peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width (gateValue config (graph.node node) channels earlier)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
  obtain ⟨dispatch, zeroCode, falseCode, inputCode, childrenCode, guardCode⟩ :=
    LiteralSourceNode.blocks program base _ config block
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have tagBound : heap.size + 2 * node.val < state.heap.size := by
    rw [physical, evaluationHeap_size, cacheHeap_size]; omega
  let tag : Fin 5 := ⟨tagValue graph node, tag_lt_five graph node⟩
  have tagWord : state.heap[heap.size + 2 * node.val] = word width tag.val := by
    simpa only [physical, tag] using tag_cell heap graph rows roots matched node channels earlier
  obtain ⟨ready, dispatchTrace, _, _, r3, rh, rs, ro, rp, rr⟩ :=
    UniformDAGDispatch.execution program state base heap.size (2 * node.val) tag
      (LiteralSourceNode.destinations base config) offset (by omega) tagBound tagWord pc running
      (by omega) dispatch
  have readyPhysical := rh.trans physical
  have readyOffset := r3.trans offset
  have readyRoom : ready.heap.size < 2 ^ width := by simpa [rh] using room
  have rl : ready.liveWords = state.liveWords := by simp [State.liveWords, rh, rs, ro]
  have handler : ∃ final ticks peak, Execution program ready final ticks peak ∧
      ticks ≤ 19 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) ∧
      peak ≤ ready.liveWords + 2 ∧
      final.heap = ready.heap.push (boolWord width (gateValue config (graph.node node) channels earlier)) ∧
      final.stack = ready.stack ∧ final.output = ready.output ∧
      final.pc = word width (base + 100) ∧ final.halted = false := by
    cases gate : graph.node node with
    | zero =>
      obtain ⟨final, trace, fh, fs, fo, fp, fr⟩ :=
        LiteralSourceNode.constant_return program ready (base + 14) base config.empty
          (by simpa [LiteralSourceNode.destinations, tag, tagValue, gate] using rp)
          rr (by omega) readyRoom zeroCode
      exact ⟨final, 4, ready.liveWords + 1, trace, by simp [gate, Gate.children, Gate.guardLabels],
        by omega, by simpa [gateValue, gate] using fh, fs, fo, fp, fr⟩
    | input c =>
      cases positive : config.positive with
      | false =>
        obtain ⟨final, trace, fh, fs, fo, fp, fr⟩ :=
          LiteralSourceNode.constant_return program ready (base + 18) base false
            (by simpa [LiteralSourceNode.destinations, tag, tagValue, gate, positive] using rp)
            rr (by omega) readyRoom falseCode
        exact ⟨final, 4, ready.liveWords + 1, trace, by simp [gate, Gate.children, Gate.guardLabels],
          by omega, by simpa [gateValue, gate, positive] using fh, fs, fo, fp, fr⟩
      | true =>
        obtain ⟨final, trace, fh, fs, fo, fp, fr⟩ :=
          input_execution program ready heap graph rows roots matched node c gate channels earlier
            readyPhysical readyOffset base
            (by simpa [LiteralSourceNode.destinations, tag, tagValue, gate, positive] using rp)
            rr fits readyRoom inputCode
        exact ⟨final, 9, ready.liveWords + 1, trace, by simp [gate, Gate.children, Gate.guardLabels],
          by omega, by simpa [gateValue, gate, positive] using fh, fs, fo, fp, fr⟩
    | disj children =>
      obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
        children_execution program ready heap graph rows roots matched node config.empty channels earlier
          readyPhysical readyOffset base
          (by simpa [LiteralSourceNode.destinations, tag, tagValue, gate] using rp)
          rr fits readyRoom childrenCode zeroCode
      refine ⟨final, ticks, peak, trace, ?_, space, ?_, fs, fo, fp, fr⟩
      · simp only [gate, Gate.children, Gate.guardLabels] at time ⊢; omega
      · cases children <;> simpa [gate, Gate.children, gateValue] using fh
    | guard child labels =>
      cases negative : config.negative with
      | false =>
        obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
          children_execution program ready heap graph rows roots matched node config.empty channels earlier
            readyPhysical readyOffset base
            (by simpa [LiteralSourceNode.destinations, tag, tagValue, gate, negative] using rp)
            rr fits readyRoom childrenCode zeroCode
        exact ⟨final, ticks, peak, trace, by
          simp only [gate, Gate.children, Gate.guardLabels, List.length_cons, List.length_nil] at time ⊢; omega, space,
          by simpa [gate, Gate.children, gateValue, negative] using fh, fs, fo, fp, fr⟩
      | true =>
        obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
          guard_execution program ready heap graph rows roots matched heads node child labels gate channels earlier
            readyPhysical readyOffset base
            (by simpa [LiteralSourceNode.destinations, tag, tagValue, gate, negative] using rp)
            rr fits readyRoom guardCode
        refine ⟨final, ticks, peak, trace, ?_, space,
          by simpa [gate, gateValue, negative] using fh, fs, fo, fp, fr⟩
        simpa [gate, Gate.children, Gate.guardLabels] using time.trans
          (by omega : 18 * labels.length + 19 ≤ 19 + 18 * (1 + labels.length))
    | liveAnd left right =>
      obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ :=
        children_execution program ready heap graph rows roots matched node config.empty channels earlier
          readyPhysical readyOffset base
          (by simpa [LiteralSourceNode.destinations, tag, tagValue, gate] using rp)
          rr fits readyRoom childrenCode zeroCode
      exact ⟨final, ticks, peak, trace, by
        simp only [gate, Gate.children, Gate.guardLabels, List.length_cons, List.length_nil] at time ⊢; omega, space,
        by simpa [gate, Gate.children, gateValue] using fh, fs, fo, fp, fr⟩
  obtain ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr⟩ := handler
  have tagSmall := tag.isLt
  refine ⟨final, (if tag.val = 0 then 4 else 5 + 2 * tag.val) + ticks,
    max state.liveWords peak, dispatchTrace.append trace, ?_, ?_,
    by simpa only [rh] using fh, fs.trans rs, fo.trans ro, fp, fr⟩
  · split_ifs <;> omega
  · rw [rl] at space; omega

theorem gate_flags (gate : Gate n available)
    (noOr : ∀ children, gate = .disj children → children.length ≤ 1)
    (earlier : Fin available → LiteralMachine.Raw n) (probe : Fin (n + 1)) (lane : Fin 3) :
    gateValue (mode probe lane) gate (fun c => decide (c.castSucc = probe))
      (fun c => LiteralMachine.flags (earlier c) probe lane) =
      LiteralMachine.flags (LiteralMachine.rawGate gate earlier) probe lane := by
  cases gate with
  | zero => fin_cases lane <;> simp [gateValue, mode, LiteralMachine.rawGate, LiteralMachine.flags]
  | input c => fin_cases lane <;> simp [gateValue, mode, LiteralMachine.rawGate, LiteralMachine.flags]
  | disj children =>
    have bound := noOr children rfl
    cases children with
    | nil => fin_cases lane <;> simp [gateValue, mode, LiteralMachine.rawGate, LiteralMachine.flags]
    | cons c rest =>
      have empty : rest = [] := by simpa using bound
      subst rest
      simp [gateValue, LiteralMachine.rawGate]
  | guard c labels =>
    fin_cases lane <;> simp [gateValue, mode, LiteralMachine.rawGate, LiteralMachine.Raw.guards,
      LiteralMachine.flags, LiteralMachine.bit_list]
  | liveAnd l r =>
    cases hl : (earlier l).zero <;> cases hr : (earlier r).zero <;>
      by_cases hp : probe.val = n <;> fin_cases lane <;>
      simp [gateValue, mode, LiteralMachine.rawGate, LiteralMachine.Raw.merge, LiteralMachine.flags, hl, hr, hp]

end Controller.Extensions.LiteralSource
