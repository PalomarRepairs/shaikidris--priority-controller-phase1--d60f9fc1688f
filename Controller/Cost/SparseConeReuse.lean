module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SparseConeTraversal
public import Controller.Cost.UniformDAGResources

@[expose] public section

/-! Shared-heap evaluation and touched-cell reuse of the actual original-ID
postorder ledger. Source child/guard occurrences retain their stored order;
only finished-prefix memo values supply the warm evaluator. -/
namespace Controller.Cost.SparseConeReuse
open Controller.Cost Controller.Decoder Controller.Cost.GateProgram
open Controller.Cost.SparseConeProgram Controller.Cost.SparseConeTraversal
variable {width n registers : Nat}

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits, present]
  rfl

private theorem scope_tail (heap : Array (Word width)) (cursor : Nat)
    (label : Channel n) (rest : List (Channel n))
    (stored : ScopeStored heap cursor (label :: rest)) : ScopeStored heap (cursor + 1) rest := by
  intro position
  have cell := stored ⟨position.val + 1, by simp only [List.length_cons]; omega⟩
  change heap[cursor + (position.val + 1)]? =
    some (word width ((label :: rest)[position.val + 1]'(by simpa only [List.length_cons] using Nat.succ_lt_succ position.isLt)).val) at cell
  have offset : cursor + (position.val + 1) = cursor + 1 + position.val := by omega
  change heap[cursor + 1 + position.val]? =
    some (word width (rest[position.val]'position.isLt).val)
  simpa only [offset, List.getElem_cons_succ] using cell

/-- Projection for proof instantiation retains every physical heap, stack,
output and control word. It is reconstructed exactly before the fetched
handler trace, so it introduces no machine reset or execution step. -/
private def narrowState (state : State width 8) : State width 4 :=
  { reg := fun register => state.reg (widenRegister register)
    heap := state.heap, stack := state.stack, output := state.output,
    pc := state.pc, halted := state.halted }

private theorem widen_narrow (state : State width 8) :
    widenState (narrowState state) state.reg = state := by
  have registers : (widenState (narrowState state) state.reg).reg = state.reg := by
    funext register
    by_cases small : register.val < 4
    · change (if h : register.val < 4 then
        state.reg (widenRegister ⟨register.val, h⟩) else state.reg register) = state.reg register
      rw [dite_eq_left small]
      have same : widenRegister ⟨register.val, small⟩ = register := Fin.ext rfl
      rw [same]
    · simp only [widenState, dite_eq_right small]
  cases state
  simp only [widenState, narrowState] at registers ⊢
  congr 1

/-- A halted state has no further fetched transition. -/
private theorem execution_nonhalted_start (program : Program width registers)
    (initial final : State width registers) (ticks peak : Nat)
    (trace : Execution program initial final ticks peak) (running : final.halted = false) :
    initial.halted = false := by
  cases trace with
  | refl => exact running
  | cons transition rest =>
      cases halted : initial.halted with
      | false => rfl
      | true =>
          unfold programStep at transition
          cases cell : program[initial.pc.val]? with
          | none => simp [cell] at transition
          | some instruction => simp [cell, step, halted] at transition

/-- The handler trace is instantiated on its actual code with halt padding.
Its nonhalted endpoint forces every executed fetch into the handler block.
Widening then follows those same fetched transitions in the containing
program, retaining the caller's four high registers and charging them. -/
private theorem widen_handler_execution (global : Program width 8)
    (base : Nat) (code : Program width 4)
    (physical : ∀ position : Fin code.size, global[base + position.val]? =
      some (widenInstruction code[position.val]))
    (initial final : State width 4) (ticks peak : Nat)
    (trace : Execution ((Array.replicate base (.halt : Instruction width 4)) ++ code)
      initial final ticks peak)
    (running : final.halted = false) (saved : Fin 8 → Word width) :
    Execution global (widenState initial saved) (widenState final saved) ticks (peak + 4) := by
  induction trace generalizing saved with
  | refl state =>
      simpa only [widenState_liveWords] using Execution.refl (p := global) (widenState state saved)
  | @cons state middle final ticks peak transition rest ih =>
      let padded : Program width 4 := Array.replicate base .halt ++ code
      change programStep padded state = some middle at transition
      have stateRunning := execution_nonhalted_start padded state final (ticks + 1) (max state.liveWords peak)
        (Execution.cons transition rest) running
      have middleRunning := execution_nonhalted_start padded middle final ticks peak rest running
      have lower : base ≤ state.pc.val := by
        by_contra below
        have bound : state.pc.val < base := by omega
        have cell : padded[state.pc.val]? = some .halt := by
          dsimp only [padded]
          rw [Array.getElem?_append_left (by simp only [Array.size_replicate]; omega)]
          simp only [Array.getElem?_replicate, ite_eq_left bound]
        have equal : ({ state.advance with halted := true } : State width 4) = middle := by
          unfold programStep at transition
          rw [cell] at transition
          change step .halt state = some middle at transition
          apply Option.some.inj
          simpa only [step, stateRunning, Bool.false_eq_true, ite_false] using transition
        have ended : middle.halted = true := congrArg State.halted equal.symm
        rw [ended] at middleRunning
        contradiction
      have upper : state.pc.val < base + code.size := by
        by_contra outside
        have bound : padded.size ≤ state.pc.val := by
          simp only [padded, Array.size_append, Array.size_replicate]
          omega
        have cell : padded[state.pc.val]? = none := Array.getElem?_eq_none bound
        unfold programStep at transition
        rw [cell] at transition
        contradiction
      have indexBound : state.pc.val - base < code.size := by omega
      have lowCell : padded[state.pc.val]? = some code[state.pc.val - base] := by
        dsimp only [padded]
        rw [Array.getElem?_append_right (by simp only [Array.size_replicate]; omega)]
        simpa only [Array.size_replicate] using Array.getElem?_eq_getElem indexBound
      have instructionStep : step code[state.pc.val - base] state = some middle := by
        unfold programStep at transition
        rw [lowCell] at transition
        exact transition
      have pcIdentity : base + (state.pc.val - base) = state.pc.val := by omega
      have highCell : global[state.pc.val]? = some (widenInstruction code[state.pc.val - base]) := by
        simpa only [pcIdentity] using physical ⟨state.pc.val - base, indexBound⟩
      have lifted : programStep global (widenState state saved) = some (widenState middle saved) := by
        unfold programStep
        change (global[state.pc.val]?.bind (fun instruction => step instruction (widenState state saved))) = _
        rw [highCell]
        change step (widenInstruction code[state.pc.val - base]) (widenState state saved) = _
        rw [widen_step, instructionStep]
        rfl
      simpa only [widenState_liveWords, Nat.add_max_add_right] using
        Execution.cons lifted (ih running saved)

/-- A retained ordered source slice and a resident value table supply every
actual incidence fetch required by the fixed evaluator scan. Repeated source
IDs remain repeated entries in the evaluated list. -/
private theorem warm_incidence_cells (heap : Array (Word width))
    (cursor valueBase available : Nat) (labels : List (Fin available))
    (values : Fin available → Bool)
    (scope : ScopeStored heap cursor labels)
    (sourceEnd : cursor + labels.length ≤ heap.size)
    (tableEnd : valueBase + available ≤ heap.size)
    (heapFits : heap.size < 2 ^ width)
    (table : ∀ label, heap[valueBase + label.val]? = some (boolWord width (values label))) :
    UniformDAGScanLoop.Stored heap valueBase cursor (labels.map values) := by
  induction labels generalizing cursor with
  | nil => exact .nil cursor
  | cons label rest ih =>
      have cursorBound : cursor < heap.size := by
        simp only [List.length_cons] at sourceEnd
        omega
      have valueBound : valueBase + label.val < heap.size := by
        have := label.isLt
        omega
      have sourceCell : heap[cursor]'cursorBound = word width label.val := by
        have cell := scope ⟨0, by simp only [List.length_cons]; omega⟩
        simp only [Nat.add_zero, Fin.getElem_fin, List.getElem_cons_zero] at cell
        rw [Array.getElem?_eq_getElem cursorBound] at cell
        exact Option.some.inj cell
      have valueCell : heap[valueBase + label.val]'valueBound = boolWord width (values label) := by
        have cell := table label
        rw [Array.getElem?_eq_getElem valueBound] at cell
        exact Option.some.inj cell
      exact .cons cursorBound valueBound (by omega) sourceCell valueCell
        (ih (cursor + 1) (scope_tail heap cursor label rest scope)
          (by simp only [List.length_cons] at sourceEnd; omega))

/-- The semantic prefix is the physically finished ledger prefix, rather than
an assumption that every ambient memo slot already has the new value. -/
private def WarmPrefixCorrect (graph : DAG n) (assignment : Assignment n)
    (completed : List (Fin graph.nodeCount)) (visited : Nat)
    (values : Fin graph.nodeCount → Bool) : Prop :=
  ∀ node ∈ completed.take visited, values node = graph.eval assignment node

private theorem warm_original_child_correct (graph : DAG n) (assignment : Assignment n)
    (completed : List (Fin graph.nodeCount)) (position : Fin completed.length)
    (values : Fin graph.nodeCount → Bool) (ordered : Postorder graph completed)
    (correct : WarmPrefixCorrect graph assignment completed position.val values)
    (child : Fin (completed[position]).val)
    (member : child ∈ (graph.node completed[position]).children) :
    values (graph.childIndex completed[position] child) =
      graph.eval assignment (graph.childIndex completed[position] child) :=
  correct _ (ordered.2 position child member)

/-- The actual committed store updates one original-ID Boolean value slot;
all other represented memo values retain their physical cell. -/
private theorem warm_table_set (heap : Array (Word width)) (graph : DAG n)
    (base : Nat) (values : Fin graph.nodeCount → Bool)
    (node : Fin graph.nodeCount) (value : Bool)
    (bound : base + node.val < heap.size)
    (table : ∀ candidate : Fin graph.nodeCount,
      heap[base + candidate.val]? = some (boolWord width (values candidate))) :
    ∀ candidate : Fin graph.nodeCount,
      (heap.set (base + node.val) (boolWord width value) bound)[base + candidate.val]? =
        some (boolWord width ((Function.update values node value) candidate)) := by
  intro candidate
  by_cases same : candidate = node
  · subst candidate
    rw [Array.getElem?_set_self]
    simp only [Function.update_self]
  · have address : base + node.val ≠ base + candidate.val := by
      intro equal
      apply same
      apply Fin.ext
      omega
    rw [Array.getElem?_set_ne bound address]
    simpa only [Function.update_of_ne same] using table candidate

/-- Updating the next distinct postorder node retains correctness of the
already visited physical ledger prefix. No value outside that prefix is
assumed to represent the new semantic evaluation. -/
private theorem warm_prefix_update (graph : DAG n) (assignment : Assignment n)
    (completed : List (Fin graph.nodeCount)) (position : Fin completed.length)
    (values : Fin graph.nodeCount → Bool) (distinct : completed.Nodup)
    (correct : WarmPrefixCorrect graph assignment completed position.val values) :
    WarmPrefixCorrect graph assignment completed (position.val + 1)
      (Function.update values completed[position] (graph.eval assignment completed[position])) := by
  intro node member
  have split : node ∈ completed.take position.val ∨ node = completed[position] := by
    have upto := List.take_succ_eq_append_getElem (l := completed) position.isLt
    rw [upto, List.mem_append, List.mem_singleton] at member
    exact member
  rcases split with prior | same
  · have different : node ≠ completed[position] := by
      intro equal
      subst node
      obtain ⟨index, indexBound, entry⟩ := List.mem_take_iff_getElem.mp prior
      have sameIndex : index = position.val := distinct.getElem_inj_iff.mp (by
        simpa only [Fin.getElem_fin] using entry)
      omega
    rw [Function.update_of_ne different]
    exact correct node prior
  · subst node
    exact Function.update_self _ _ _

/-- Only previously visited original child values are required. The memo
outside the produced ledger prefix may retain values from another cone. -/
private theorem warm_next_value (graph : DAG n) (assignment : Assignment n)
    (completed : List (Fin graph.nodeCount)) (position : Fin completed.length)
    (values : Fin graph.nodeCount → Bool) (ordered : Postorder graph completed)
    (correct : WarmPrefixCorrect graph assignment completed position.val values) :
    (graph.node completed[position]).eval assignment
      (fun child => values (graph.childIndex completed[position] child)) =
        graph.eval assignment completed[position] := by
  rw [graph.eval_eq]
  apply Gate.eval_congr
  · intro channel member
    rfl
  · intro child member
    exact warm_original_child_correct graph assignment completed position values
      ordered correct child member

/-- Every operand read is transported from the retained physical packet.
The original address and representation bound remain explicit. -/
private theorem retained_source_cell (current source : Array (Word width))
    (retained : CachePrefix current source) (address : Nat) (value : Word width)
    (sourceBound : address < source.size) (currentBound : address < current.size)
    (cell : source[address]'sourceBound = value) :
    current[address]'currentBound = value := by
  have same := retained ⟨address, sourceBound⟩
  rw [Array.getElem?_eq_getElem currentBound] at same
  simp only [Fin.getElem_fin] at same
  exact (Option.some.inj same).trans cell

/-- The physical header condition comes from the source adapter and survives
all DFS stores. It is not inferred from child incidence agreement alone. -/
private theorem retained_typed_head (caller current : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (retained : CachePrefix current (ForestIndexedOperands.cacheHeap width caller rows roots))
    (node : Fin graph.nodeCount) :
    current[caller.size + 2 * node.val + 1]? =
      some (word width (UniformDAGSource.typedHead (graph.node node))) := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have bounded : caller.size + (2 * node.val + 1) <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have original := ForestIndexedOperands.cache_header_word caller rows roots (2 * node.val + 1)
    (by rw [ForestIndexedOperands.rowHeaders_length]; omega)
  rw [ForestIndexedOperands.header_head_value rows node.val rowBound, heads.head node] at original
  have stored := retained ⟨caller.size + (2 * node.val + 1), bounded⟩
  have result := stored.trans (congrArg some original)
  simpa only [Nat.add_assoc] using result

private structure ChildMetadata (graph : DAG n) (layout : SharedLayout)
    (heap : Array (Word width)) (arityBase childDirectory : Nat)
    (child : Fin graph.nodeCount) where
  cursor : Nat
  arityBound : arityBase + 2 * child.val < heap.size
  directoryBound : childDirectory + 2 * child.val < heap.size
  arityBeforeMarker : arityBase + 2 * child.val < layout.nodeMarkerBase
  directoryBeforeMarker : childDirectory + 2 * child.val < layout.nodeMarkerBase
  arity : heap[arityBase + 2 * child.val]'arityBound = word width (graph.node child).children.length
  directory : heap[childDirectory + 2 * child.val]'directoryBound = word width cursor
  slice : ScopeStored heap cursor (graph.node child).children
  endBound : cursor + (graph.node child).children.length ≤ layout.nodeMarkerBase

private def retained_child_metadata (caller heap : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (layout : SharedLayout)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (retained : CachePrefix heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : heap.size = layout.storageEnd) (child : Fin graph.nodeCount) :
    ChildMetadata graph layout heap (caller.size + 4 * rows.length)
      (caller.size + 2 * rows.length) child := by
  have valid : child.val < rows.length := by rw [matched.length_eq]; exact child.isLt
  have sourceLength := sourceSize
  simp only [ForestIndexedOperands.cacheHeap_size] at sourceLength
  have sourceBelowHeap : layout.sourceEnd < heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega
  have sourceBelowMarker : layout.sourceEnd ≤ layout.nodeMarkerBase := by
    simp only [SharedLayout.nodeMarkerBase]
    omega
  have aritySource : caller.size + 4 * rows.length + 2 * child.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have directorySource : caller.size + 2 * rows.length + 2 * child.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have arityBound : caller.size + 4 * rows.length + 2 * child.val < heap.size := by
    rw [sourceSize] at aritySource
    omega
  have directoryBound : caller.size + 2 * rows.length + 2 * child.val < heap.size := by
    rw [sourceSize] at directorySource
    omega
  refine ⟨caller.size + 6 * rows.length +
      (ForestIndexedOperands.rowChildren (rows.take child.val)).length,
    arityBound, directoryBound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceSize] at aritySource
    omega
  · rw [sourceSize] at directorySource
    omega
  · have cell := retained ⟨_, aritySource⟩
    have original := ForestIndexedOperands.cache_child_arity_word caller graph rows roots matched child
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem arityBound] at exactCell
    exact Option.some.inj exactCell
  · have cell := retained ⟨_, directorySource⟩
    have original := (ForestIndexedOperands.cache_base_words caller rows roots child.val valid).1
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem directoryBound] at exactCell
    exact Option.some.inj exactCell
  · intro position
    change heap[(caller.size + 6 * rows.length +
        (ForestIndexedOperands.rowChildren (rows.take child.val)).length) + position.val]? =
      some (word width ((graph.node child).children[position.val]'position.isLt).val)
    exact retained_child_cell caller heap graph rows roots matched retained child
      position.val position.isLt
  · have lengths := congrArg List.length (ForestInputStored.row_children_split rows child.val valid)
    simp only [List.length_append, (matched.node child).2.2.1, List.length_map] at lengths
    omega


private structure RetainedScopeMetadata (graph : DAG n) (layout : SharedLayout)
    (heap caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (node : Fin graph.nodeCount) where
  tagBound : caller.size + 2 * node.val < heap.size
  arityBound : caller.size + 4 * rows.length + (2 * node.val + 1) < heap.size
  directoryBound : caller.size + 2 * rows.length + (2 * node.val + 1) < heap.size
  tagCell : heap[caller.size + 2 * node.val]'tagBound =
    word width (ForestIndexedOperands.tagValue graph node)
  arityCell : heap[caller.size + 4 * rows.length + (2 * node.val + 1)]'arityBound =
    word width (graph.node node).guardLabels.length
  directoryCell : heap[caller.size + 2 * rows.length + (2 * node.val + 1)]'directoryBound =
    word width (caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards (rows.take node.val)).length)
  guardEnd : caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
    (ForestIndexedOperands.rowGuards (rows.take node.val)).length +
    (graph.node node).guardLabels.length ≤ layout.nodeMarkerBase
  scope : ScopeStored heap
    (caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards (rows.take node.val)).length)
    (graph.node node).guardLabels

private def retained_scope_metadata (caller heap : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (layout : SharedLayout)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (retained : CachePrefix heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : heap.size = layout.storageEnd) (node : Fin graph.nodeCount) :
    RetainedScopeMetadata graph layout heap caller rows node := by
  have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have sourceBelowHeap : layout.sourceEnd < heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega
  have sourceBelowMarker : layout.sourceEnd ≤ layout.nodeMarkerBase := by
    simp only [SharedLayout.nodeMarkerBase]
    omega
  have tagSource : caller.size + 2 * node.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have aritySource : caller.size + 4 * rows.length + (2 * node.val + 1) <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have directorySource : caller.size + 2 * rows.length + (2 * node.val + 1) <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have tagBound : caller.size + 2 * node.val < heap.size := by
    rw [sourceSize] at tagSource
    omega
  have arityBound : caller.size + 4 * rows.length + (2 * node.val + 1) < heap.size := by
    rw [sourceSize] at aritySource
    omega
  have directoryBound : caller.size + 2 * rows.length + (2 * node.val + 1) < heap.size := by
    rw [sourceSize] at directorySource
    omega
  refine {
    tagBound := tagBound, arityBound := arityBound, directoryBound := directoryBound,
    tagCell := ?_, arityCell := ?_, directoryCell := ?_, guardEnd := ?_,
    scope := guard_scope_stored caller heap graph rows roots matched retained node }
  · have cell := retained ⟨_, tagSource⟩
    have original := ForestIndexedOperands.cache_tag_word caller graph rows roots matched node
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem tagBound] at exactCell
    exact Option.some.inj exactCell
  · have cell := retained ⟨_, aritySource⟩
    have original := ForestIndexedOperands.cache_guard_arity_word caller graph rows roots matched node
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem arityBound] at exactCell
    exact Option.some.inj exactCell
  · have cell := retained ⟨_, directorySource⟩
    have original := (ForestIndexedOperands.cache_base_words caller rows roots node.val valid).2
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem directoryBound] at exactCell
    exact Option.some.inj exactCell
  · have lengths := congrArg List.length (ForestInputStored.row_guards_split rows node.val valid)
    simp only [List.length_append, (matched.node node).2.2.2, List.length_map] at lengths
    have sourceLength := sourceSize
    simp only [ForestIndexedOperands.cacheHeap_size] at sourceLength
    omega


/-- Layout addresses are the retained packet directories and shared resident
value tables. They do not describe a newly constructed incidence index. -/
def warmLayout (caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (layout : SharedLayout) : UniformDAGNode.Layout where
  tagBase := caller.size
  headBase := caller.size + 1
  channelBase := layout.channelValueBase
  nodeBase := layout.nodeValueBase
  childArityBase := caller.size + 4 * rows.length
  childSourceBase := caller.size + 2 * rows.length
  guardArityBase := caller.size + 4 * rows.length + 1
  guardSourceBase := caller.size + 2 * rows.length + 1

private theorem warm_zero_handler (program : Program width 4) (state : State width 4)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (retained : CachePrefix state.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceEnd : (ForestIndexedOperands.cacheHeap width caller rows roots).size ≤ state.heap.size)
    (node : Fin graph.nodeCount) (gate : graph.node node = .zero)
    (offset : state.reg 3 = word width (2 * node.val))
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program entry (UniformDAGNode.code width entry (warmLayout caller rows layout))) :
    ∃ final, Execution program state final 8 (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width false) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 109) ∧ final.halted = false := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have tagSource : caller.size + 2 * node.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have tagBound : caller.size + 2 * node.val < state.heap.size := by omega
  have tagFits : caller.size + 2 * node.val < 2 ^ width := by omega
  have tag := ForestIndexedOperands.cache_tag_word caller graph rows roots matched node
  have tagCell := retained_source_cell state.heap _ retained _ _ tagSource tagBound tag
  have actualTag : state.heap[caller.size + 2 * node.val]'tagBound = word width 0 := by
    simpa only [ForestIndexedOperands.tagValue, gate] using tagCell
  exact UniformDAGNode.execution_zero program state entry (2 * node.val)
    (warmLayout caller rows layout) offset tagFits tagBound actualTag position running codeFits room block

private theorem warm_input_handler (program : Program width 4) (state : State width 4)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (retained : CachePrefix state.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceEnd : (ForestIndexedOperands.cacheHeap width caller rows roots).size ≤ state.heap.size)
    (channelEnd : layout.channelValueBase + n ≤ state.heap.size)
    (assignment : Assignment n)
    (channels : ∀ channel : Channel n,
      state.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)))
    (node : Fin graph.nodeCount) (channel : Channel n) (gate : graph.node node = .input channel)
    (offset : state.reg 3 = word width (2 * node.val))
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program entry (UniformDAGNode.code width entry (warmLayout caller rows layout))) :
    ∃ final, Execution program state final 16 (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width (assignment channel)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 109) ∧ final.halted = false := by
  have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have tagSource : caller.size + 2 * node.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have tagBound : caller.size + 2 * node.val < state.heap.size := by omega
  have headBound : caller.size + 2 * node.val + 1 < state.heap.size := by
    have bounded : caller.size + 2 * node.val + 1 <
        (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
      simp only [ForestIndexedOperands.cacheHeap_size]
      omega
    omega
  have valueBound : layout.channelValueBase + channel.val < state.heap.size := by
    have := channel.isLt
    omega
  have tag := ForestIndexedOperands.cache_tag_word caller graph rows roots matched node
  have tagCell := retained_source_cell state.heap _ retained _ _ tagSource tagBound tag
  have actualTag : state.heap[caller.size + 2 * node.val]'tagBound = word width 1 := by
    simpa only [ForestIndexedOperands.tagValue, gate] using tagCell
  have head := retained_typed_head caller state.heap graph rows roots matched heads retained node
  have actualHead : state.heap[caller.size + 1 + 2 * node.val]'(by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using headBound) = word width channel.val := by
    rw [Array.getElem?_eq_getElem headBound] at head
    have wordHead := Option.some.inj head
    simpa only [UniformDAGSource.typedHead, gate, warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wordHead
  have channelCell := channels channel
  rw [Array.getElem?_eq_getElem valueBound] at channelCell
  exact UniformDAGNode.execution_input program state entry (2 * node.val) channel.val
    (warmLayout caller rows layout) (assignment channel) offset
    (by change caller.size + 2 * node.val < 2 ^ width; omega)
    (by change caller.size + 1 + 2 * node.val < 2 ^ width; omega)
    (by exact Nat.lt_trans valueBound room)
    tagBound (by simpa only [warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using headBound)
    valueBound actualTag actualHead (Option.some.inj channelCell) position running codeFits room block

private theorem warm_or_handler (program : Program width 4) (state : State width 4)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (retained : CachePrefix state.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : state.heap.size = layout.storageEnd)
    (dimension : layout.nodeCount = graph.nodeCount)
    (values : Fin graph.nodeCount → Bool)
    (table : ∀ child : Fin graph.nodeCount,
      state.heap[layout.nodeValueBase + child.val]? = some (boolWord width (values child)))
    (node : Fin graph.nodeCount) (refs : List (Fin node.val)) (gate : graph.node node = .disj refs)
    (offset : state.reg 3 = word width (2 * node.val))
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program entry (UniformDAGNode.code width entry (warmLayout caller rows layout))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 18 * refs.length + 23 ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width
        (refs.any (fun child => values (graph.childIndex node child)))) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 109) ∧ final.halted = false := by
  let metadata := retained_child_metadata caller state.heap graph rows roots layout
    matched retained sourceSize allocation node
  let reads := fun child : Fin node.val => values (graph.childIndex node child)
  have tagSource : caller.size + 2 * node.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have sourceBelow : layout.sourceEnd < state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega
  have tagBound : caller.size + 2 * node.val < state.heap.size := by rw [sourceSize] at tagSource; omega
  have tagCell := retained_source_cell state.heap _ retained _ _ tagSource tagBound
    (ForestIndexedOperands.cache_tag_word caller graph rows roots matched node)
  have actualTag : state.heap[caller.size + 2 * node.val]'tagBound = word width 2 := by
    simpa only [ForestIndexedOperands.tagValue, gate] using tagCell
  have markerBelow : layout.nodeMarkerBase < state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have tableEnd : layout.nodeValueBase + node.val ≤ state.heap.size := by
    try dsimp only [SharedLayout.nodeValueBase]
    have := node.isLt
    simp only [SharedLayout.nodeValueBase, SharedLayout.nodeMarkerBase, dimension] at markerBelow
    omega
  have cursorEnd : metadata.cursor + refs.length < state.heap.size := by
    have endBound := metadata.endBound
    simp only [gate, Gate.children] at endBound
    omega
  have scope : ScopeStored state.heap metadata.cursor refs := by
    simpa only [gate, Gate.children] using metadata.slice
  have cells := warm_incidence_cells state.heap metadata.cursor layout.nodeValueBase node.val refs reads
    scope cursorEnd.le tableEnd room (by
      intro child
      simpa only [reads, DAG.childIndex] using table (graph.childIndex node child))
  obtain ⟨final, ticks, peak, trace, charged, space, heap, stack, output, pc, live⟩ :=
    UniformDAGNode.execution_or program state entry (2 * node.val) metadata.cursor
      (warmLayout caller rows layout) (refs.map reads) offset (by try dsimp only [warmLayout, SharedLayout.nodeValueBase, SharedLayout.channelValueBase]; omega) tagBound actualTag
      (by try dsimp only [warmLayout]; have := metadata.arityBound; omega) (by try dsimp only [warmLayout]; have := metadata.directoryBound; omega)
      metadata.arityBound metadata.directoryBound
      (by simpa only [warmLayout, gate, Gate.children, List.length_map] using metadata.arity)
      metadata.directory (by simpa only [List.length_map] using (show metadata.cursor + refs.length < 2 ^ width from by omega))
      (by simp only [List.length_map]; omega) cells position running codeFits room block
  refine ⟨final, ticks, peak, trace, ?_, space, ?_, stack, output, pc, live⟩
  · simpa only [List.length_map] using charged
  · simpa only [List.any_map, Function.comp_def, reads] using heap

private theorem warm_guard_handler (program : Program width 4) (state : State width 4)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (retained : CachePrefix state.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : state.heap.size = layout.storageEnd)
    (dimension : layout.nodeCount = graph.nodeCount)
    (channelDimension : layout.channels = n)
    (assignment : Assignment n) (values : Fin graph.nodeCount → Bool)
    (channels : ∀ channel : Channel n,
      state.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)))
    (table : ∀ child : Fin graph.nodeCount,
      state.heap[layout.nodeValueBase + child.val]? = some (boolWord width (values child)))
    (node : Fin graph.nodeCount) (child : Fin node.val) (guards : List (Channel n))
    (gate : graph.node node = .guard child guards)
    (offset : state.reg 3 = word width (2 * node.val))
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program entry (UniformDAGNode.code width entry (warmLayout caller rows layout))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 18 * guards.length + 30 ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width
        (values (graph.childIndex node child) && !(guards.any assignment))) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 109) ∧ final.halted = false := by
  let metadata := retained_scope_metadata caller state.heap graph rows roots layout
    matched retained sourceSize allocation node
  let cursor := caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
    (ForestIndexedOperands.rowGuards (rows.take node.val)).length
  have markerBelow : layout.nodeMarkerBase < state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have headBound : caller.size + 2 * node.val + 1 < state.heap.size := by
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    have below : caller.size + 2 * node.val + 1 <
        (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
      simp only [ForestIndexedOperands.cacheHeap_size]
      omega
    rw [sourceSize] at below
    simp only [SharedLayout.nodeMarkerBase] at markerBelow
    omega
  have childBound : layout.nodeValueBase + child.val < state.heap.size := by
    try dsimp only [SharedLayout.nodeValueBase]
    have := child.isLt
    have := node.isLt
    simp only [SharedLayout.nodeValueBase, SharedLayout.nodeMarkerBase, dimension] at markerBelow
    omega
  have channelsEnd : layout.channelValueBase + n ≤ state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.channelValueBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
      SharedLayout.nodeMarkerBase, channelDimension]
    omega
  have guardsEnd : cursor + guards.length < state.heap.size := by
    have bounded := metadata.guardEnd
    simp only [gate, Gate.guardLabels] at bounded
    change cursor + guards.length ≤ layout.nodeMarkerBase at bounded
    omega
  have cells := warm_incidence_cells state.heap cursor layout.channelValueBase n guards assignment
    (by simpa only [cursor, gate, Gate.guardLabels] using metadata.scope)
    guardsEnd.le channelsEnd room channels
  have head := retained_typed_head caller state.heap graph rows roots matched heads retained node
  rw [Array.getElem?_eq_getElem headBound] at head
  have actualHead : state.heap[caller.size + 1 + 2 * node.val]'(by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using headBound) = word width child.val := by
    simpa only [UniformDAGSource.typedHead, gate, warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Option.some.inj head
  have childCell := table (graph.childIndex node child)
  change state.heap[layout.nodeValueBase + child.val]? = _ at childCell
  rw [Array.getElem?_eq_getElem childBound] at childCell
  obtain ⟨final, ticks, peak, trace, charged, space, heap, stack, output, pc, live⟩ :=
    UniformDAGNode.execution_guard program state entry (2 * node.val) child.val cursor
      (warmLayout caller rows layout) (values (graph.childIndex node child)) (guards.map assignment)
      offset (by try dsimp only [warmLayout]; have := metadata.tagBound; omega) metadata.tagBound
      (by simpa only [warmLayout, gate, ForestIndexedOperands.tagValue] using metadata.tagCell)
      (by change caller.size + 1 + 2 * node.val < 2 ^ width; omega)
      (by exact Nat.lt_trans childBound room)
      (by simpa only [warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using headBound)
      childBound actualHead (Option.some.inj childCell)
      (by try dsimp only [warmLayout]; have := metadata.arityBound; omega) (by try dsimp only [warmLayout]; have := metadata.directoryBound; omega)
      (by simpa only [warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using metadata.arityBound)
      (by simpa only [warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using metadata.directoryBound)
      (by simpa only [gate, Gate.guardLabels, List.length_map, warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using metadata.arityCell)
      (by simpa only [cursor, warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using metadata.directoryCell)
      (by simpa only [List.length_map] using (show cursor + guards.length < 2 ^ width from by omega))
      (by simp only [List.length_map]; omega) cells position running codeFits room block
  refine ⟨final, ticks, peak, trace, ?_, space, ?_, stack, output, pc, live⟩
  · simpa only [List.length_map] using charged
  · simpa only [List.any_map, Function.comp_def] using heap

private theorem warm_and_handler (program : Program width 4) (state : State width 4)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (retained : CachePrefix state.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : state.heap.size = layout.storageEnd)
    (dimension : layout.nodeCount = graph.nodeCount)
    (values : Fin graph.nodeCount → Bool)
    (table : ∀ child : Fin graph.nodeCount,
      state.heap[layout.nodeValueBase + child.val]? = some (boolWord width (values child)))
    (node : Fin graph.nodeCount) (left right : Fin node.val)
    (gate : graph.node node = .liveAnd left right)
    (offset : state.reg 3 = word width (2 * node.val))
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program entry (UniformDAGNode.code width entry (warmLayout caller rows layout))) :
    ∃ final, Execution program state final
        (if values (graph.childIndex node left) then 30 else 29) (state.liveWords + 1) ∧
      final.heap = state.heap.push (boolWord width
        (values (graph.childIndex node left) && values (graph.childIndex node right))) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 109) ∧ final.halted = false := by
  let metadata := retained_child_metadata caller state.heap graph rows roots layout
    matched retained sourceSize allocation node
  have markerBelow : layout.nodeMarkerBase < state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have tagSource : caller.size + 2 * node.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have tagBound : caller.size + 2 * node.val < state.heap.size := by
    rw [sourceSize] at tagSource
    simp only [SharedLayout.nodeMarkerBase] at markerBelow
    omega
  have tag := retained_source_cell state.heap _ retained _ _ tagSource tagBound
    (ForestIndexedOperands.cache_tag_word caller graph rows roots matched node)
  have actualTag : state.heap[caller.size + 2 * node.val]'tagBound = word width 4 := by
    simpa only [gate, ForestIndexedOperands.tagValue] using tag
  have headBound : caller.size + 2 * node.val + 1 < state.heap.size := by
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    have below : caller.size + 2 * node.val + 1 <
        (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
      simp only [ForestIndexedOperands.cacheHeap_size]
      omega
    rw [sourceSize] at below
    simp only [SharedLayout.nodeMarkerBase] at markerBelow
    omega
  have memoBound : ∀ child : Fin node.val, layout.nodeValueBase + child.val < state.heap.size := by
    try dsimp only [SharedLayout.nodeValueBase]
    intro child
    have := child.isLt
    have := node.isLt
    simp only [SharedLayout.nodeValueBase, SharedLayout.nodeMarkerBase, dimension] at markerBelow
    omega
  have cursorBound : metadata.cursor + 1 < state.heap.size := by
    have below := metadata.endBound
    simp only [gate, Gate.children, List.length_cons, List.length_nil] at below
    omega
  have head := retained_typed_head caller state.heap graph rows roots matched heads retained node
  rw [Array.getElem?_eq_getElem headBound] at head
  have actualHead : state.heap[caller.size + 1 + 2 * node.val]'(by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using headBound) = word width left.val := by
    simpa only [UniformDAGSource.typedHead, gate, warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Option.some.inj head
  have rightCell := metadata.slice ⟨1, by simp only [gate, Gate.children, List.length_cons, List.length_nil]; omega⟩
  simp only [gate, Gate.children, Fin.getElem_fin, List.getElem_cons_succ, List.getElem_cons_zero] at rightCell
  rw [Array.getElem?_eq_getElem cursorBound] at rightCell
  have leftCell := table (graph.childIndex node left)
  have rightValue := table (graph.childIndex node right)
  change state.heap[layout.nodeValueBase + left.val]? = _ at leftCell
  change state.heap[layout.nodeValueBase + right.val]? = _ at rightValue
  rw [Array.getElem?_eq_getElem (memoBound left)] at leftCell
  rw [Array.getElem?_eq_getElem (memoBound right)] at rightValue
  exact UniformDAGNode.execution_and program state entry (2 * node.val) metadata.cursor left.val right.val
    (warmLayout caller rows layout) (values (graph.childIndex node left)) (values (graph.childIndex node right))
    offset (by try dsimp only [warmLayout, SharedLayout.nodeValueBase, SharedLayout.channelValueBase]; omega) tagBound actualTag (by try dsimp only [warmLayout, SharedLayout.nodeValueBase, SharedLayout.channelValueBase]; omega) (by try dsimp only [warmLayout]; have := metadata.directoryBound; omega)
    (by exact Nat.lt_trans cursorBound room) (by try dsimp only [warmLayout]; have := memoBound left; omega) (by try dsimp only [warmLayout]; have := memoBound right; omega)
    (by simpa only [warmLayout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using headBound)
    metadata.directoryBound cursorBound (memoBound left) (memoBound right) actualHead metadata.directory
    (Option.some.inj rightCell) (Option.some.inj leftCell) (Option.some.inj rightValue)
    position running codeFits room block

/-- The actual dispatcher and selected stored-operand handler cover the full
original gate grammar on the resident shared heap. -/
private theorem warm_node_handler (program : Program width 4) (state : State width 4)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (retained : CachePrefix state.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : state.heap.size = layout.storageEnd)
    (dimension : layout.nodeCount = graph.nodeCount) (channelDimension : layout.channels = n)
    (assignment : Assignment n) (values : Fin graph.nodeCount → Bool)
    (channels : ∀ channel : Channel n,
      state.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)))
    (table : ∀ child : Fin graph.nodeCount,
      state.heap[layout.nodeValueBase + child.val]? = some (boolWord width (values child)))
    (node : Fin graph.nodeCount) (offset : state.reg 3 = word width (2 * node.val))
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (block : BlockAt program entry (UniformDAGNode.code width entry (warmLayout caller rows layout))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 30 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) ∧
      peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width
        ((graph.node node).eval assignment (fun child => values (graph.childIndex node child)))) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 109) ∧ final.halted = false := by
  have sourceEnd : (ForestIndexedOperands.cacheHeap width caller rows roots).size ≤ state.heap.size := by
    rw [sourceSize, allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega
  have channelEnd : layout.channelValueBase + n ≤ state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.channelValueBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
      SharedLayout.nodeMarkerBase, channelDimension]
    omega
  cases gate : graph.node node with
  | zero =>
      obtain ⟨final, trace, heap, stack, output, pc, live⟩ :=
        warm_zero_handler program state caller graph rows roots layout matched retained sourceEnd node gate
          offset entry position running codeFits room block
      refine ⟨final, 8, state.liveWords + 1, trace, ?_, by omega, ?_, stack, output, pc, live⟩
      · simp only [gate, Gate.children, Gate.guardLabels, List.length_nil]; omega
      · simpa only [gate, Gate.eval] using heap
  | input channel =>
      obtain ⟨final, trace, heap, stack, output, pc, live⟩ :=
        warm_input_handler program state caller graph rows roots layout matched heads retained sourceEnd
          channelEnd assignment channels node channel gate offset entry position running codeFits room block
      refine ⟨final, 16, state.liveWords + 1, trace, ?_, by omega, ?_, stack, output, pc, live⟩
      · simp only [gate, Gate.children, Gate.guardLabels, List.length_nil]; omega
      · simpa only [gate, Gate.eval] using heap
  | disj refs =>
      obtain ⟨final, ticks, peak, trace, charged, space, heap, stack, output, pc, live⟩ :=
        warm_or_handler program state caller graph rows roots layout matched retained sourceSize allocation
          dimension values table node refs gate offset entry position running codeFits room block
      refine ⟨final, ticks, peak, trace, ?_, space, ?_, stack, output, pc, live⟩
      · simp only [gate, Gate.children, Gate.guardLabels, List.length_nil]; omega
      · simpa only [gate, Gate.eval] using heap
  | guard child labels =>
      obtain ⟨final, ticks, peak, trace, charged, space, heap, stack, output, pc, live⟩ :=
        warm_guard_handler program state caller graph rows roots layout matched heads retained sourceSize
          allocation dimension channelDimension assignment values channels table node child labels gate
          offset entry position running codeFits room block
      refine ⟨final, ticks, peak, trace, ?_, space, ?_, stack, output, pc, live⟩
      · simp only [gate, Gate.children, Gate.guardLabels, List.length_singleton]; omega
      · simpa only [gate, Gate.eval] using heap
  | liveAnd left right =>
      obtain ⟨final, trace, heap, stack, output, pc, live⟩ :=
        warm_and_handler program state caller graph rows roots layout matched heads retained sourceSize
          allocation dimension values table node left right gate offset entry position running codeFits room block
      refine ⟨final, _, state.liveWords + 1, trace, ?_, by omega, ?_, stack, output, pc, live⟩
      · simp only [gate, Gate.children, Gate.guardLabels, List.length_cons, List.length_nil]
        split <;> omega
      · simpa only [gate, Gate.eval] using heap

private theorem padded_block (entry : Nat) (code : Code width) :
    BlockAt (Array.replicate entry (.halt : Instruction width 4) ++ code.toArray) entry code := by
  intro offset bound
  rw [Array.getElem?_append_right (by simp only [Array.size_replicate]; omega)]
  simp only [Array.size_replicate, Nat.add_sub_cancel_left, List.getElem?_toArray]

/-- All five fetched node handlers execute inside the real eight-register
warm driver. The executed footprint is inferred from successful low-register
execution, and the four charged driver registers are retained exactly. -/
theorem warm_node_execution (program : Program width 8) (state : State width 8)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (retained : CachePrefix state.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : state.heap.size = layout.storageEnd)
    (dimension : layout.nodeCount = graph.nodeCount) (channelDimension : layout.channels = n)
    (assignment : Assignment n) (values : Fin graph.nodeCount → Bool)
    (channels : ∀ channel : Channel n,
      state.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)))
    (table : ∀ child : Fin graph.nodeCount,
      state.heap[layout.nodeValueBase + child.val]? = some (boolWord width (values child)))
    (node : Fin graph.nodeCount) (offset : state.reg 3 = word width (2 * node.val))
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 109 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (physical : ∀ phase : Fin (UniformDAGNode.code width entry (warmLayout caller rows layout)).length,
      program[entry + phase.val]? = some (widenInstruction
        ((UniformDAGNode.code width entry (warmLayout caller rows layout)).toArray[phase.val]))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 30 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) ∧
      peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap.push (boolWord width
        ((graph.node node).eval assignment (fun child => values (graph.childIndex node child)))) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) ∧
      final.pc = word width (entry + 109) ∧ final.halted = false := by
  let code := UniformDAGNode.code width entry (warmLayout caller rows layout)
  let padded : Program width 4 := Array.replicate entry .halt ++ code.toArray
  obtain ⟨final, ticks, peak, trace, charged, space, heap, stack, output, pc, live⟩ :=
    warm_node_handler padded (narrowState state) caller graph rows roots layout matched heads retained
      sourceSize allocation dimension channelDimension assignment values channels table node offset
      entry position running codeFits room (padded_block entry code)
  have lifted := widen_handler_execution program entry code.toArray
    (by intro phase; simpa only [code, List.size_toArray] using physical ⟨phase.val, by simpa only [code, List.size_toArray] using phase.isLt⟩)
    (narrowState state) final ticks peak trace live state.reg
  rw [widen_narrow] at lifted
  have realLive : state.liveWords = (narrowState state).liveWords + 4 := by
    have same := widenState_liveWords (narrowState state) state.reg
    rw [widen_narrow] at same
    exact same
  refine ⟨widenState final state.reg, ticks, peak + 4, lifted, charged, ?_, heap, stack, output,
    fun register high => widenState_high final state.reg register high, pc, live⟩
  omega

/-- The warm evaluator consumes the actual postorder source-ID ledger. The
handler's low registers retain four charged loop/root registers. Each result
is committed to its original-ID slot and its transient cell is released. -/
def warmLedgerCode (width entry nodeBase temporary : Nat)
    (layout : UniformDAGNode.Layout) : Program width 8 :=
  #[.branchZero 4 (word width (entry + 125)), .load 5 6, .add 3 5 5,
    .branchZero 2 (word width (entry + 4))] ++
  widenProgram (UniformDAGNode.code width (entry + 4) layout).toArray ++
  commitResultCode width temporary nodeBase ++
  #[.constant 2 (word width 0), .constant 3 (word width 1),
    .constant 5 (word width (2 ^ width - 1)), .add 4 4 5, .add 6 6 3,
    .branchZero 2 (word width entry)]

private theorem warmLedgerCode_size (width entry nodeBase temporary : Nat)
    (layout : UniformDAGNode.Layout) :
    (warmLedgerCode width entry nodeBase temporary layout).size = 125 := by
  simp only [warmLedgerCode, Array.size_append, List.size_toArray, widenProgram,
    Array.size_map, UniformDAGNode.code_length, commitResultCode]
  rfl

/-- The warm loop fetches the next original ID from its produced physical
ledger before entering the mapped node handler. The read does not substitute
an abstract iteration over a supplied list. -/
private def warmDriverPrefix (width entry : Nat) : Program width 8 :=
  #[.branchZero 4 (word width (entry + 125)), .load 5 6, .add 3 5 5,
    .branchZero 2 (word width (entry + 4))]

private theorem warm_driver_prefix (program : Program width 8)
    (state : State width 8) (entry cursor identifier remaining : Nat)
    (present : ∀ phase : Fin 4, program[entry + phase.val]? =
      (warmDriverPrefix width entry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 125 < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) (offsetFits : 2 * identifier < 2 ^ width)
    (remainingFits : remaining < 2 ^ width) (nonempty : remaining ≠ 0)
    (cursorBound : cursor < state.heap.size)
    (cell : state.heap[cursor]'cursorBound = word width identifier)
    (cursorHeld : state.reg 6 = word width cursor)
    (remainingHeld : state.reg 4 = word width remaining)
    (zeroHeld : state.reg 2 = word width 0) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 3 = word width (2 * identifier) ∧
      final.reg 5 = word width identifier ∧
      (∀ register : Fin 8, register ≠ 3 → register ≠ 5 →
        final.reg register = state.reg register) ∧
      final.pc = word width (entry + 4) ∧ final.halted = false := by
  let s1 := state.advance
  let s2 := s1.advance.put 5 (word width identifier)
  let s3 := s2.advance.put 3 (word width (2 * identifier))
  let final : State width 8 := { s3.advance with pc := word width (entry + 4) }
  have remainingVal : (word width remaining).val = remaining := Nat.mod_eq_of_lt remainingFits
  have cursorVal : (word width cursor).val = cursor := Nat.mod_eq_of_lt cursorFits
  have identifierFits : identifier < 2 ^ width := by omega
  have identifierVal : (word width identifier).val = identifier := Nat.mod_eq_of_lt identifierFits
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.branchZero 4 (word width (entry + 125)))
      (by simpa using position) (by omega)
      (by simpa [warmDriverPrefix] using present ⟨0, by decide⟩)]
    simp [step, final, s3, s2, s1, State.put, State.advance, running,
      remainingHeld, remainingVal, nonempty, cursorHeld, cursorVal,
      cursorBound, cell, identifierVal, zeroHeld, word, Nat.mul_comm, Nat.mul_two,
      Nat.mod_eq_of_lt remainingFits, Nat.mod_eq_of_lt identifierFits,
      Nat.mod_eq_of_lt offsetFits, Nat.mod_eq_of_lt cursorFits]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.load 5 6)
      (by simpa using p1) (by omega)
      (by simpa [warmDriverPrefix] using present ⟨1, by decide⟩)]
    simp [step, final, s3, s2, s1, State.put, State.advance, running,
      remainingHeld, remainingVal, nonempty, cursorHeld, cursorVal,
      cursorBound, cell, identifierVal, zeroHeld, word, Nat.mul_comm, Nat.mul_two,
      Nat.mod_eq_of_lt remainingFits, Nat.mod_eq_of_lt identifierFits,
      Nat.mod_eq_of_lt offsetFits, Nat.mod_eq_of_lt cursorFits]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 3 5 5)
      (by simpa using p2) (by omega)
      (by simpa [warmDriverPrefix] using present ⟨2, by decide⟩)]
    simp [step, final, s3, s2, s1, State.put, State.advance, running,
      remainingHeld, remainingVal, nonempty, cursorHeld, cursorVal,
      cursorBound, cell, identifierVal, zeroHeld, word, Nat.mul_comm, Nat.mul_two,
      Nat.mod_eq_of_lt remainingFits, Nat.mod_eq_of_lt identifierFits,
      Nat.mod_eq_of_lt offsetFits, Nat.mod_eq_of_lt cursorFits]
  have t3 : programStep program s3 = some final := by
    rw [fetched program s3 (entry + 3) (.branchZero 2 (word width (entry + 4)))
      (by simpa using p3) (by omega)
      (by simpa [warmDriverPrefix] using present ⟨3, by decide⟩)]
    simp [step, final, s3, s2, s1, State.put, State.advance, running,
      remainingHeld, remainingVal, nonempty, cursorHeld, cursorVal,
      cursorBound, cell, identifierVal, zeroHeld, word, Nat.mul_comm, Nat.mul_two,
      Nat.mod_eq_of_lt remainingFits, Nat.mod_eq_of_lt identifierFits,
      Nat.mod_eq_of_lt offsetFits, Nat.mod_eq_of_lt cursorFits]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, rfl, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1
      (Execution.cons t2 (Execution.cons t3 (Execution.refl final))))
    simpa [final, s3, s2, s1, State.liveWords, State.put, State.advance] using trace
  · simp [final, s3, State.put, State.advance]
  · simp [final, s3, s2, State.put, State.advance]
  · intro register different3 different5
    simp [final, s3, s2, s1, State.put, State.advance, different3, different5]

/-- Counted traversal of the produced original-ID node ledger. Each actual
ledger ID clears its own marker and sparse rank-map cell. -/
def resetNodesCode (width base markerBase mapBase : Nat) : Program width 8 := #[
  .branchZero 4 (word width (base + 12)), .load 0 6,
  .constant 1 (word width markerBase), .add 1 1 0, .store 1 2,
  .constant 1 (word width mapBase), .add 1 1 0, .store 1 2,
  .constant 5 (word width (2 ^ width - 1)), .add 4 4 5,
  .add 6 6 3, .branchZero 2 (word width base)]

/-- Channel reuse clears only IDs actually published to the channel ledger. -/
def resetChannelsCode (width base markerBase : Nat) : Program width 8 := #[
  .branchZero 4 (word width (base + 9)), .load 0 6,
  .constant 1 (word width markerBase), .add 1 1 0, .store 1 2,
  .constant 5 (word width (2 ^ width - 1)), .add 4 4 5,
  .add 6 6 3, .branchZero 2 (word width base)]

/-- Both produced ledgers become empty by actual count-header stores. The
ledger payload cells remain dead until overwritten by the next query. -/
def clearLedgerCountsCode (width nodeCountSlot channelCountSlot : Nat) : Program width 8 := #[
  .constant 1 (word width nodeCountSlot), .store 1 2,
  .constant 1 (word width channelCountSlot), .store 1 2]

@[simp] theorem resetNodesCode_size (width base markerBase mapBase : Nat) :
    (resetNodesCode width base markerBase mapBase).size = 12 := rfl
@[simp] theorem resetChannelsCode_size (width base markerBase : Nat) :
    (resetChannelsCode width base markerBase).size = 9 := rfl
@[simp] theorem clearLedgerCountsCode_size (width nodeCountSlot channelCountSlot : Nat) :
    (clearLedgerCountsCode width nodeCountSlot channelCountSlot).size = 4 := rfl

def clearNodes (layout : SharedLayout) (heap : Array (Word width)) {dimension : Nat} :
    List (Fin dimension) → Array (Word width)
  | [] => heap
  | node :: rest => clearNodes layout
      ((heap.setIfInBounds (layout.nodeMarkerBase + node.val) (word width 0)).setIfInBounds
        (layout.mapBase + node.val) (word width 0)) rest

def clearChannels (layout : SharedLayout) (heap : Array (Word width)) {dimension : Nat} :
    List (Fin dimension) → Array (Word width)
  | [] => heap
  | channel :: rest => clearChannels layout
      (heap.setIfInBounds (layout.channelMarkerBase + channel.val) (word width 0)) rest

theorem reset_node_iteration (program : Program width 8) (initial : State width 8)
    (base markerBase mapBase cursor node remaining : Nat)
    (present : ∀ phase : Fin 12, program[base + phase.val]? =
      (resetNodesCode width base markerBase mapBase)[phase.val]?)
    (position : initial.pc = word width base) (running : initial.halted = false)
    (codeFits : base + 12 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (markerFits : markerBase + node < 2 ^ width) (mapFits : mapBase + node < 2 ^ width)
    (countHeld : initial.reg 4 = word width (remaining + 1))
    (cursorHeld : initial.reg 6 = word width cursor)
    (zero : initial.reg 2 = word width 0) (one : initial.reg 3 = word width 1)
    (cursorBound : cursor < initial.heap.size)
    (sourceCell : initial.heap[cursor]'cursorBound = word width node)
    (markerBound : markerBase + node < initial.heap.size)
    (mapBound : mapBase + node < initial.heap.size) :
    ∃ final, Execution program initial final 12 initial.liveWords ∧
      final.heap = (initial.heap.set (markerBase + node) (word width 0) markerBound).set
        (mapBase + node) (word width 0) (by simpa only [Array.size_set] using mapBound) ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧ final.reg 7 = initial.reg 7 ∧
      final.pc = word width base ∧ final.halted = false := by
  let s1 : State width 8 := initial.advance
  let s2 : State width 8 := s1.advance.put 0 (word width node)
  let s3 : State width 8 := s2.advance.put 1 (word width markerBase)
  let s4 : State width 8 := s3.advance.put 1 (word width (markerBase + node))
  let s5 : State width 8 := { s4.advance with heap := initial.heap.set (markerBase + node) (word width 0) markerBound }
  let s6 : State width 8 := s5.advance.put 1 (word width mapBase)
  let s7 : State width 8 := s6.advance.put 1 (word width (mapBase + node))
  let s8 : State width 8 := { s7.advance with heap := (initial.heap.set (markerBase + node) (word width 0) markerBound).set (mapBase + node) (word width 0) (by simpa only [Array.size_set] using mapBound) }
  let s9 : State width 8 := s8.advance.put 5 (word width (2 ^ width - 1))
  let s10 : State width 8 := s9.advance.put 4 (word width remaining)
  let s11 : State width 8 := s10.advance.put 6 (word width (cursor + 1))
  let final : State width 8 := { s11.advance with pc := word width base }
  have nodeFits : node < 2 ^ width := by omega
  have markerBaseFits : markerBase < 2 ^ width := by omega
  have mapBaseFits : mapBase < 2 ^ width := by omega
  have capacity : 1 < 2 ^ width := by omega
  have minusFits : 2 ^ width - 1 < 2 ^ width := by omega
  have predecessorSum : remaining + 1 + (2 ^ width - 1) = remaining + 2 ^ width := by omega
  have p1 : s1.pc = word width (base + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width base).val = base + 0 from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (base + 2) := by
    simp only [s2, State.advance, State.put, p1]
    rw [show (word width (base + 1)).val = base + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (base + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (base + 2)).val = base + 2 from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (base + 4) := by
    simp only [s4, State.advance, State.put, p3]
    rw [show (word width (base + 3)).val = base + 3 from Nat.mod_eq_of_lt (by omega)]
  have p5 : s5.pc = word width (base + 5) := by
    simp only [s5, State.advance, State.put, p4]
    rw [show (word width (base + 4)).val = base + 4 from Nat.mod_eq_of_lt (by omega)]
  have p6 : s6.pc = word width (base + 6) := by
    simp only [s6, State.advance, State.put, p5]
    rw [show (word width (base + 5)).val = base + 5 from Nat.mod_eq_of_lt (by omega)]
  have p7 : s7.pc = word width (base + 7) := by
    simp only [s7, State.advance, State.put, p6]
    rw [show (word width (base + 6)).val = base + 6 from Nat.mod_eq_of_lt (by omega)]
  have p8 : s8.pc = word width (base + 8) := by
    simp only [s8, State.advance, State.put, p7]
    rw [show (word width (base + 7)).val = base + 7 from Nat.mod_eq_of_lt (by omega)]
  have p9 : s9.pc = word width (base + 9) := by
    simp only [s9, State.advance, State.put, p8]
    rw [show (word width (base + 8)).val = base + 8 from Nat.mod_eq_of_lt (by omega)]
  have p10 : s10.pc = word width (base + 10) := by
    simp only [s10, State.advance, State.put, p9]
    rw [show (word width (base + 9)).val = base + 9 from Nat.mod_eq_of_lt (by omega)]
  have p11 : s11.pc = word width (base + 11) := by
    simp only [s11, State.advance, State.put, p10]
    rw [show (word width (base + 10)).val = base + 10 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial (base + 0) (.branchZero 4 (word width (base + 12)))
      (by simpa only [Nat.add_zero] using position)
      (by omega) (by simpa [resetNodesCode] using present ⟨0, by decide⟩)]
    simp only [step, running, Bool.false_eq_true, ite_false, countHeld,
      show (word width (remaining + 1)).val = remaining + 1 from Nat.mod_eq_of_lt countFits]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, s1]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.load 0 6)
      (by simpa only [Nat.add_zero] using p1)
      (by omega) (by simpa [resetNodesCode] using present ⟨1, by decide⟩)]
    simp [s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.constant 1 (word width markerBase))
      (by simpa only [Nat.add_zero] using p2)
      (by omega) (by simpa [resetNodesCode] using present ⟨2, by decide⟩)]
    simp [s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.add 1 1 0)
      (by simpa only [Nat.add_zero] using p3)
      (by omega) (by simpa [resetNodesCode] using present ⟨3, by decide⟩)]
    simp [s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.store 1 2)
      (by simpa only [Nat.add_zero] using p4)
      (by omega) (by simpa [resetNodesCode] using present ⟨4, by decide⟩)]
    simp [s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.constant 1 (word width mapBase))
      (by simpa only [Nat.add_zero] using p5)
      (by omega) (by simpa [resetNodesCode] using present ⟨5, by decide⟩)]
    simp [s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.add 1 1 0)
      (by simpa only [Nat.add_zero] using p6)
      (by omega) (by simpa [resetNodesCode] using present ⟨6, by decide⟩)]
    simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (base + 7) (.store 1 2)
      (by simpa only [Nat.add_zero] using p7)
      (by omega) (by simpa [resetNodesCode] using present ⟨7, by decide⟩)]
    simp [s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (base + 8) (.constant 5 (word width (2 ^ width - 1)))
      (by simpa only [Nat.add_zero] using p8)
      (by omega) (by simpa [resetNodesCode] using present ⟨8, by decide⟩)]
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t9 : programStep program s9 = some s10 := by
    rw [fetched program s9 (base + 9) (.add 4 4 5)
      (by simpa only [Nat.add_zero] using p9)
      (by omega) (by simpa [resetNodesCode] using present ⟨9, by decide⟩)]
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t10 : programStep program s10 = some s11 := by
    rw [fetched program s10 (base + 10) (.add 6 6 3)
      (by simpa only [Nat.add_zero] using p10)
      (by omega) (by simpa [resetNodesCode] using present ⟨10, by decide⟩)]
    simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t11 : programStep program s11 = some final := by
    rw [fetched program s11 (base + 11) (.branchZero 2 (word width base))
      (by simpa only [Nat.add_zero] using p11)
      (by omega) (by simpa [resetNodesCode] using present ⟨11, by decide⟩)]
    simp [final, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld,
      zero, one, word, sourceCell, cursorBound, markerBound, mapBound,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt nodeFits,
      Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt mapBaseFits,
      Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt mapFits, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.refl (p := program) final))))))))))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa [final, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set, Nat.max_self] using trace
  all_goals simp [final, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running]

/-- Resetting produced node IDs changes only their marker/map cells. -/
private theorem clearNodes_frame (layout : SharedLayout) (heap : Array (Word width))
    {dimension : Nat} (nodes : List (Fin dimension)) (address : Nat)
    (outside : ∀ node ∈ nodes,
      layout.nodeMarkerBase + node.val ≠ address ∧ layout.mapBase + node.val ≠ address) :
    (clearNodes layout heap nodes)[address]? = heap[address]? := by
  induction nodes generalizing heap with
  | nil => rfl
  | cons node rest ih =>
      simp only [clearNodes]
      rw [ih _ (fun other member => outside other (List.mem_cons_of_mem node member))]
      rw [Array.getElem?_setIfInBounds_ne (outside node (List.mem_cons_self)).2,
        Array.getElem?_setIfInBounds_ne (outside node (List.mem_cons_self)).1]

/-- Published-channel reset preserves every cell outside those marker IDs. -/
private theorem clearChannels_frame (layout : SharedLayout) (heap : Array (Word width))
    {dimension : Nat} (channels : List (Fin dimension)) (address : Nat)
    (outside : ∀ channel ∈ channels, layout.channelMarkerBase + channel.val ≠ address) :
    (clearChannels layout heap channels)[address]? = heap[address]? := by
  induction channels generalizing heap with
  | nil => rfl
  | cons channel rest ih =>
      simp only [clearChannels]
      rw [ih _ (fun other member => outside other (List.mem_cons_of_mem channel member))]
      exact Array.getElem?_setIfInBounds_ne (outside channel List.mem_cons_self)

/-- Direct input reads and guard reads are absorbed by source-local node and
incidence cost; the declared ambient channel count is absent. -/
private theorem local_weight_le (graph : DAG n) (node : Fin graph.nodeCount) :
    localNodeWeight graph node ≤
      2 * (1 + (graph.node node).children.length + (graph.node node).guardLabels.length) := by
  cases gateEq : graph.node node <;>
    simp only [localNodeWeight, gateEq, Gate.children, Gate.guardLabels, Gate.directChannels,
      List.length_nil, List.length_singleton, List.length_cons] <;> omega

private theorem direct_stream_charge (graph : DAG n) (nodes : List (Fin graph.nodeCount)) :
    (nodes.flatMap (fun node => (graph.node node).directChannels)).length ≤ freshWeight graph nodes := by
  induction nodes with
  | nil => simp [freshWeight]
  | cons node rest ih =>
      simp only [freshWeight] at ih
      simp only [List.flatMap_cons, List.length_append, freshWeight, List.map_cons, List.sum_cons]
      have own : (graph.node node).directChannels.length ≤ localNodeWeight graph node := by
        simp only [localNodeWeight]
        omega
      omega

private theorem completed_scope_covered (graph : DAG n) (logical : DFSState graph)
    (channels : List (Channel n))
    (published : ∀ node ∈ logical.completed, ∀ channel ∈ (graph.node node).directChannels,
      channel ∈ channels)
    (node : Fin graph.nodeCount) (member : node ∈ logical.completed)
    (channel : Channel n) (included : channel ∈ graph.scope node) : channel ∈ channels := by
  rw [graph.scope_eq] at included
  rcases Finset.mem_union.mp included with direct | descendant
  · exact published node member channel (List.mem_toFinset.mp direct)
  · obtain ⟨child, childMember, inChild⟩ := Finset.mem_biUnion.mp descendant
    exact completed_scope_covered graph logical channels published (graph.childIndex node child)
      (logical.closed node member child (List.mem_toFinset.mp childMember)) channel inChild
termination_by node.val
decreasing_by exact graph.childIndex_lt node child

/-- Every published channel is charged to an original direct occurrence of a
finished source node. Distinct published labels therefore require only a
cone-local reset even when the ambient declaration is much larger. -/
private theorem produced_channel_charge (graph : DAG n) (logical : DFSState graph)
    (root : Fin graph.nodeCount) (labels : List (Channel n))
    (rootDone : root ∈ logical.completed) (distinct : labels.Nodup)
    (exactScope : ∀ channel, channel ∈ labels ↔ channel ∈ graph.scope root) :
    labels.length ≤ freshWeight graph logical.completed := by
  have included : labels ⊆ logical.completed.flatMap
      (fun node => (graph.node node).directChannels) := by
    intro channel member
    exact completed_scope_covered graph logical
      (logical.completed.flatMap (fun node => (graph.node node).directChannels))
      (fun node nodeMember label labelMember => List.mem_flatMap.mpr ⟨node, nodeMember, labelMember⟩)
      root rootDone channel ((exactScope channel).mp member)
  exact (distinct.length_le_of_subset included).trans (direct_stream_charge graph logical.completed)

/-- Machine capacity covers represented storage and the complete resident
instruction sequence. This includes constant code capacity for an empty DAG. -/
private def sparseWidth (inputWords codeWords : Nat) : Nat :=
  Nat.log 2 (inputWords + codeWords + 1) + 1

private theorem sparse_capacity (inputWords codeWords : Nat) :
    inputWords + codeWords + 1 < 2 ^ sparseWidth inputWords codeWords := by
  exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) _

private theorem sparse_storage_fits (inputWords codeWords : Nat) :
    inputWords < 2 ^ sparseWidth inputWords codeWords := by
  have capacity := sparse_capacity inputWords codeWords
  omega

private theorem sparse_code_fits (inputWords codeWords : Nat) :
    codeWords < 2 ^ sparseWidth inputWords codeWords := by
  have capacity := sparse_capacity inputWords codeWords
  omega

private def warmBackedgeCode (width loop : Nat) : Program width 8 :=
  #[.constant 2 (word width 0), .constant 3 (word width 1),
    .constant 5 (word width (2 ^ width - 1)), .add 4 4 5, .add 6 6 3,
    .branchZero 2 (word width loop)]

private theorem warm_backedge (program : Program width 8) (initial : State width 8)
    (entry loop cursor remaining : Nat)
    (present : ∀ phase : Fin 6, program[entry + phase.val]? =
      (warmBackedgeCode width loop)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 6 < 2 ^ width) (loopFits : loop < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (count : initial.reg 4 = word width (remaining + 1))
    (cursorHeld : initial.reg 6 = word width cursor) :
    ∃ final, Execution program initial final 6 initial.liveWords ∧
      final.heap = initial.heap ∧ final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧ final.reg 7 = initial.reg 7 ∧
      final.pc = word width loop ∧ final.halted = false := by
  let s1 := initial.advance.put 2 (word width 0)
  let s2 := s1.advance.put 3 (word width 1)
  let s3 := s2.advance.put 5 (word width (2 ^ width - 1))
  let s4 := s3.advance.put 4 (word width remaining)
  let s5 := s4.advance.put 6 (word width (cursor + 1))
  let final : State width 8 := { s5.advance with pc := word width loop }
  have capacity : 1 < 2 ^ width := by omega
  have minusFits : 2 ^ width - 1 < 2 ^ width := by omega
  have predecessorSum : remaining + 1 + (2 ^ width - 1) = remaining + 2 ^ width := by omega
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width (entry)).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.advance, State.put, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.advance, State.put, p3]
    rw [show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.advance, State.put, p4]
    rw [show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial (entry + 0) (.constant 2 (word width 0))
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [warmBackedgeCode] using present ⟨0, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.put, State.advance, running,
      count, cursorHeld, word, predecessorSum, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 3 (word width 1))
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [warmBackedgeCode] using present ⟨1, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.put, State.advance, running,
      count, cursorHeld, word, predecessorSum, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.constant 5 (word width (2 ^ width - 1)))
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [warmBackedgeCode] using present ⟨2, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.put, State.advance, running,
      count, cursorHeld, word, predecessorSum, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.add 4 4 5)
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [warmBackedgeCode] using present ⟨3, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.put, State.advance, running,
      count, cursorHeld, word, predecessorSum, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 6 6 3)
      (by simpa only [Nat.add_zero] using p4) (by omega)
      (by simpa [warmBackedgeCode] using present ⟨4, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.put, State.advance, running,
      count, cursorHeld, word, predecessorSum, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t5 : programStep program s5 = some final := by
    rw [fetched program s5 (entry + 5) (.branchZero 2 (word width loop))
      (by simpa only [Nat.add_zero] using p5) (by omega)
      (by simpa [warmBackedgeCode] using present ⟨5, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.put, State.advance, running,
      count, cursorHeld, word, predecessorSum, Nat.mod_eq_of_lt countFits,
      Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity,
      Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width),
      Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, running⟩
  · simpa [final, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put] using trace
  all_goals simp [final, s5, s4, s3, s2, s1, State.advance, State.put]


private theorem warm_handler_section (width base nodeBase temporary : Nat)
    (layout : UniformDAGNode.Layout)
    (phase : Fin (UniformDAGNode.code width (base + 4) layout).length) :
    (warmLedgerCode width base nodeBase temporary layout)[4 + phase.val]? =
      some (widenInstruction ((UniformDAGNode.code width (base + 4) layout).toArray[phase.val])) := by
  have frontSize : (warmDriverPrefix width base).size = 4 := rfl
  have middleSize : (widenProgram (UniformDAGNode.code width (base + 4) layout).toArray).size = 109 := by
    simp only [widenProgram, Array.size_map, List.size_toArray, UniformDAGNode.code_length]
  have phaseBound : phase.val < 109 := by simpa only [UniformDAGNode.code_length] using phase.isLt
  simp only [warmLedgerCode, Array.append_assoc]
  change ((warmDriverPrefix width base) ++
    (widenProgram (UniformDAGNode.code width (base + 4) layout).toArray ++
      (commitResultCode width temporary nodeBase ++ warmBackedgeCode width base)))[4 + phase.val]? = _
  rw [Array.getElem?_append_right (by rw [frontSize]; omega)]
  simp only [frontSize, Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left (by rw [middleSize]; omega)]
  simp only [widenProgram, Array.getElem?_map]
  rw [Array.getElem?_eq_getElem (by simpa only [List.size_toArray] using phase.isLt)]
  rfl

private theorem warm_prefix_section (width base nodeBase temporary : Nat)
    (layout : UniformDAGNode.Layout) (phase : Fin 4) :
    (warmLedgerCode width base nodeBase temporary layout)[phase.val]? =
      (warmDriverPrefix width base)[phase.val]? := by
  simp only [warmLedgerCode, Array.append_assoc]
  change ((warmDriverPrefix width base) ++ _)[phase.val]? = _
  exact Array.getElem?_append_left (by change phase.val < 4; exact phase.isLt)

private theorem warm_commit_section (width base nodeBase temporary : Nat)
    (layout : UniformDAGNode.Layout) (phase : Fin 6) :
    (warmLedgerCode width base nodeBase temporary layout)[113 + phase.val]? =
      (commitResultCode width temporary nodeBase)[phase.val]? := by
  have frontSize : (warmDriverPrefix width base).size = 4 := rfl
  have middleSize : (widenProgram (UniformDAGNode.code width (base + 4) layout).toArray).size = 109 := by
    simp only [widenProgram, Array.size_map, List.size_toArray, UniformDAGNode.code_length]
  simp only [warmLedgerCode, Array.append_assoc]
  change ((warmDriverPrefix width base) ++
    (widenProgram (UniformDAGNode.code width (base + 4) layout).toArray ++
      (commitResultCode width temporary nodeBase ++ warmBackedgeCode width base)))[113 + phase.val]? = _
  rw [Array.getElem?_append_right (by rw [frontSize]; omega)]
  rw [Array.getElem?_append_right (by rw [middleSize]; omega)]
  have index : 113 + phase.val - (warmDriverPrefix width base).size -
      (widenProgram (UniformDAGNode.code width (base + 4) layout).toArray).size = phase.val := by
    rw [frontSize, middleSize]
    omega
  rw [index]
  exact Array.getElem?_append_left (by change phase.val < 6; exact phase.isLt)

private theorem warm_backedge_section (width base nodeBase temporary : Nat)
    (layout : UniformDAGNode.Layout) (phase : Fin 6) :
    (warmLedgerCode width base nodeBase temporary layout)[119 + phase.val]? =
      (warmBackedgeCode width base)[phase.val]? := by
  have frontSize : (warmDriverPrefix width base).size = 4 := rfl
  have middleSize : (widenProgram (UniformDAGNode.code width (base + 4) layout).toArray).size = 109 := by
    simp only [widenProgram, Array.size_map, List.size_toArray, UniformDAGNode.code_length]
  have commitSize : (commitResultCode width temporary nodeBase).size = 6 := rfl
  simp only [warmLedgerCode, Array.append_assoc]
  change ((warmDriverPrefix width base) ++
    (widenProgram (UniformDAGNode.code width (base + 4) layout).toArray ++
      (commitResultCode width temporary nodeBase ++ warmBackedgeCode width base)))[119 + phase.val]? = _
  rw [Array.getElem?_append_right (by rw [frontSize]; omega)]
  rw [Array.getElem?_append_right (by rw [middleSize]; omega)]
  rw [Array.getElem?_append_right (by rw [commitSize]; omega)]
  have index : 119 + phase.val - (warmDriverPrefix width base).size -
      (widenProgram (UniformDAGNode.code width (base + 4) layout).toArray).size -
      (commitResultCode width temporary nodeBase).size = phase.val := by
    rw [frontSize, middleSize, commitSize]
    omega
  rw [index]


/-- One complete fetched warm iteration reads the physical ledger ID, runs
its source-derived handler, stores and releases the actual temporary result,
and returns to the same loop. Correctness concerns only the visited prefix. -/
private theorem warm_iteration (program : Program width 8) (initial : State width 8)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (retained : CachePrefix initial.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : initial.heap.size = layout.storageEnd)
    (dimension : layout.nodeCount = graph.nodeCount) (channelDimension : layout.channels = n)
    (assignment : Assignment n) (values : Fin graph.nodeCount → Bool)
    (channels : ∀ channel : Channel n,
      initial.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)))
    (table : ∀ child : Fin graph.nodeCount,
      initial.heap[layout.nodeValueBase + child.val]? = some (boolWord width (values child)))
    (completed : List (Fin graph.nodeCount)) (slot : Fin completed.length)
    (ordered : Postorder graph completed)
    (correct : WarmPrefixCorrect graph assignment completed slot.val values)
    (base cursor remaining : Nat)
    (physical : ∀ phase : Fin 125, program[base + phase.val]? =
      (warmLedgerCode width base layout.nodeValueBase layout.storageEnd
        (warmLayout caller rows layout))[phase.val]?)
    (position : initial.pc = word width base) (running : initial.halted = false)
    (codeFits : base + 125 < 2 ^ width) (room : initial.heap.size < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < initial.heap.size)
    (ledgerCell : initial.heap[cursor]'cursorBound = word width (completed[slot]).val)
    (count : initial.reg 4 = word width (remaining + 1))
    (cursorHeld : initial.reg 6 = word width cursor) (zero : initial.reg 2 = word width 0) :
    ∃ final ticks peak, Execution program initial final ticks peak ∧
      ticks ≤ 46 * localNodeWeight graph completed[slot] ∧ peak ≤ initial.liveWords + 2 ∧
      final.heap = initial.heap.set (layout.nodeValueBase + (completed[slot]).val)
        (boolWord width (graph.eval assignment completed[slot])) (by
          rw [allocation]
          simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase,
            SharedLayout.nodeValueBase, dimension]
          have := (completed[slot]).isLt
          omega) ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧ final.reg 7 = initial.reg 7 ∧
      final.pc = word width base ∧ final.halted = false := by
  let node := completed[slot]
  have nodeBound : layout.nodeValueBase + node.val < initial.heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase,
      SharedLayout.nodeValueBase, dimension]
    have := node.isLt
    omega
  have offsetFits : 2 * node.val < 2 ^ width := by
    have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    have sourceBelow : layout.sourceEnd < initial.heap.size := by
      rw [allocation]
      simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
      omega
    have sourceWords := sourceSize
    simp only [ForestIndexedOperands.cacheHeap_size] at sourceWords
    omega
  have prefixAt : ∀ phase : Fin 4, program[base + phase.val]? =
      (warmDriverPrefix width base)[phase.val]? := by
    intro phase
    exact (physical ⟨phase.val, by omega⟩).trans
      (warm_prefix_section width base layout.nodeValueBase layout.storageEnd (warmLayout caller rows layout) phase)
  obtain ⟨entered, prefixTrace, enteredHeap, enteredStack, enteredOutput, enteredOffset,
    enteredNode, enteredFrame, enteredPosition, enteredRunning⟩ :=
    warm_driver_prefix program initial base cursor node.val (remaining + 1) prefixAt position running
      codeFits (by omega) offsetFits countFits (by omega) cursorBound ledgerCell cursorHeld count zero
  have enteredLive : entered.liveWords = initial.liveWords := by
    simp only [State.liveWords, enteredHeap, enteredStack, enteredOutput]
  have handlerAt : ∀ phase : Fin (UniformDAGNode.code width (base + 4) (warmLayout caller rows layout)).length,
      program[(base + 4) + phase.val]? = some (widenInstruction
        ((UniformDAGNode.code width (base + 4) (warmLayout caller rows layout)).toArray[phase.val])) := by
    intro phase
    have valid : 4 + phase.val < 125 := by
      have bound : phase.val < 109 := by
        simpa only [UniformDAGNode.code_length] using phase.isLt
      omega
    simpa only [Nat.add_assoc] using (physical ⟨4 + phase.val, valid⟩).trans
      (warm_handler_section width base layout.nodeValueBase layout.storageEnd (warmLayout caller rows layout) phase)
  obtain ⟨allocated, handlerTicks, handlerPeak, handlerTrace, handlerCharge, handlerSpace,
      allocatedHeap, allocatedStack, allocatedOutput, allocatedFrame, allocatedPosition, allocatedRunning⟩ :=
    warm_node_execution program entered caller graph rows roots layout matched heads
      (by simpa only [enteredHeap] using retained) sourceSize
      (by simpa only [enteredHeap] using allocation) dimension channelDimension assignment values
      (by simpa only [enteredHeap] using channels) (by simpa only [enteredHeap] using table)
      node enteredOffset (base + 4) enteredPosition enteredRunning (by omega)
      (by simpa only [enteredHeap] using room) handlerAt
  have semantic : (graph.node node).eval assignment
      (fun child => values (graph.childIndex node child)) = graph.eval assignment node :=
    warm_next_value graph assignment completed slot values ordered correct
  rw [semantic, enteredHeap] at allocatedHeap
  have allocatedLive : allocated.liveWords = initial.liveWords + 1 := by
    simp only [State.liveWords, allocatedHeap, allocatedStack, allocatedOutput, enteredStack,
      enteredOutput, Array.size_push]
    omega
  have temporaryBound : layout.storageEnd < allocated.heap.size := by
    rw [allocatedHeap, Array.size_push, allocation]
    omega
  have temporaryCell : allocated.heap[layout.storageEnd]'temporaryBound =
      boolWord width (graph.eval assignment node) := by
    have cell : allocated.heap[layout.storageEnd]? = some (boolWord width (graph.eval assignment node)) := by
      rw [allocatedHeap, ← allocation]
      exact Array.getElem?_push_size
    rw [Array.getElem?_eq_getElem temporaryBound] at cell
    exact Option.some.inj cell
  have commitAt : ∀ phase : Fin 6, program[(base + 113) + phase.val]? =
      (commitResultCode width layout.storageEnd layout.nodeValueBase)[phase.val]? := by
    intro phase
    simpa only [Nat.add_assoc] using (physical ⟨113 + phase.val, by omega⟩).trans
      (warm_commit_section width base layout.nodeValueBase layout.storageEnd (warmLayout caller rows layout) phase)
  have allocatedNode : allocated.reg 5 = word width node.val :=
    (allocatedFrame 5 (by decide)).trans enteredNode
  obtain ⟨committed, commitTrace, committedHeap, committedStack, committedOutput,
      committedFrame, committedPosition, committedRunning⟩ :=
    commitResult_execution program allocated (base + 113) layout.storageEnd layout.nodeValueBase node.val
      (boolWord width (graph.eval assignment node)) commitAt
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using allocatedPosition) allocatedRunning
      (by omega) (by omega) (by omega) temporaryBound
      (by rw [allocatedHeap, Array.size_push]; omega) allocatedNode temporaryCell
  have actualHeap : committed.heap = initial.heap.set (layout.nodeValueBase + node.val)
      (boolWord width (graph.eval assignment node)) nodeBound := by
    simp only [allocatedHeap] at committedHeap
    exact committedHeap.trans (committed_push initial.heap _ _ nodeBound)
  have committedLive : committed.liveWords = initial.liveWords := by
    simp only [State.liveWords, actualHeap, Array.size_set, committedStack, allocatedStack,
      enteredStack, committedOutput, allocatedOutput, enteredOutput]
  have backAt : ∀ phase : Fin 6, program[(base + 119) + phase.val]? =
      (warmBackedgeCode width base)[phase.val]? := by
    intro phase
    simpa only [Nat.add_assoc] using (physical ⟨119 + phase.val, by omega⟩).trans
      (warm_backedge_section width base layout.nodeValueBase layout.storageEnd (warmLayout caller rows layout) phase)
  have preserved4 : committed.reg 4 = initial.reg 4 :=
    (committedFrame 4 (by decide) (by decide)).trans
      ((allocatedFrame 4 (by decide)).trans (enteredFrame 4 (by decide) (by decide)))
  have preserved6 : committed.reg 6 = initial.reg 6 :=
    (committedFrame 6 (by decide) (by decide)).trans
      ((allocatedFrame 6 (by decide)).trans (enteredFrame 6 (by decide) (by decide)))
  have preserved7 : committed.reg 7 = initial.reg 7 :=
    (committedFrame 7 (by decide) (by decide)).trans
      ((allocatedFrame 7 (by decide)).trans (enteredFrame 7 (by decide) (by decide)))
  obtain ⟨final, backTrace, backHeap, backStack, backOutput, finalCount, finalCursor,
      finalZero, finalOne, finalRoot, finalPosition, finalRunning⟩ :=
    warm_backedge program committed (base + 119) base cursor remaining backAt
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using committedPosition) committedRunning
      (by omega) (by omega) countFits cursorFits (preserved4.trans count) (preserved6.trans cursorHeld)
  have trace := ((prefixTrace.append handlerTrace).append commitTrace).append backTrace
  refine ⟨final, 4 + handlerTicks + 6 + 6,
    max (max (max initial.liveWords handlerPeak) allocated.liveWords) committed.liveWords,
    trace, ?_, ?_, backHeap.trans actualHeap,
    backStack.trans (committedStack.trans (allocatedStack.trans enteredStack)),
    backOutput.trans (committedOutput.trans (allocatedOutput.trans enteredOutput)),
    finalCount, finalCursor, finalZero, finalOne, finalRoot.trans preserved7, finalPosition, finalRunning⟩
  · have charged := handlerCharge
    dsimp only [node] at charged
    simp only [localNodeWeight]
    omega
  · rw [allocatedLive, committedLive]
    rw [enteredLive] at handlerSpace
    omega


/-- The loop carries the original physical ledger, not an abstract trace
successor or a fresh cone list. Count and cursor describe its unvisited suffix. -/
private structure WarmLedgerInvariant (graph : DAG n) (layout : SharedLayout)
    (source : Array (Word width)) (assignment : Assignment n)
    (completed : List (Fin graph.nodeCount)) (visited : Nat)
    (state : State width 8) (values : Fin graph.nodeCount → Bool) : Prop where
  visitedBound : visited ≤ completed.length
  retained : CachePrefix state.heap source
  allocation : state.heap.size = layout.storageEnd
  ledger : CompletedStored layout state.heap graph completed
  table : ∀ node : Fin graph.nodeCount,
    state.heap[layout.nodeValueBase + node.val]? = some (boolWord width (values node))
  channels : ∀ channel : Channel n,
    state.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel))
  correct : WarmPrefixCorrect graph assignment completed visited values
  count : state.reg 4 = word width (completed.length - visited)
  cursor : state.reg 6 = word width (layout.nodeLedgerBase + visited)
  zero : state.reg 2 = word width 0
  one : state.reg 3 = word width 1
  running : state.halted = false

private theorem postorder_length_bound (graph : DAG n)
    (completed : List (Fin graph.nodeCount)) (ordered : Postorder graph completed) :
    completed.length ≤ graph.nodeCount := by
  have injective : Function.Injective (fun slot : Fin completed.length => completed[slot]) := by
    intro first second equal
    apply Fin.ext
    exact ordered.1.getElem_inj_iff.mp (by simpa only [Fin.getElem_fin] using equal)
  have cardinal := Fintype.card_le_of_injective _ injective
  simpa only [Fintype.card_fin] using cardinal


/-- Committing a value writes below every sparse marker/map/ledger cell,
while retaining the original serialized source and ambient assignment. -/
private theorem warm_commit_frame (graph : DAG n) (layout : SharedLayout)
    (heap source : Array (Word width)) (completed : List (Fin graph.nodeCount))
    (node : Fin graph.nodeCount) (value : Word width)
    (dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n)
    (sourceSize : source.size = layout.sourceEnd)
    (bound : layout.nodeValueBase + node.val < heap.size)
    (retained : CachePrefix heap source)
    (stored : CompletedStored layout heap graph completed) :
    CachePrefix (heap.set (layout.nodeValueBase + node.val) value bound) source ∧
      CompletedStored layout (heap.set (layout.nodeValueBase + node.val) value bound)
        graph completed ∧
      (∀ address, address < layout.nodeValueBase ∨ layout.nodeMarkerBase ≤ address →
        (heap.set (layout.nodeValueBase + node.val) value bound)[address]? = heap[address]?) := by
  have nodeBefore : layout.nodeValueBase + node.val < layout.nodeMarkerBase := by
    simp only [SharedLayout.nodeValueBase, SharedLayout.nodeMarkerBase]
    have valid := node.isLt
    have count := dimensions.1
    omega
  have sourceBefore : layout.sourceEnd ≤ layout.nodeValueBase := by
    simp only [SharedLayout.nodeValueBase]
    omega
  have unchanged : ∀ address, address < layout.nodeValueBase ∨ layout.nodeMarkerBase ≤ address →
      (heap.set (layout.nodeValueBase + node.val) value bound)[address]? = heap[address]? := by
    intro address separated
    apply Array.getElem?_set_ne bound
    rcases separated with below | above <;> omega
  refine ⟨?_, ?_, unchanged⟩
  · intro address
    have valid : address.val < layout.sourceEnd := by
      simpa only [sourceSize] using address.isLt
    rw [unchanged address.val (Or.inl (Nat.lt_of_lt_of_le valid sourceBefore))]
    exact retained address
  · constructor
    · rw [unchanged layout.nodeCountSlot (Or.inr (by
        simp only [SharedLayout.nodeCountSlot]; omega))]
      exact stored.count
    · intro position
      rw [unchanged (layout.nodeLedgerBase + position.val) (Or.inr (by
        simp only [SharedLayout.nodeLedgerBase]; omega))]
      exact stored.ledger position
    · intro position
      rw [unchanged (layout.mapBase + (completed[position]).val) (Or.inr (by
        simp only [SharedLayout.mapBase]; omega))]
      exact stored.map position


/-- The physical single-cell commit advances the ledger prefix invariant.
The machine endpoint is the actual iteration endpoint, including its restored
loop registers. -/
private theorem warm_invariant_successor (graph : DAG n) (layout : SharedLayout)
    (source : Array (Word width)) (assignment : Assignment n)
    (completed : List (Fin graph.nodeCount)) (slot : Fin completed.length)
    (initial final : State width 8) (values : Fin graph.nodeCount → Bool)
    (dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n)
    (sourceSize : source.size = layout.sourceEnd) (ordered : Postorder graph completed)
    (invariant : WarmLedgerInvariant graph layout source assignment completed slot.val initial values)
    (nodeBound : layout.nodeValueBase + (completed[slot]).val < initial.heap.size)
    (actualHeap : final.heap = initial.heap.set (layout.nodeValueBase + (completed[slot]).val)
      (boolWord width (graph.eval assignment completed[slot])) nodeBound)
    (count : final.reg 4 = word width (completed.length - (slot.val + 1)))
    (cursor : final.reg 6 = word width (layout.nodeLedgerBase + (slot.val + 1)))
    (zero : final.reg 2 = word width 0) (one : final.reg 3 = word width 1)
    (running : final.halted = false) :
    WarmLedgerInvariant graph layout source assignment completed (slot.val + 1) final
      (Function.update values completed[slot] (graph.eval assignment completed[slot])) ∧
    (∀ address, layout.nodeMarkerBase ≤ address → final.heap[address]? = initial.heap[address]?) := by
  obtain ⟨retained, ledger, frame⟩ := warm_commit_frame graph layout initial.heap source
    completed completed[slot] (boolWord width (graph.eval assignment completed[slot]))
    dimensions sourceSize nodeBound invariant.retained invariant.ledger
  constructor
  · constructor
    · omega
    · simpa only [actualHeap] using retained
    · rw [actualHeap, Array.size_set]
      exact invariant.allocation
    · simpa only [actualHeap] using ledger
    · simpa only [actualHeap] using warm_table_set initial.heap graph layout.nodeValueBase
        values completed[slot] (graph.eval assignment completed[slot]) nodeBound invariant.table
    · intro channel
      rw [actualHeap, frame (layout.channelValueBase + channel.val) (Or.inl (by
        simp only [SharedLayout.channelValueBase, SharedLayout.nodeValueBase]
        have valid := channel.isLt
        have channelCount := dimensions.2
        omega))]
      exact invariant.channels channel
    · exact warm_prefix_update graph assignment completed slot values ordered.1 invariant.correct
    · exact count
    · exact cursor
    · exact zero
    · exact one
    · exact running
  · intro address above
    rw [actualHeap]
    exact frame address (Or.inr above)


/-- Execute the whole unvisited physical postorder ledger on one resident
machine. Every recursive call follows the fetched backedge endpoint. -/
private theorem warm_suffix (program : Program width 8)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n)
    (assignment : Assignment n) (completed : List (Fin graph.nodeCount))
    (ordered : Postorder graph completed) (base : Nat)
    (physical : ∀ phase : Fin 125, program[base + phase.val]? =
      (warmLedgerCode width base layout.nodeValueBase layout.storageEnd
        (warmLayout caller rows layout))[phase.val]?)
    (codeFits : base + 125 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (remaining visited : Nat) (lengthEq : visited + remaining = completed.length)
    (initial : State width 8) (values : Fin graph.nodeCount → Bool)
    (invariant : WarmLedgerInvariant graph layout
      (ForestIndexedOperands.cacheHeap width caller rows roots) assignment completed visited initial values)
    (position : initial.pc = word width base) :
    ∃ (final : State width 8) (ticks peak : Nat) (finalValues : Fin graph.nodeCount → Bool),
      Execution program initial final ticks peak ∧
      ticks ≤ 46 * freshWeight graph (completed.drop visited) + 1 ∧
      peak ≤ initial.liveWords + 2 ∧
      WarmLedgerInvariant graph layout
        (ForestIndexedOperands.cacheHeap width caller rows roots) assignment completed
        completed.length final finalValues ∧
      (∀ address, layout.nodeMarkerBase ≤ address → final.heap[address]? = initial.heap[address]?) ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 7 = initial.reg 7 ∧ final.pc = word width (base + 125) := by
  have listBound := postorder_length_bound graph completed ordered
  have testAt : program[base]? = some (.branchZero 4 (word width (base + 125))) := by
    have original := (physical ⟨0, by decide⟩).trans
      (warm_prefix_section width base layout.nodeValueBase layout.storageEnd (warmLayout caller rows layout)
        ⟨0, by decide⟩)
    simpa [warmDriverPrefix] using original
  induction remaining generalizing visited initial values with
  | zero =>
      have visitedEq : visited = completed.length := by omega
      let final : State width 8 := { initial.advance with pc := word width (base + 125) }
      have count : initial.reg 4 = word width 0 := by
        rw [invariant.count, visitedEq, Nat.sub_self]
      have trace : Execution program initial final 1 initial.liveWords := by
        simpa only [final, ite_true] using streamTest_execution program initial base (base + 125) 0
          testAt position invariant.running (by omega) (by have := storageFits; simp only [SharedLayout.storageEnd] at this; omega) count
      refine ⟨final, 1, initial.liveWords, values, trace, ?_, by omega, ?_, ?_, rfl, rfl, rfl, rfl⟩
      · rw [visitedEq, List.drop_length]
        simp [freshWeight]
      · rw [← visitedEq]
        exact {
          visitedBound := invariant.visitedBound
          retained := invariant.retained
          allocation := invariant.allocation
          ledger := invariant.ledger
          table := invariant.table
          channels := invariant.channels
          correct := invariant.correct
          count := invariant.count
          cursor := invariant.cursor
          zero := invariant.zero
          one := invariant.one
          running := invariant.running }
      · intro address above
        rfl
  | succ remaining ih =>
      have visitedBound : visited < completed.length := by omega
      let slot : Fin completed.length := ⟨visited, visitedBound⟩
      let node := completed[slot]
      let cursor := layout.nodeLedgerBase + visited
      obtain ⟨cursorBound, ledgerCell⟩ := Array.getElem?_eq_some_iff.mp (invariant.ledger.ledger slot)
      have countFits : remaining + 1 < 2 ^ width := by
        have count := dimensions.1
        simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
          SharedLayout.nodeMarkerBase] at storageFits
        omega
      have cursorFits : cursor + 1 < 2 ^ width := by
        have count := dimensions.1
        dsimp only [cursor]
        simp only [SharedLayout.nodeLedgerBase, SharedLayout.storageEnd,
          SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase] at storageFits ⊢
        omega
      have countHeld : initial.reg 4 = word width (remaining + 1) := by
        rw [invariant.count, show completed.length - visited = remaining + 1 by omega]
      obtain ⟨next, iterationTicks, iterationPeak, iterationTrace, iterationCharge,
        iterationSpace, nextHeap, nextStack, nextOutput, nextCount, nextCursor,
        nextZero, nextOne, nextRoot, nextPC, nextRunning⟩ :=
        warm_iteration program initial caller graph rows roots layout matched heads invariant.retained
          sourceSize invariant.allocation dimensions.1 dimensions.2 assignment values invariant.channels
          invariant.table completed slot ordered invariant.correct base cursor remaining physical position
          invariant.running codeFits (by rw [invariant.allocation]; exact storageFits) cursorFits countFits
          cursorBound ledgerCell countHeld invariant.cursor invariant.zero
      let nextValues := Function.update values node (graph.eval assignment node)
      have nodeBound : layout.nodeValueBase + node.val < initial.heap.size := by
        rw [invariant.allocation]
        simp only [SharedLayout.nodeValueBase, SharedLayout.storageEnd,
          SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
        have count := dimensions.1
        have valid := node.isLt
        omega
      have successor := warm_invariant_successor graph layout _ assignment completed slot initial next values
        dimensions sourceSize ordered invariant nodeBound nextHeap
        (by simpa only [slot, Fin.val_mk, show completed.length - (visited + 1) = remaining by omega] using nextCount)
        (by simpa only [slot, Fin.val_mk, cursor, Nat.add_assoc] using nextCursor)
        nextZero nextOne nextRunning
      obtain ⟨final, tailTicks, tailPeak, finalValues, tailTrace, tailCharge, tailSpace,
        finalInvariant, tailFrame, finalStack, finalOutput, finalRoot, finalPC⟩ :=
        ih (visited := visited + 1) (initial := next) (values := nextValues)
          (by omega) successor.1 nextPC
      have nextLive : next.liveWords = initial.liveWords := by
        simp only [State.liveWords, nextHeap, Array.size_set, nextStack, nextOutput]
      have suffixEq : completed.drop visited = node :: completed.drop (visited + 1) := by
        simpa only [node, slot, Fin.getElem_fin] using List.drop_eq_getElem_cons visitedBound
      have weightEq : freshWeight graph (completed.drop visited) =
          localNodeWeight graph node + freshWeight graph (completed.drop (visited + 1)) := by
        rw [suffixEq]
        rfl
      refine ⟨final, iterationTicks + tailTicks, max iterationPeak tailPeak, finalValues,
        iterationTrace.append tailTrace, ?_, ?_, finalInvariant, ?_,
        finalStack.trans nextStack, finalOutput.trans nextOutput, finalRoot.trans nextRoot, finalPC⟩
      · change iterationTicks ≤ 46 * localNodeWeight graph node at iterationCharge
        calc
          iterationTicks + tailTicks ≤ 46 * localNodeWeight graph node +
              (46 * freshWeight graph (completed.drop (visited + 1)) + 1) :=
            Nat.add_le_add iterationCharge tailCharge
          _ = 46 * freshWeight graph (completed.drop visited) + 1 := by
            rw [weightEq]
            omega
      · rw [nextLive] at tailSpace
        omega
      · intro address above
        exact (tailFrame address above).trans (successor.2 address above)


/-- Evaluate the complete physically produced original-ID postorder ledger.
Ambient memo cells may contain Boolean values left by other queries. Every
selected child is proved to belong to the already evaluated prefix. -/
theorem warm_ledger_execution (program : Program width 8)
    (caller : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (layout : SharedLayout) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n)
    (assignment : Assignment n) (completed : List (Fin graph.nodeCount))
    (ordered : Postorder graph completed) (base : Nat)
    (physical : ∀ phase : Fin 125, program[base + phase.val]? =
      (warmLedgerCode width base layout.nodeValueBase layout.storageEnd
        (warmLayout caller rows layout))[phase.val]?)
    (codeFits : base + 125 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (initial : State width 8) (values : Fin graph.nodeCount → Bool)
    (retained : CachePrefix initial.heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (allocation : initial.heap.size = layout.storageEnd)
    (ledger : CompletedStored layout initial.heap graph completed)
    (table : ∀ node : Fin graph.nodeCount,
      initial.heap[layout.nodeValueBase + node.val]? = some (boolWord width (values node)))
    (channels : ∀ channel : Channel n,
      initial.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)))
    (position : initial.pc = word width base) (running : initial.halted = false)
    (count : initial.reg 4 = word width completed.length)
    (cursor : initial.reg 6 = word width layout.nodeLedgerBase)
    (zero : initial.reg 2 = word width 0) (one : initial.reg 3 = word width 1) :
    ∃ (final : State width 8) (ticks peak : Nat) (finalValues : Fin graph.nodeCount → Bool),
      Execution program initial final ticks peak ∧
      ticks ≤ 46 * freshWeight graph completed + 1 ∧ peak ≤ initial.liveWords + 2 ∧
      (∀ node ∈ completed, finalValues node = graph.eval assignment node) ∧
      (∀ node : Fin graph.nodeCount,
        final.heap[layout.nodeValueBase + node.val]? = some (boolWord width (finalValues node))) ∧
      (∀ channel : Channel n,
        final.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel))) ∧
      CachePrefix final.heap (ForestIndexedOperands.cacheHeap width caller rows roots) ∧
      CompletedStored layout final.heap graph completed ∧ final.heap.size = layout.storageEnd ∧
      (∀ address, layout.nodeMarkerBase ≤ address → final.heap[address]? = initial.heap[address]?) ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧ final.reg 7 = initial.reg 7 ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧
      final.pc = word width (base + 125) ∧ final.halted = false := by
  have invariant : WarmLedgerInvariant graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      assignment completed 0 initial values := {
    visitedBound := Nat.zero_le _
    retained := retained
    allocation := allocation
    ledger := ledger
    table := table
    channels := channels
    correct := by intro node member; simp only [List.take_zero, List.not_mem_nil] at member
    count := by simpa only [Nat.sub_zero] using count
    cursor := by simpa only [Nat.add_zero] using cursor
    zero := zero
    one := one
    running := running }
  obtain ⟨final, ticks, peak, finalValues, trace, charge, space, finalInvariant, frame,
    stack, output, root, pc⟩ := warm_suffix program caller graph rows roots layout matched heads
      sourceSize dimensions assignment completed ordered base physical codeFits storageFits
      completed.length 0 (by omega) initial values invariant position
  refine ⟨final, ticks, peak, finalValues, trace, ?_, space, ?_, finalInvariant.table, finalInvariant.channels,
    finalInvariant.retained, finalInvariant.ledger, finalInvariant.allocation, frame,
    stack, output, root, finalInvariant.zero, finalInvariant.one, pc, finalInvariant.running⟩
  · simpa only [List.drop_zero] using charge
  · intro node member
    exact finalInvariant.correct node (by simpa only [List.take_length] using member)


/-- One fetched channel-reset iteration clears its actual published ID. -/
private theorem reset_channel_iteration (program : Program width 8) (initial : State width 8)
    (base markerBase cursor channel remaining : Nat)
    (present : ∀ phase : Fin 9, program[base + phase.val]? =
      (resetChannelsCode width base markerBase)[phase.val]?)
    (position : initial.pc = word width base) (running : initial.halted = false)
    (codeFits : base + 9 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (markerFits : markerBase + channel < 2 ^ width)
    (countHeld : initial.reg 4 = word width (remaining + 1))
    (cursorHeld : initial.reg 6 = word width cursor)
    (zero : initial.reg 2 = word width 0) (one : initial.reg 3 = word width 1)
    (cursorBound : cursor < initial.heap.size)
    (sourceCell : initial.heap[cursor]'cursorBound = word width channel)
    (markerBound : markerBase + channel < initial.heap.size) :
    ∃ final, Execution program initial final 9 initial.liveWords ∧
      final.heap = initial.heap.set (markerBase + channel) (word width 0) markerBound ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧ final.reg 7 = initial.reg 7 ∧
      final.pc = word width base ∧ final.halted = false := by
  let s1 : State width 8 := initial.advance
  let s2 : State width 8 := s1.advance.put 0 (word width channel)
  let s3 : State width 8 := s2.advance.put 1 (word width markerBase)
  let s4 : State width 8 := s3.advance.put 1 (word width (markerBase + channel))
  let s5 : State width 8 := { s4.advance with heap := initial.heap.set (markerBase + channel) (word width 0) markerBound }
  let s6 : State width 8 := s5.advance.put 5 (word width (2 ^ width - 1))
  let s7 : State width 8 := s6.advance.put 4 (word width remaining)
  let s8 : State width 8 := s7.advance.put 6 (word width (cursor + 1))
  let final : State width 8 := { s8.advance with pc := word width base }
  have channelFits : channel < 2 ^ width := by omega
  have markerBaseFits : markerBase < 2 ^ width := by omega
  have capacity : 1 < 2 ^ width := by omega
  have minusFits : 2 ^ width - 1 < 2 ^ width := by omega
  have predecessorSum : remaining + 1 + (2 ^ width - 1) = remaining + 2 ^ width := by omega
  have p1 : s1.pc = word width (base + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width (base)).val = base from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (base + 2) := by
    simp only [s2, State.advance, State.put, p1]
    rw [show (word width (base + 1)).val = base + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (base + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (base + 2)).val = base + 2 from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (base + 4) := by
    simp only [s4, State.advance, State.put, p3]
    rw [show (word width (base + 3)).val = base + 3 from Nat.mod_eq_of_lt (by omega)]
  have p5 : s5.pc = word width (base + 5) := by
    simp only [s5, State.advance, State.put, p4]
    rw [show (word width (base + 4)).val = base + 4 from Nat.mod_eq_of_lt (by omega)]
  have p6 : s6.pc = word width (base + 6) := by
    simp only [s6, State.advance, State.put, p5]
    rw [show (word width (base + 5)).val = base + 5 from Nat.mod_eq_of_lt (by omega)]
  have p7 : s7.pc = word width (base + 7) := by
    simp only [s7, State.advance, State.put, p6]
    rw [show (word width (base + 6)).val = base + 6 from Nat.mod_eq_of_lt (by omega)]
  have p8 : s8.pc = word width (base + 8) := by
    simp only [s8, State.advance, State.put, p7]
    rw [show (word width (base + 7)).val = base + 7 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial (base + 0) (.branchZero 4 (word width (base + 9)))
      (by simpa only [Nat.add_zero] using position)
      (by omega) (by simpa [resetChannelsCode] using present ⟨0, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.load 0 6)
      (by simpa only [Nat.add_zero] using p1)
      (by omega) (by simpa [resetChannelsCode] using present ⟨1, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.constant 1 (word width markerBase))
      (by simpa only [Nat.add_zero] using p2)
      (by omega) (by simpa [resetChannelsCode] using present ⟨2, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.add 1 1 0)
      (by simpa only [Nat.add_zero] using p3)
      (by omega) (by simpa [resetChannelsCode] using present ⟨3, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.store 1 2)
      (by simpa only [Nat.add_zero] using p4)
      (by omega) (by simpa [resetChannelsCode] using present ⟨4, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.constant 5 (word width (2 ^ width - 1)))
      (by simpa only [Nat.add_zero] using p5)
      (by omega) (by simpa [resetChannelsCode] using present ⟨5, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.add 4 4 5)
      (by simpa only [Nat.add_zero] using p6)
      (by omega) (by simpa [resetChannelsCode] using present ⟨6, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (base + 7) (.add 6 6 3)
      (by simpa only [Nat.add_zero] using p7)
      (by omega) (by simpa [resetChannelsCode] using present ⟨7, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have t8 : programStep program s8 = some final := by
    rw [fetched program s8 (base + 8) (.branchZero 2 (word width base))
      (by simpa only [Nat.add_zero] using p8)
      (by omega) (by simpa [resetChannelsCode] using present ⟨8, by decide⟩)]
    simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, countHeld, cursorHeld, zero, one, word, sourceCell, cursorBound, markerBound, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), Nat.mod_eq_of_lt channelFits, Nat.mod_eq_of_lt markerBaseFits, Nat.mod_eq_of_lt markerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt capacity, predecessorSum, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width)]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl (p := program) final)))))))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa [final, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords,
      State.advance, State.put, Array.size_set, Nat.max_self] using trace
  all_goals simp [final, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running]


@[simp] private theorem clearNodes_size (layout : SharedLayout) (heap : Array (Word width))
    {dimension : Nat} (nodes : List (Fin dimension)) :
    (clearNodes layout heap nodes).size = heap.size := by
  induction nodes generalizing heap with
  | nil => rfl
  | cons node rest ih => simp only [clearNodes, ih, Array.size_setIfInBounds]

/-- Clear the actual unvisited node ledger, with one final fetched empty test.
The physical ledger survives every marker and map store. -/
theorem reset_node_suffix (program : Program width 8) (layout : SharedLayout)
    (base : Nat)
    (present : ∀ phase : Fin 12, program[base + phase.val]? =
      (resetNodesCode width base layout.nodeMarkerBase layout.mapBase)[phase.val]?)
    (codeFits : base + 12 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (nodes : List (Fin layout.nodeCount)) (initial : State width 8) (cursor : Nat)
    (allocation : initial.heap.size = layout.storageEnd)
    (stored : ScopeStored initial.heap cursor nodes)
    (cursorLower : layout.nodeLedgerBase ≤ cursor)
    (cursorEnd : cursor + nodes.length ≤ layout.storageEnd)
    (countFits : nodes.length < 2 ^ width)
    (position : initial.pc = word width base) (running : initial.halted = false)
    (count : initial.reg 4 = word width nodes.length) (heldCursor : initial.reg 6 = word width cursor)
    (zero : initial.reg 2 = word width 0) (one : initial.reg 3 = word width 1) :
    ∃ final, Execution program initial final (12 * nodes.length + 1) initial.liveWords ∧
      final.heap = clearNodes layout initial.heap nodes ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width 0 ∧ final.reg 6 = word width (cursor + nodes.length) ∧
      final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧ final.reg 7 = initial.reg 7 ∧
      final.pc = word width (base + 12) ∧ final.halted = false := by
  have testAt : program[base]? = some (.branchZero 4 (word width (base + 12))) := by
    simpa [resetNodesCode] using present ⟨0, by decide⟩
  induction nodes generalizing initial cursor with
  | nil =>
      let final : State width 8 := { initial.advance with pc := word width (base + 12) }
      refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, running⟩
      · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, final, ite_true] using
          streamTest_execution program initial base (base + 12) 0 testAt position running
            (by omega) countFits count
      · exact count
      · simpa only [final, State.advance, List.length_nil, Nat.add_zero] using heldCursor
  | cons node rest ih =>
      have markerBound : layout.nodeMarkerBase + node.val < initial.heap.size := by
        rw [allocation]
        simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
        have valid := node.isLt
        omega
      have mapBound : layout.mapBase + node.val < initial.heap.size := by
        rw [allocation]
        simp only [SharedLayout.mapBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
        have valid := node.isLt
        omega
      obtain ⟨cursorBound, sourceCell⟩ := Array.getElem?_eq_some_iff.mp (stored ⟨0, by simp⟩)
      simp only [Nat.add_zero, Fin.getElem_fin, List.getElem_cons_zero] at cursorBound sourceCell
      obtain ⟨next, iteration, nextHeap, nextStack, nextOutput, nextCount, nextCursor,
        nextZero, nextOne, nextRoot, nextPC, nextRunning⟩ :=
        reset_node_iteration program initial base layout.nodeMarkerBase layout.mapBase cursor node.val
          rest.length present position running codeFits (by simpa only [List.length_cons] using countFits)
          (by simp only [List.length_cons] at cursorEnd; omega)
          (Nat.lt_trans markerBound (by rw [allocation]; exact storageFits))
          (Nat.lt_trans mapBound (by rw [allocation]; exact storageFits))
          (by simpa only [List.length_cons] using count) heldCursor zero one cursorBound sourceCell
          markerBound mapBound
      have nextAllocation : next.heap.size = layout.storageEnd := by
        rw [nextHeap, Array.size_set, Array.size_set]
        exact allocation
      have nextStored : ScopeStored next.heap (cursor + 1) rest := by
        have tail := scope_tail initial.heap cursor node rest stored
        intro slot
        have markerBelow : layout.nodeMarkerBase + node.val < layout.nodeLedgerBase := by
          simp only [SharedLayout.nodeLedgerBase]
          have valid := node.isLt
          omega
        have mapBelow : layout.mapBase + node.val < layout.nodeLedgerBase := by
          simp only [SharedLayout.mapBase, SharedLayout.nodeLedgerBase]
          have valid := node.isLt
          omega
        rw [nextHeap, Array.getElem?_set_ne (by simpa only [Array.size_set] using mapBound) (by omega),
          Array.getElem?_set_ne markerBound (by omega)]
        exact tail slot
      obtain ⟨final, tailTrace, finalHeap, finalStack, finalOutput, finalCount, finalCursor,
        finalZero, finalOne, finalRoot, finalPC, finalRunning⟩ :=
        ih next (cursor + 1) nextAllocation nextStored (by omega)
          (by simp only [List.length_cons] at cursorEnd; omega) (by simp only [List.length_cons] at countFits; omega)
          nextPC nextRunning nextCount nextCursor (nextZero.trans zero) (nextOne.trans one)
      have nextLive : next.liveWords = initial.liveWords := by
        simp only [State.liveWords, nextHeap, Array.size_set, nextStack, nextOutput]
      have semantic : next.heap = (initial.heap.setIfInBounds (layout.nodeMarkerBase + node.val)
          (word width 0)).setIfInBounds (layout.mapBase + node.val) (word width 0) := by
        rw [nextHeap]
        simp only [Array.setIfInBounds_def, markerBound, dite_eq_left, Array.size_set, mapBound]
      refine ⟨final, ?_, ?_, finalStack.trans nextStack, finalOutput.trans nextOutput,
        finalCount, ?_, finalZero.trans nextZero, finalOne.trans nextOne,
        finalRoot.trans nextRoot, finalPC, finalRunning⟩
      · have trace := iteration.append tailTrace
        simpa only [nextLive, Nat.max_self, List.length_cons, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace
      · rw [finalHeap, semantic]
        rfl
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalCursor


@[simp] private theorem clearChannels_size (layout : SharedLayout) (heap : Array (Word width))
    {dimension : Nat} (nodes : List (Fin dimension)) :
    (clearChannels layout heap nodes).size = heap.size := by
  induction nodes generalizing heap with
  | nil => rfl
  | cons node rest ih => simp only [clearChannels, ih, Array.size_setIfInBounds]

/-- Clear the actual unvisited channel ledger, with one final fetched empty test.
The physical ledger survives every marker store. -/
theorem reset_channel_suffix (program : Program width 8) (layout : SharedLayout)
    (base : Nat)
    (present : ∀ phase : Fin 9, program[base + phase.val]? =
      (resetChannelsCode width base layout.channelMarkerBase)[phase.val]?)
    (codeFits : base + 9 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (nodes : List (Fin layout.channels)) (initial : State width 8) (cursor : Nat)
    (allocation : initial.heap.size = layout.storageEnd)
    (stored : ScopeStored initial.heap cursor nodes)
    (cursorLower : layout.channelLedgerBase ≤ cursor)
    (cursorEnd : cursor + nodes.length ≤ layout.storageEnd)
    (countFits : nodes.length < 2 ^ width)
    (position : initial.pc = word width base) (running : initial.halted = false)
    (count : initial.reg 4 = word width nodes.length) (heldCursor : initial.reg 6 = word width cursor)
    (zero : initial.reg 2 = word width 0) (one : initial.reg 3 = word width 1) :
    ∃ final, Execution program initial final (9 * nodes.length + 1) initial.liveWords ∧
      final.heap = clearChannels layout initial.heap nodes ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width 0 ∧ final.reg 6 = word width (cursor + nodes.length) ∧
      final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧ final.reg 7 = initial.reg 7 ∧
      final.pc = word width (base + 9) ∧ final.halted = false := by
  have testAt : program[base]? = some (.branchZero 4 (word width (base + 9))) := by
    simpa [resetChannelsCode] using present ⟨0, by decide⟩
  induction nodes generalizing initial cursor with
  | nil =>
      let final : State width 8 := { initial.advance with pc := word width (base + 9) }
      refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, running⟩
      · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, final, ite_true] using
          streamTest_execution program initial base (base + 9) 0 testAt position running
            (by omega) countFits count
      · exact count
      · simpa only [final, State.advance, List.length_nil, Nat.add_zero] using heldCursor
  | cons node rest ih =>
      have markerBound : layout.channelMarkerBase + node.val < initial.heap.size := by
        rw [allocation]
        simp only [SharedLayout.channelMarkerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
        have valid := node.isLt
        omega
      obtain ⟨cursorBound, sourceCell⟩ := Array.getElem?_eq_some_iff.mp (stored ⟨0, by simp⟩)
      simp only [Nat.add_zero, Fin.getElem_fin, List.getElem_cons_zero] at cursorBound sourceCell
      obtain ⟨next, iteration, nextHeap, nextStack, nextOutput, nextCount, nextCursor,
        nextZero, nextOne, nextRoot, nextPC, nextRunning⟩ :=
        reset_channel_iteration program initial base layout.channelMarkerBase cursor node.val
          rest.length present position running codeFits (by simpa only [List.length_cons] using countFits)
          (by simp only [List.length_cons] at cursorEnd; omega)
          (Nat.lt_trans markerBound (by rw [allocation]; exact storageFits))
          (by simpa only [List.length_cons] using count) heldCursor zero one cursorBound sourceCell
          markerBound
      have nextAllocation : next.heap.size = layout.storageEnd := by
        rw [nextHeap, Array.size_set]
        exact allocation
      have nextStored : ScopeStored next.heap (cursor + 1) rest := by
        have tail := scope_tail initial.heap cursor node rest stored
        intro slot
        have markerBelow : layout.channelMarkerBase + node.val < layout.channelLedgerBase := by
          simp only [SharedLayout.channelMarkerBase, SharedLayout.channelLedgerBase]
          have valid := node.isLt
          omega
        rw [nextHeap, Array.getElem?_set_ne markerBound (by omega)]
        exact tail slot
      obtain ⟨final, tailTrace, finalHeap, finalStack, finalOutput, finalCount, finalCursor,
        finalZero, finalOne, finalRoot, finalPC, finalRunning⟩ :=
        ih next (cursor + 1) nextAllocation nextStored (by omega)
          (by simp only [List.length_cons] at cursorEnd; omega) (by simp only [List.length_cons] at countFits; omega)
          nextPC nextRunning nextCount nextCursor (nextZero.trans zero) (nextOne.trans one)
      have nextLive : next.liveWords = initial.liveWords := by
        simp only [State.liveWords, nextHeap, Array.size_set, nextStack, nextOutput]
      have semantic : next.heap = initial.heap.setIfInBounds (layout.channelMarkerBase + node.val)
          (word width 0) := by
        rw [nextHeap]
        simp only [Array.setIfInBounds_def, markerBound, dite_eq_left]
      refine ⟨final, ?_, ?_, finalStack.trans nextStack, finalOutput.trans nextOutput,
        finalCount, ?_, finalZero.trans nextZero, finalOne.trans nextOne,
        finalRoot.trans nextRoot, finalPC, finalRunning⟩
      · have trace := iteration.append tailTrace
        simpa only [nextLive, Nat.max_self, List.length_cons, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace
      · rw [finalHeap, semantic]
        rfl
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalCursor


/-- Empty both produced ledgers by four fetched instructions. -/
theorem clear_counts_execution (program : Program width 8) (initial : State width 8)
    (entry nodeCountSlot channelCountSlot : Nat)
    (physical : ∀ phase : Fin 4, program[entry + phase.val]? =
      (clearLedgerCountsCode width nodeCountSlot channelCountSlot)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 4 < 2 ^ width) (room : initial.heap.size < 2 ^ width)
    (nodeBound : nodeCountSlot < initial.heap.size)
    (channelBound : channelCountSlot < initial.heap.size)
    (zero : initial.reg 2 = word width 0) :
    ∃ final, Execution program initial final 4 initial.liveWords ∧
      final.heap = (initial.heap.set nodeCountSlot (word width 0) nodeBound).set
        channelCountSlot (word width 0) (by simpa only [Array.size_set] using channelBound) ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      (∀ register : Fin 8, register ≠ 1 → final.reg register = initial.reg register) ∧
      final.pc = word width (entry + 4) ∧ final.halted = false := by
  let s1 := initial.advance.put 1 (word width nodeCountSlot)
  let s2 : State width 8 := { s1.advance with heap := initial.heap.set nodeCountSlot (word width 0) nodeBound }
  let s3 := s2.advance.put 1 (word width channelCountSlot)
  let final : State width 8 := { s3.advance with heap := (initial.heap.set nodeCountSlot (word width 0) nodeBound).set channelCountSlot (word width 0) (by simpa only [Array.size_set] using channelBound) }
  have nodeFits := Nat.lt_trans nodeBound room
  have channelFits := Nat.lt_trans channelBound room
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial entry (.constant 1 (word width nodeCountSlot)) position (by omega)
      (by simpa [clearLedgerCountsCode, Nat.add_zero] using physical ⟨0, by decide⟩)]
    simp [step, s1, running]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.store 1 2) p1 (by omega)
      (by simpa [clearLedgerCountsCode] using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running, zero, word,
      Nat.mod_eq_of_lt nodeFits, nodeBound]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.constant 1 (word width channelCountSlot)) p2 (by omega)
      (by simpa [clearLedgerCountsCode] using physical ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running]
  have t3 : programStep program s3 = some final := by
    rw [fetched program s3 (entry + 3) (.store 1 2) p3 (by omega)
      (by simpa [clearLedgerCountsCode] using physical ⟨3, by decide⟩)]
    simp [step, final, s3, s2, s1, State.advance, State.put, running, zero, word,
      Nat.mod_eq_of_lt channelFits, channelBound]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.refl (p := program) final))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, running⟩
  · simpa [final, s3, s2, s1, State.liveWords, State.advance, State.put,
      Array.size_set, Nat.max_self] using trace
  · intro register different
    simp [final, s3, s2, s1, State.advance, State.put, different]
  · change word width (s3.pc.val + 1) = word width (entry + 4)
    rw [p3, show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]


/-- Repeated clearing is harmless: a node marker is zero after reset whenever
it was already zero or its original ID occurs in the actual touched ledger. -/
private theorem clearNodes_marker_zero (layout : SharedLayout) (heap : Array (Word width))
    {dimension : Nat} (nodes : List (Fin dimension)) (target : Fin dimension)
    (dimensionEq : layout.nodeCount = dimension) (allocation : heap.size = layout.storageEnd)
    (eligible : heap[layout.nodeMarkerBase + target.val]? = some (word width 0) ∨ target ∈ nodes) :
    (clearNodes layout heap nodes)[layout.nodeMarkerBase + target.val]? = some (word width 0) := by
  induction nodes generalizing heap with
  | nil =>
      rcases eligible with zero | impossible
      · exact zero
      · simp only [List.not_mem_nil] at impossible
  | cons node rest ih =>
      let next := (heap.setIfInBounds (layout.nodeMarkerBase + node.val) (word width 0)).setIfInBounds
        (layout.mapBase + node.val) (word width 0)
      have nextSize : next.size = layout.storageEnd := by
        simp only [next, Array.size_setIfInBounds, allocation]
      have mapDifferent : layout.mapBase + node.val ≠ layout.nodeMarkerBase + target.val := by
        simp only [SharedLayout.mapBase]
        have valid := target.isLt
        omega
      have nextEligible : next[layout.nodeMarkerBase + target.val]? = some (word width 0) ∨ target ∈ rest := by
        by_cases same : node = target
        · subst node
          left
          rw [show next = (heap.setIfInBounds (layout.nodeMarkerBase + target.val) (word width 0)).setIfInBounds
            (layout.mapBase + target.val) (word width 0) from rfl,
            Array.getElem?_setIfInBounds_ne mapDifferent]
          apply Array.getElem?_setIfInBounds_self_of_lt
          rw [allocation]
          simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
          have valid := target.isLt
          omega
        · rcases eligible with zero | member
          · left
            have markerDifferent : layout.nodeMarkerBase + node.val ≠ layout.nodeMarkerBase + target.val := by
              intro equal
              apply same
              apply Fin.ext
              omega
            rw [show next = (heap.setIfInBounds (layout.nodeMarkerBase + node.val) (word width 0)).setIfInBounds
              (layout.mapBase + node.val) (word width 0) from rfl,
              Array.getElem?_setIfInBounds_ne mapDifferent, Array.getElem?_setIfInBounds_ne markerDifferent]
            exact zero
          · right
            rcases List.mem_cons.mp member with equal | tail
            · exact False.elim (same equal.symm)
            · exact tail
      exact ih next nextSize nextEligible

/-- Every ambient node marker is zero after resetting the produced ledger.
The untouched sparse map and ledger payload cells need not equal their cold
values, because empty counts make those payloads inactive. -/
private theorem clearNodes_all_flags_zero (graph : DAG n) (layout : SharedLayout)
    (heap : Array (Word width)) (completed : List (Fin graph.nodeCount))
    (dimensionEq : layout.nodeCount = graph.nodeCount) (allocation : heap.size = layout.storageEnd)
    (flags : ∀ node : Fin graph.nodeCount, heap[layout.nodeMarkerBase + node.val]? =
      some (word width (if node ∈ completed then 1 else 0))) :
    ∀ node : Fin graph.nodeCount,
      (clearNodes layout heap completed)[layout.nodeMarkerBase + node.val]? = some (word width 0) := by
  intro node
  apply clearNodes_marker_zero layout heap completed node dimensionEq allocation
  by_cases member : node ∈ completed
  · exact Or.inr member
  · exact Or.inl (by simpa only [member, ite_false] using flags node)


private theorem clearChannels_marker_zero (layout : SharedLayout) (heap : Array (Word width))
    {dimension : Nat} (channels : List (Fin dimension)) (target : Fin dimension)
    (dimensionEq : layout.channels = dimension) (allocation : heap.size = layout.storageEnd)
    (eligible : heap[layout.channelMarkerBase + target.val]? = some (word width 0) ∨ target ∈ channels) :
    (clearChannels layout heap channels)[layout.channelMarkerBase + target.val]? = some (word width 0) := by
  induction channels generalizing heap with
  | nil =>
      rcases eligible with zero | impossible
      · exact zero
      · simp only [List.not_mem_nil] at impossible
  | cons channel rest ih =>
      let next := heap.setIfInBounds (layout.channelMarkerBase + channel.val) (word width 0)
      have nextSize : next.size = layout.storageEnd := by
        simp only [next, Array.size_setIfInBounds, allocation]
      have nextEligible : next[layout.channelMarkerBase + target.val]? = some (word width 0) ∨ target ∈ rest := by
        by_cases same : channel = target
        · subst channel
          left
          apply Array.getElem?_setIfInBounds_self_of_lt
          rw [allocation]
          simp only [SharedLayout.channelMarkerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
          have valid := target.isLt
          omega
        · rcases eligible with zero | member
          · left
            have different : layout.channelMarkerBase + channel.val ≠ layout.channelMarkerBase + target.val := by
              intro equal
              apply same
              apply Fin.ext
              omega
            rw [show next = heap.setIfInBounds (layout.channelMarkerBase + channel.val) (word width 0) from rfl,
              Array.getElem?_setIfInBounds_ne different]
            exact zero
          · right
            rcases List.mem_cons.mp member with equal | tail
            · exact False.elim (same equal.symm)
            · exact tail
      exact ih next nextSize nextEligible

private theorem clearChannels_all_flags_zero (layout : SharedLayout) (heap : Array (Word width))
    (channels : List (Channel n)) (dimensionEq : layout.channels = n)
    (allocation : heap.size = layout.storageEnd)
    (flags : ∀ channel : Channel n, heap[layout.channelMarkerBase + channel.val]? =
      some (word width (if channel ∈ channels then 1 else 0))) :
    ∀ channel : Channel n,
      (clearChannels layout heap channels)[layout.channelMarkerBase + channel.val]? = some (word width 0) := by
  intro channel
  apply clearChannels_marker_zero layout heap channels channel dimensionEq allocation
  by_cases member : channel ∈ channels
  · exact Or.inr member
  · exact Or.inl (by simpa only [member, ite_false] using flags channel)


def emptyDFS (graph : DAG n) : DFSState graph where
  completed := []
  active := []
  completedUnique := List.nodup_nil
  activeUnique := List.nodup_nil
  separate := by simp
  closed := by intro node member; simp only [List.not_mem_nil] at member

def resetHeap (layout : SharedLayout) (heap : Array (Word width))
    (nodes : List (Fin dimension)) (channels : List (Channel n)) : Array (Word width) :=
  ((clearChannels layout (clearNodes layout heap nodes) channels).setIfInBounds
    layout.nodeCountSlot (word width 0)).setIfInBounds layout.channelCountSlot (word width 0)

@[simp] private theorem resetHeap_size (layout : SharedLayout) (heap : Array (Word width))
    (nodes : List (Fin dimension)) (channels : List (Channel n)) :
    (resetHeap layout heap nodes channels).size = heap.size := by
  simp only [resetHeap, Array.size_setIfInBounds, clearChannels_size, clearNodes_size]

private theorem resetHeap_lower_frame (layout : SharedLayout) (heap : Array (Word width))
    (nodes : List (Fin dimension)) (channels : List (Channel n))
    (address : Nat) (below : address < layout.nodeMarkerBase) :
    (resetHeap layout heap nodes channels)[address]? = heap[address]? := by
  simp only [resetHeap]
  rw [Array.getElem?_setIfInBounds_ne (by
    simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot]
    omega), Array.getElem?_setIfInBounds_ne (by
      simp only [SharedLayout.nodeCountSlot]
      omega)]
  rw [clearChannels_frame layout _ channels address (by
    intro channel member; simp only [SharedLayout.channelMarkerBase]; omega)]
  exact clearNodes_frame layout heap nodes address (by
    intro node member
    constructor
    · omega
    · simp only [SharedLayout.mapBase]; omega)

/-- The actual touched stores establish the empty marker invariant; inactive
map and ledger payload cells are intentionally unconstrained. -/
private theorem resetHeap_flags (graph : DAG n) (layout : SharedLayout)
    (heap : Array (Word width)) (nodes : List (Fin graph.nodeCount)) (channels : List (Channel n))
    (dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n)
    (allocation : heap.size = layout.storageEnd)
    (nodeFlags : ∀ node : Fin graph.nodeCount, heap[layout.nodeMarkerBase + node.val]? =
      some (word width (if node ∈ nodes then 1 else 0)))
    (channelFlags : ∀ channel : Channel n, heap[layout.channelMarkerBase + channel.val]? =
      some (word width (if channel ∈ channels then 1 else 0))) :
    (∀ node : Fin graph.nodeCount,
      (resetHeap layout heap nodes channels)[layout.nodeMarkerBase + node.val]? = some (word width 0)) ∧
    (∀ channel : Channel n,
      (resetHeap layout heap nodes channels)[layout.channelMarkerBase + channel.val]? = some (word width 0)) := by
  have nodeZero := clearNodes_all_flags_zero graph layout heap nodes dimensions.1 allocation nodeFlags
  have channelRetained : ∀ channel : Channel n,
      (clearNodes layout heap nodes)[layout.channelMarkerBase + channel.val]? = heap[layout.channelMarkerBase + channel.val]? := by
    intro channel
    apply clearNodes_frame
    intro node member
    have nodeBound := node.isLt
    have channelBound := channel.isLt
    simp only [SharedLayout.channelMarkerBase, SharedLayout.mapBase]
    constructor <;> omega
  have channelZero := clearChannels_all_flags_zero layout (clearNodes layout heap nodes) channels
    dimensions.2 (by simp only [clearNodes_size]; exact allocation)
    (fun channel => (channelRetained channel).trans (channelFlags channel))
  constructor
  · intro node
    simp only [resetHeap]
    rw [Array.getElem?_setIfInBounds_ne (by
      simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot]; have valid := node.isLt; omega),
      Array.getElem?_setIfInBounds_ne (by
        simp only [SharedLayout.nodeCountSlot]; have valid := node.isLt; omega)]
    rw [clearChannels_frame layout _ channels (layout.nodeMarkerBase + node.val) (by
      intro channel member
      simp only [SharedLayout.channelMarkerBase]
      have valid := node.isLt
      omega)]
    exact nodeZero node
  · intro channel
    simp only [resetHeap]
    rw [Array.getElem?_setIfInBounds_ne (by
      simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot, SharedLayout.channelMarkerBase]
      have valid := channel.isLt; omega),
      Array.getElem?_setIfInBounds_ne (by
        simp only [SharedLayout.nodeCountSlot, SharedLayout.channelMarkerBase]
        have valid := channel.isLt; omega)]
    exact channelZero channel

theorem reset_empty_stored (graph : DAG n) (layout : SharedLayout)
    (source heap : Array (Word width)) (nodes : List (Fin graph.nodeCount)) (channels : List (Channel n))
    (dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n)
    (sourceSize : source.size = layout.sourceEnd) (allocation : heap.size = layout.storageEnd)
    (retained : CachePrefix heap source)
    (nodeFlags : ∀ node : Fin graph.nodeCount, heap[layout.nodeMarkerBase + node.val]? =
      some (word width (if node ∈ nodes then 1 else 0)))
    (channelFlags : ∀ channel : Channel n, heap[layout.channelMarkerBase + channel.val]? =
      some (word width (if channel ∈ channels then 1 else 0)))
    (final : State width 8) (actualHeap : final.heap = resetHeap layout heap nodes channels)
    (depth : final.reg 7 = word width 0) (zero : final.reg 2 = word width 0)
    (one : final.reg 3 = word width 1) :
    TraversalStored graph layout source final (emptyDFS graph) [] := by
  have flags := resetHeap_flags graph layout heap nodes channels dimensions allocation nodeFlags channelFlags
  have middleSize : (clearChannels layout (clearNodes layout heap nodes) channels).size = layout.storageEnd := by
    simp only [clearChannels_size, clearNodes_size, allocation]
  have nodeBound : layout.nodeCountSlot < (clearChannels layout (clearNodes layout heap nodes) channels).size := by
    rw [middleSize]
    simp only [SharedLayout.storageEnd]
    omega
  have channelBound : layout.channelCountSlot <
      ((clearChannels layout (clearNodes layout heap nodes) channels).setIfInBounds layout.nodeCountSlot (word width 0)).size := by
    rw [Array.size_setIfInBounds, middleSize]
    simp only [SharedLayout.channelCountSlot, SharedLayout.storageEnd]
    omega
  constructor
  · intro address
    rw [actualHeap, resetHeap_lower_frame layout heap nodes channels address.val (by
      have valid : address.val < layout.sourceEnd := by
        simpa only [sourceSize] using address.isLt
      exact Nat.lt_of_lt_of_le valid (by simp only [SharedLayout.nodeMarkerBase]; omega))]
    exact retained address
  · exact dimensions.1
  · exact dimensions.2
  · rw [actualHeap, resetHeap_size]
    exact allocation
  · constructor
    · rw [actualHeap]
      simp only [resetHeap, Array.getElem?_setIfInBounds_ne (show layout.channelCountSlot ≠ layout.nodeCountSlot by
        simp only [SharedLayout.channelCountSlot]; omega),
        Array.getElem?_setIfInBounds_self_of_lt nodeBound, emptyDFS, List.length_nil]
    · intro position
      exact Fin.elim0 position
    · intro position
      exact Fin.elim0 position
  · constructor
    · rw [actualHeap]
      simpa only [resetHeap, List.length_nil] using Array.getElem?_setIfInBounds_self_of_lt channelBound
    · intro position
      exact Fin.elim0 position
    · intro channel
      rw [actualHeap]
      simpa only [List.not_mem_nil, ite_false] using flags.2 channel
  · exact List.nodup_nil
  · intro node
    rw [actualHeap]
    simpa only [emptyDFS, List.not_mem_nil, or_false, ite_false] using flags.1 node
  · intro node member
    simp only [emptyDFS, List.not_mem_nil] at member
  · simpa only [emptyDFS, List.length_nil] using depth
  · exact zero
  · exact one


/-- Casting the finite original IDs to the equal physical marker dimension
preserves exactly the IDs read/stored by reset; it constructs no new stream. -/
private theorem clearNodes_map_cast (layout : SharedLayout) (heap : Array (Word width))
    {first second : Nat} (equal : first = second) (nodes : List (Fin first)) :
    clearNodes layout heap (nodes.map (Fin.cast equal)) = clearNodes layout heap nodes := by
  induction nodes generalizing heap with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.map_cons, clearNodes, Fin.val_cast]
      exact ih _

private theorem clearChannels_map_cast (layout : SharedLayout) (heap : Array (Word width))
    {first second : Nat} (equal : first = second) (channels : List (Fin first)) :
    clearChannels layout heap (channels.map (Fin.cast equal)) = clearChannels layout heap channels := by
  induction channels generalizing heap with
  | nil => rfl
  | cons channel rest ih =>
      simp only [List.map_cons, clearChannels, Fin.val_cast]
      exact ih _

private theorem completed_ledger_scope (graph : DAG n) (layout : SharedLayout)
    (heap : Array (Word width)) (completed : List (Fin graph.nodeCount))
    (dimension : layout.nodeCount = graph.nodeCount)
    (stored : CompletedStored layout heap graph completed) :
    ScopeStored heap layout.nodeLedgerBase (completed.map (Fin.cast dimension.symm)) := by
  intro slot
  have valid : slot.val < completed.length := by simpa only [List.length_map] using slot.isLt
  have original := stored.ledger ⟨slot.val, valid⟩
  simpa only [Fin.getElem_fin, List.getElem_map, Fin.val_cast] using original

private theorem published_ledger_scope (layout : SharedLayout)
    (heap : Array (Word width)) (channels : List (Channel n))
    (dimension : layout.channels = n) (stored : ChannelsStored layout heap channels) :
    ScopeStored heap layout.channelLedgerBase (channels.map (Fin.cast dimension.symm)) := by
  intro slot
  have valid : slot.val < channels.length := by simpa only [List.length_map] using slot.isLt
  have original := stored.ledger ⟨slot.val, valid⟩
  simpa only [Fin.getElem_fin, List.getElem_map, Fin.val_cast] using original


/-- A physical instruction slice of the one resident eight-register program. -/
def CodeAt8 (program : Program width 8) (base : Nat) (code : Program width 8) : Prop :=
  ∀ phase : Fin code.size, program[base + phase.val]? = code[phase.val]?

private theorem codeAt8_prefix (program : Program width 8) (base : Nat)
    (first rest : Program width 8) (physical : CodeAt8 program base (first ++ rest)) :
    CodeAt8 program base first := by
  intro phase
  have cell := physical ⟨phase.val, by simp only [Array.size_append]; have valid := phase.isLt; omega⟩
  exact cell.trans (Array.getElem?_append_left phase.isLt)

private theorem codeAt8_suffix (program : Program width 8) (base : Nat)
    (first rest : Program width 8) (physical : CodeAt8 program base (first ++ rest)) :
    CodeAt8 program (base + first.size) rest := by
  intro phase
  have cell := physical ⟨first.size + phase.val, by
    simp only [Array.size_append]; have valid := phase.isLt; omega⟩
  have right : (first ++ rest)[first.size + phase.val]? = rest[phase.val]? := by
    rw [Array.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
  simpa only [Nat.add_assoc] using cell.trans right


private def rootPrefixCode (width done dfsEntry : Nat) : Program width 8 := #[
  .branchZero 4 (word width done), .push 4, .constant 4 (word width 1), .branchZero 2 (word width dfsEntry)]

private theorem root_prefix_execution (program : Program width 8) (initial : State width 8)
    (entry done dfsEntry remaining : Nat)
    (physical : ∀ phase : Fin 4, program[entry + phase.val]? = (rootPrefixCode width done dfsEntry)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 4 < 2 ^ width) (dfsFits : dfsEntry < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (count : initial.reg 4 = word width (remaining + 1)) (zero : initial.reg 2 = word width 0) :
    ∃ final, Execution program initial final 4 (initial.liveWords + 1) ∧
      final.heap = initial.heap ∧ final.stack = word width (remaining + 1) :: initial.stack ∧
      final.output = initial.output ∧ final.reg 4 = word width 1 ∧
      (∀ register : Fin 8, register ≠ 4 → final.reg register = initial.reg register) ∧
      final.pc = word width dfsEntry ∧ final.halted = false := by
  let s1 := initial.advance
  let s2 : State width 8 := { s1.advance with stack := word width (remaining + 1) :: initial.stack }
  let s3 := s2.advance.put 4 (word width 1)
  let final : State width 8 := { s3.advance with pc := word width dfsEntry }
  have capacity : 1 < 2 ^ width := by omega
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial entry (.branchZero 4 (word width done)) position (by omega)
      (by simpa [rootPrefixCode] using physical ⟨0, by decide⟩)]
    simp [step, s1, running, count, word, Nat.mod_eq_of_lt countFits]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.push 4) p1 (by omega)
      (by simpa [rootPrefixCode] using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, running, count]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.constant 4 (word width 1)) p2 (by omega)
      (by simpa [rootPrefixCode] using physical ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running]
  have t3 : programStep program s3 = some final := by
    rw [fetched program s3 (entry + 3) (.branchZero 2 (word width dfsEntry)) p3 (by omega)
      (by simpa [rootPrefixCode] using physical ⟨3, by decide⟩)]
    simp [step, final, s3, s2, s1, State.advance, State.put, running, zero, word]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.refl (p := program) final))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, rfl, running⟩
  · simpa [final, s3, s2, s1, State.liveWords, State.advance, State.put,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.max_self, show max initial.liveWords (initial.liveWords + 1) = initial.liveWords + 1 by omega] using trace
  · simp [final, s3, State.advance, State.put]
  · intro register different
    simp [final, s3, s2, s1, State.advance, State.put, different]


private def postQueryCode (width ledgerBase countSlot : Nat) : Program width 8 := #[
  .push 6, .constant 1 (word width (2 ^ width - 1)), .add 7 6 1, .load 7 7,
  .constant 6 (word width ledgerBase), .constant 1 (word width countSlot), .load 4 1]

/-- Save the actual advanced root cursor, reread its original source ID, and
load the physical produced-ledger count before warm evaluation. -/
private theorem post_query_execution (program : Program width 8) (initial : State width 8)
    (entry rootCursor rootID ledgerBase countSlot count : Nat)
    (physical : ∀ phase : Fin 7, program[entry + phase.val]? = (postQueryCode width ledgerBase countSlot)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 7 < 2 ^ width) (room : initial.heap.size < 2 ^ width)
    (cursorFits : rootCursor + 1 < 2 ^ width) (ledgerFits : ledgerBase < 2 ^ width)
    (countFits : count < 2 ^ width) (rootFits : rootID < 2 ^ width)
    (cursor : initial.reg 6 = word width (rootCursor + 1))
    (rootBound : rootCursor < initial.heap.size) (countBound : countSlot < initial.heap.size)
    (rootCell : initial.heap[rootCursor]'rootBound = word width rootID)
    (countCell : initial.heap[countSlot]'countBound = word width count) :
    ∃ final, Execution program initial final 7 (initial.liveWords + 1) ∧
      final.heap = initial.heap ∧ final.stack = word width (rootCursor + 1) :: initial.stack ∧
      final.output = initial.output ∧ final.reg 7 = word width rootID ∧
      final.reg 6 = word width ledgerBase ∧ final.reg 4 = word width count ∧
      final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧
      final.pc = word width (entry + 7) ∧ final.halted = false := by
  let s1 : State width 8 := { initial.advance with stack := word width (rootCursor + 1) :: initial.stack }
  let s2 := s1.advance.put 1 (word width (2 ^ width - 1))
  let s3 := s2.advance.put 7 (word width rootCursor)
  let s4 := s3.advance.put 7 (word width rootID)
  let s5 := s4.advance.put 6 (word width ledgerBase)
  let s6 := s5.advance.put 1 (word width countSlot)
  let final := s6.advance.put 4 (word width count)
  have countSlotFits := Nat.lt_trans countBound room
  have cursorSum : rootCursor + 1 + (2 ^ width - 1) = rootCursor + 2 ^ width := by omega
  have capacity : 1 < 2 ^ width := by omega
  have minusFits : 2 ^ width - 1 < 2 ^ width := by omega
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width (entry)).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.advance, State.put, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.advance, State.put, p3]
    rw [show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.advance, State.put, p4]
    rw [show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have p6 : s6.pc = word width (entry + 6) := by
    simp only [s6, State.advance, State.put, p5]
    rw [show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial (entry + 0) (.push 6)
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [postQueryCode] using physical ⟨0, by decide⟩)]
    simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, cursor, rootCell, countCell, rootBound, countBound, Nat.mod_eq_of_lt countSlotFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt (by omega : rootCursor < 2 ^ width), Nat.mod_eq_of_lt rootFits, Nat.mod_eq_of_lt ledgerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, cursorSum, word]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 1 (word width (2 ^ width - 1)))
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [postQueryCode] using physical ⟨1, by decide⟩)]
    simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, cursor, rootCell, countCell, rootBound, countBound, Nat.mod_eq_of_lt countSlotFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt (by omega : rootCursor < 2 ^ width), Nat.mod_eq_of_lt rootFits, Nat.mod_eq_of_lt ledgerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, cursorSum, word]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 7 6 1)
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [postQueryCode] using physical ⟨2, by decide⟩)]
    simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, cursor, rootCell, countCell, rootBound, countBound, Nat.mod_eq_of_lt countSlotFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt (by omega : rootCursor < 2 ^ width), Nat.mod_eq_of_lt rootFits, Nat.mod_eq_of_lt ledgerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, cursorSum, word]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.load 7 7)
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [postQueryCode] using physical ⟨3, by decide⟩)]
    simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, cursor, rootCell, countCell, rootBound, countBound, Nat.mod_eq_of_lt countSlotFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt (by omega : rootCursor < 2 ^ width), Nat.mod_eq_of_lt rootFits, Nat.mod_eq_of_lt ledgerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, cursorSum, word]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.constant 6 (word width ledgerBase))
      (by simpa only [Nat.add_zero] using p4) (by omega)
      (by simpa [postQueryCode] using physical ⟨4, by decide⟩)]
    simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, cursor, rootCell, countCell, rootBound, countBound, Nat.mod_eq_of_lt countSlotFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt (by omega : rootCursor < 2 ^ width), Nat.mod_eq_of_lt rootFits, Nat.mod_eq_of_lt ledgerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, cursorSum, word]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.constant 1 (word width countSlot))
      (by simpa only [Nat.add_zero] using p5) (by omega)
      (by simpa [postQueryCode] using physical ⟨5, by decide⟩)]
    simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, cursor, rootCell, countCell, rootBound, countBound, Nat.mod_eq_of_lt countSlotFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt (by omega : rootCursor < 2 ^ width), Nat.mod_eq_of_lt rootFits, Nat.mod_eq_of_lt ledgerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, cursorSum, word]
  have t6 : programStep program s6 = some final := by
    rw [fetched program s6 (entry + 6) (.load 4 1)
      (by simpa only [Nat.add_zero] using p6) (by omega)
      (by simpa [postQueryCode] using physical ⟨6, by decide⟩)]
    simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put, step, running, cursor, rootCell, countCell, rootBound, countBound, Nat.mod_eq_of_lt countSlotFits, Nat.mod_eq_of_lt cursorFits, Nat.mod_eq_of_lt (by omega : rootCursor < 2 ^ width), Nat.mod_eq_of_lt rootFits, Nat.mod_eq_of_lt ledgerFits, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, cursorSum, word]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.refl (p := program) final)))))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, running⟩
  · simpa [final, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.max_self, show max initial.liveWords (initial.liveWords + 1) = initial.liveWords + 1 by omega] using trace
  · simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · change word width (s6.pc.val + 1) = word width (entry + 7)
    rw [p6, show (word width (entry + 6)).val = entry + 6 from Nat.mod_eq_of_lt (by omega)]


private def ledgerSetupCode (width ledgerBase countSlot : Nat) : Program width 8 := #[
  .constant 6 (word width ledgerBase), .constant 1 (word width countSlot), .load 4 1]

private theorem ledger_setup_execution (program : Program width 8) (initial : State width 8)
    (entry ledgerBase countSlot count : Nat)
    (physical : ∀ phase : Fin 3, program[entry + phase.val]? = (ledgerSetupCode width ledgerBase countSlot)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 3 < 2 ^ width) (room : initial.heap.size < 2 ^ width)
    (countBound : countSlot < initial.heap.size)
    (cell : initial.heap[countSlot]'countBound = word width count) :
    ∃ final, Execution program initial final 3 initial.liveWords ∧
      final.heap = initial.heap ∧ final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 6 = word width ledgerBase ∧ final.reg 4 = word width count ∧
      (∀ register : Fin 8, register ≠ 1 → register ≠ 4 → register ≠ 6 → final.reg register = initial.reg register) ∧
      final.pc = word width (entry + 3) ∧ final.halted = false := by
  let s1 := initial.advance.put 6 (word width ledgerBase)
  let s2 := s1.advance.put 1 (word width countSlot)
  let final := s2.advance.put 4 (word width count)
  have slotFits := Nat.lt_trans countBound room
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.advance, State.put, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial entry (.constant 6 (word width ledgerBase)) position (by omega)
      (by simpa [ledgerSetupCode] using physical ⟨0, by decide⟩)]
    simp [step, s1, running]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 1 (word width countSlot)) p1 (by omega)
      (by simpa [ledgerSetupCode] using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running]
  have t2 : programStep program s2 = some final := by
    rw [fetched program s2 (entry + 2) (.load 4 1) p2 (by omega)
      (by simpa [ledgerSetupCode] using physical ⟨2, by decide⟩)]
    simp [step, final, s2, s1, State.advance, State.put, running, word,
      Nat.mod_eq_of_lt slotFits, countBound, cell]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl (p := program) final)))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, running⟩
  · simpa [final, s2, s1, State.liveWords, State.advance, State.put, Nat.max_self] using trace
  · simp [final, s2, s1, State.advance, State.put]
  · simp [final, s2, s1, State.advance, State.put]
  · intro register notOne notFour notSix
    simp [final, s2, s1, State.advance, State.put, notOne, notFour, notSix]
  · simp only [final, State.advance, State.put, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]


private def memoEmitCode (width nodeBase : Nat) : Program width 8 := #[
  .constant 1 (word width nodeBase), .add 1 1 7, .load 0 1, .emit 0]

/-- The answer is fetched from the evaluated original root's resident slot
and emitted by a real instruction. The machine output list records newest
words first, so the outer driver preserves source order chronologically. -/
private theorem memo_emit_execution (program : Program width 8) (initial : State width 8)
    (entry nodeBase rootID : Nat) (value : Word width)
    (physical : ∀ phase : Fin 4, program[entry + phase.val]? = (memoEmitCode width nodeBase)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 4 < 2 ^ width) (room : initial.heap.size < 2 ^ width)
    (nodeBound : nodeBase + rootID < initial.heap.size)
    (root : initial.reg 7 = word width rootID)
    (cell : initial.heap[nodeBase + rootID]'nodeBound = value) :
    ∃ final, Execution program initial final 4 (initial.liveWords + 1) ∧
      final.heap = initial.heap ∧ final.stack = initial.stack ∧ final.output = value :: initial.output ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = initial.reg register) ∧
      final.pc = word width (entry + 4) ∧ final.halted = false := by
  let s1 := initial.advance.put 1 (word width nodeBase)
  let s2 := s1.advance.put 1 (word width (nodeBase + rootID))
  let s3 := s2.advance.put 0 value
  let final : State width 8 := { s3.advance with output := value :: initial.output }
  have addressFits := Nat.lt_trans nodeBound room
  have baseFits : nodeBase < 2 ^ width := by omega
  have rootFits : rootID < 2 ^ width := by omega
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.advance, State.put, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial entry (.constant 1 (word width nodeBase)) position (by omega)
      (by simpa [memoEmitCode] using physical ⟨0, by decide⟩)]
    simp [step, s1, running]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.add 1 1 7) p1 (by omega)
      (by simpa [memoEmitCode] using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running, root, word,
      Nat.mod_eq_of_lt baseFits, Nat.mod_eq_of_lt rootFits, Nat.mod_eq_of_lt addressFits]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 0 1) p2 (by omega)
      (by simpa [memoEmitCode] using physical ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running, word,
      Nat.mod_eq_of_lt addressFits, nodeBound, cell]
  have t3 : programStep program s3 = some final := by
    rw [fetched program s3 (entry + 3) (.emit 0) p3 (by omega)
      (by simpa [memoEmitCode] using physical ⟨3, by decide⟩)]
    simp [step, final, s3, s2, s1, State.advance, State.put, running]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.refl (p := program) final))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, running⟩
  · simpa [final, s3, s2, s1, State.liveWords, State.advance, State.put,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.max_self, show max initial.liveWords (initial.liveWords + 1) = initial.liveWords + 1 by omega] using trace
  · intro register notZero notOne
    simp [final, s3, s2, s1, State.advance, State.put, notZero, notOne]
  · change word width (s3.pc.val + 1) = word width (entry + 4)
    rw [p3, show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]


private def rootBackedgeCode (width loop : Nat) : Program width 8 := #[
  .constant 7 (word width 0), .pop 6, .pop 4, .constant 5 (word width (2 ^ width - 1)),
  .add 4 4 5, .branchZero 2 (word width loop)]

/-- Restore the saved actual outer count/cursor after evaluation, reset and
emission. No caller-side state replacement occurs between root queries. -/
private theorem root_backedge_execution (program : Program width 8) (initial : State width 8)
    (entry loop nextCursor remaining : Nat) (suffix : List (Word width))
    (physical : ∀ phase : Fin 6, program[entry + phase.val]? = (rootBackedgeCode width loop)[phase.val]?)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + 6 < 2 ^ width) (loopFits : loop < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (stack : initial.stack = word width nextCursor :: word width (remaining + 1) :: suffix)
    (zero : initial.reg 2 = word width 0) :
    ∃ final, Execution program initial final 6 initial.liveWords ∧
      final.heap = initial.heap ∧ final.stack = suffix ∧ final.output = initial.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width nextCursor ∧
      final.reg 7 = word width 0 ∧ final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧
      final.pc = word width loop ∧ final.halted = false := by
  let s1 := initial.advance.put 7 (word width 0)
  let s2 : State width 8 := { (s1.advance.put 6 (word width nextCursor)) with
    stack := word width (remaining + 1) :: suffix }
  let s3 : State width 8 := { (s2.advance.put 4 (word width (remaining + 1))) with stack := suffix }
  let s4 := s3.advance.put 5 (word width (2 ^ width - 1))
  let s5 := s4.advance.put 4 (word width remaining)
  let final : State width 8 := { s5.advance with pc := word width loop }
  have capacity : 1 < 2 ^ width := by omega
  have minusFits : 2 ^ width - 1 < 2 ^ width := by omega
  have predecessorSum : remaining + 1 + (2 ^ width - 1) = remaining + 2 ^ width := by omega
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width (entry)).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.advance, State.put, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.advance, State.put, p3]
    rw [show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.advance, State.put, p4]
    rw [show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial (entry + 0) (.constant 7 (word width 0))
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [rootBackedgeCode] using physical ⟨0, by decide⟩)]
    simp [final, s5, s4, s3, s2, s1, State.advance, State.put, step, running, stack, zero, word, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width), Nat.mod_eq_of_lt capacity, predecessorSum]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.pop 6)
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [rootBackedgeCode] using physical ⟨1, by decide⟩)]
    simp [final, s5, s4, s3, s2, s1, State.advance, State.put, step, running, stack, zero, word, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width), Nat.mod_eq_of_lt capacity, predecessorSum]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.pop 4)
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [rootBackedgeCode] using physical ⟨2, by decide⟩)]
    simp [final, s5, s4, s3, s2, s1, State.advance, State.put, step, running, stack, zero, word, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width), Nat.mod_eq_of_lt capacity, predecessorSum]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.constant 5 (word width (2 ^ width - 1)))
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [rootBackedgeCode] using physical ⟨3, by decide⟩)]
    simp [final, s5, s4, s3, s2, s1, State.advance, State.put, step, running, stack, zero, word, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width), Nat.mod_eq_of_lt capacity, predecessorSum]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 4 4 5)
      (by simpa only [Nat.add_zero] using p4) (by omega)
      (by simpa [rootBackedgeCode] using physical ⟨4, by decide⟩)]
    simp [final, s5, s4, s3, s2, s1, State.advance, State.put, step, running, stack, zero, word, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width), Nat.mod_eq_of_lt capacity, predecessorSum]
  have t5 : programStep program s5 = some final := by
    rw [fetched program s5 (entry + 5) (.branchZero 2 (word width loop))
      (by simpa only [Nat.add_zero] using p5) (by omega)
      (by simpa [rootBackedgeCode] using physical ⟨5, by decide⟩)]
    simp [final, s5, s4, s3, s2, s1, State.advance, State.put, step, running, stack, zero, word, Nat.mod_eq_of_lt countFits, Nat.mod_eq_of_lt minusFits, Nat.mod_eq_of_lt (by omega : remaining < 2 ^ width), Nat.mod_eq_of_lt capacity, predecessorSum]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl (p := program) final))))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, running⟩
  · have live2 : s2.liveWords ≤ initial.liveWords := by
      simp [s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live3 : s3.liveWords ≤ initial.liveWords := by
      simp [s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live32 : s3.liveWords ≤ s2.liveWords := by
      simp [s3, s2, s1, State.liveWords, State.advance, State.put] <;> omega
    have same1 : s1.liveWords = initial.liveWords := rfl
    have same4 : s4.liveWords = s3.liveWords := rfl
    have same5 : s5.liveWords = s3.liveWords := rfl
    have sameFinal : final.liveWords = s3.liveWords := rfl
    simpa only [same1, same4, same5, sameFinal, Nat.max_self,
      Nat.max_eq_left live32, Nat.max_eq_left live2, Nat.max_eq_left live3] using trace
  all_goals simp [final, s5, s4, s3, s2, s1, State.advance, State.put]


private theorem root_empty_halt (program : Program width 8) (initial : State width 8)
    (entry done : Nat)
    (testAt : program[entry]? = some (.branchZero 4 (word width done)))
    (haltAt : program[done]? = some .halt)
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (entryFits : entry < 2 ^ width) (doneFits : done + 1 < 2 ^ width)
    (zeroCount : initial.reg 4 = word width 0) :
    ∃ final, Execution program initial final 2 initial.liveWords ∧
      final.heap = initial.heap ∧ final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg = initial.reg ∧ final.pc = word width (done + 1) ∧ final.halted = true := by
  let tested : State width 8 := { initial.advance with pc := word width done }
  let final : State width 8 := { tested.advance with halted := true }
  have test : Execution program initial tested 1 initial.liveWords := by
    simpa only [tested, ite_true] using streamTest_execution program initial entry done 0 testAt
      position running entryFits (by omega) zeroCount
  have halt : programStep program tested = some final := by
    rw [fetched program tested done .halt rfl (by omega) haltAt]
    simp [step, tested, final, State.advance, running]
  have last : Execution program tested final 1 initial.liveWords := by
    have trace := Execution.cons halt (Execution.refl (p := program) final)
    simpa only [tested, final, State.advance, State.liveWords, Nat.max_self] using trace
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simpa only [Nat.reduceAdd, Nat.max_self] using test.append last
  · simp only [final, tested, State.advance]
    rw [show (word width done).val = done from Nat.mod_eq_of_lt (by omega)]


/-- The resident driver consumes the original serialized root sequence. Its
DFS setup prefix is bypassed on each query so the live root cursor is never
reset. The next cursor and remaining outer count are stored on the charged
stack while the physical produced ledgers are evaluated and cleared. -/
def orderedRootCode (width base : Nat) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (layout : SharedLayout) : Program width 8 :=
  let dfsBase := base + 4
  let warmBase := base + 131
  let nodeResetBase := base + 259
  let channelResetBase := base + 274
  #[.branchZero 4 (word width (base + 297)), .push 4,
    .constant 4 (word width 1), .branchZero 2 (word width (dfsBase + 5))] ++
  dfsFromCache width caller rows roots dfsBase layout ++
  #[.push 6, .constant 1 (word width (2 ^ width - 1)), .add 7 6 1, .load 7 7,
    .constant 6 (word width layout.nodeLedgerBase), .constant 1 (word width layout.nodeCountSlot), .load 4 1] ++
  warmLedgerCode width warmBase layout.nodeValueBase layout.storageEnd (warmLayout caller rows layout) ++
  #[.constant 6 (word width layout.nodeLedgerBase), .constant 1 (word width layout.nodeCountSlot), .load 4 1] ++
  resetNodesCode width nodeResetBase layout.nodeMarkerBase layout.mapBase ++
  #[.constant 6 (word width layout.channelLedgerBase), .constant 1 (word width layout.channelCountSlot), .load 4 1] ++
  resetChannelsCode width channelResetBase layout.channelMarkerBase ++
  clearLedgerCountsCode width layout.nodeCountSlot layout.channelCountSlot ++
  #[.constant 1 (word width layout.nodeValueBase), .add 1 1 7, .load 0 1, .emit 0] ++
  #[.constant 7 (word width 0), .pop 6, .pop 4, .constant 5 (word width (2 ^ width - 1)),
    .add 4 4 5, .branchZero 2 (word width base)] ++ #[.halt]

theorem orderedRootCode_size (width base : Nat) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (layout : SharedLayout) :
    (orderedRootCode width base caller rows roots layout).size = 298 := by
  simp only [orderedRootCode, Array.size_append, dfsFromCache, dfsProgram_size, warmLedgerCode_size,
    resetNodesCode_size, resetChannelsCode_size, clearLedgerCountsCode_size]
  rfl


def sparseLayout (width : Nat) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) : SharedLayout where
  sourceEnd := (ForestIndexedOperands.cacheHeap width
    (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots).size
  nodeCount := graph.nodeCount
  channels := n

def scratchWords (graph : DAG n) : Nat := 2 * n + 3 * graph.nodeCount + 2

def coldReuseCode (width : Nat) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n) : Program width 8 :=
  let caller := UniformDAGRun.packetHeaderHeap width n rows roots
  let layout := sparseLayout width graph rows roots
  let low := UniformDAGResources.program width n rows roots assignment ++
    (Initialize.code (word width 0) (scratchWords graph)).toArray
  let outer := low.size + 5
  let rootStart := caller.size + 6 * rows.length +
    (ForestIndexedOperands.rowChildren rows).length + (ForestIndexedOperands.rowGuards rows).length
  widenProgram low ++
  #[.constant 2 (word width 0), .constant 3 (word width 1), .constant 7 (word width 0),
    .constant 4 (word width roots.length), .constant 6 (word width rootStart)] ++
  orderedRootCode width outer caller rows roots layout

def reuseWidth (graph : DAG n) : Nat := Nat.log 2 (graph.countedSize + 1) + 13

private theorem reuse_capacity (graph : DAG n) :
    4096 * (graph.countedSize + 1) < 2 ^ reuseWidth graph := by
  have basic := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (graph.countedSize + 1)
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 4096)
  have identity : 4096 * 2 ^ (Nat.log 2 (graph.countedSize + 1) + 1) =
      2 ^ reuseWidth graph := by
    simp only [reuseWidth, Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  simpa only [identity] using scaled

private theorem coldReuseCode_size (width : Nat) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n) :
    (coldReuseCode width graph rows roots assignment).size = 466 + 6 * n + 6 * graph.nodeCount := by
  simp only [coldReuseCode, Array.size_append, widenProgram, Array.size_map,
    UniformDAGResources.program_size, List.size_toArray, Initialize.code_length,
    orderedRootCode_size, scratchWords, List.length_cons, List.length_nil]
  omega

private theorem sparseLayout_storage_le (width : Nat) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots) :
    (sparseLayout width graph rows roots).storageEnd ≤ 10 * graph.countedSize + 7 := by
  obtain ⟨children, guards⟩ := ForestIndexedOperands.matched_incidence_lengths graph rows matched
  have rootsLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  have size := graph.countedSize_eq
  simp only [sparseLayout, SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
    SharedLayout.nodeMarkerBase, ForestIndexedOperands.cacheHeap_size,
    UniformDAGRun.packetHeaderHeap_size, matched.length_eq, children, guards, rootsLength]
  omega

private theorem coldReuseCode_le (width : Nat) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n) :
    (coldReuseCode width graph rows roots assignment).size ≤ 466 * (graph.countedSize + 1) := by
  rw [coldReuseCode_size]
  have size := graph.countedSize_eq
  omega

private theorem reuse_storage_fits (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots) :
    (sparseLayout (reuseWidth graph) graph rows roots).storageEnd < 2 ^ reuseWidth graph := by
  have cap := reuse_capacity graph
  have bound := sparseLayout_storage_le (reuseWidth graph) graph rows roots matched rootMatches
  omega

private theorem reuse_code_fits (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n) :
    (coldReuseCode (reuseWidth graph) graph rows roots assignment).size < 2 ^ reuseWidth graph := by
  have cap := reuse_capacity graph
  have bound := coldReuseCode_le (reuseWidth graph) graph rows roots assignment
  omega

/- The loop keeps physically stale memo/ledger cells, and requires semantic memo
correctness only after each root's produced postorder has been evaluated. -/
structure OrderedRootInvariant (graph : DAG n) (layout : SharedLayout)
    (source : Array (Word width)) (assignment : Assignment n)
    (base rootStart visited : Nat) (callerStack callerOutput : List (Word width))
    (state : State width 8) : Prop where
  visitedBound : visited ≤ graph.roots.length
  stored : TraversalStored graph layout source state (emptyDFS graph) []
  memo : ∃ values : Fin graph.nodeCount → Bool, ∀ node,
    state.heap[layout.nodeValueBase + node.val]? = some (boolWord width (values node))
  assignmentTable : ∀ channel : Channel n,
    state.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel))
  count : state.reg 4 = word width (graph.roots.length - visited)
  cursor : state.reg 6 = word width (rootStart + visited)
  position : state.pc = word width base
  running : state.halted = false
  stack : state.stack = callerStack
  output : state.output =
    ((graph.roots.take visited).map (fun node => boolWord width (graph.eval assignment node))).reverse ++ callerOutput

private theorem emitted_prefix_successor (graph : DAG n) (assignment : Assignment n)
    (visited : Nat) (bound : visited < graph.roots.length) (callerOutput : List (Word width)) :
    boolWord width (graph.eval assignment graph.roots[visited]) ::
      (((graph.roots.take visited).map (fun node => boolWord width (graph.eval assignment node))).reverse ++ callerOutput) =
      ((graph.roots.take (visited + 1)).map (fun node => boolWord width (graph.eval assignment node))).reverse ++ callerOutput := by
  rw [List.take_succ_eq_append_getElem bound, List.map_append, List.reverse_append]
  simp

private theorem produced_node_charge (graph : DAG n) (nodes : List (Fin graph.nodeCount)) :
    nodes.length ≤ freshWeight graph nodes := by
  induction nodes with
  | nil => simp [freshWeight]
  | cons node rest ih =>
      have own : 1 ≤ localNodeWeight graph node := by simp only [localNodeWeight]; omega
      simp only [List.length_cons, freshWeight, List.map_cons, List.sum_cons] at *
      omega

private theorem root_iteration_charge (weight nodeCount channelCount dfsTicks warmTicks : Nat)
    (nodes : nodeCount ≤ weight) (channels : channelCount ≤ weight)
    (dfs : dfsTicks ≤ 46 * weight + 17) (warm : warmTicks ≤ 46 * weight + 1) :
    4 + dfsTicks + 7 + warmTicks + 3 + (12 * nodeCount + 1) +
      3 + (9 * channelCount + 1) + 4 + 4 + 6 ≤ 113 * weight + 51 := by
  omega


private theorem traversal_same_heap (graph : DAG n) (layout : SharedLayout)
    (source : Array (Word width)) (before after : State width 8)
    (logical : DFSState graph) (channels : List (Channel n))
    (stored : TraversalStored graph layout source before logical channels)
    (heap : after.heap = before.heap)
    (depth : after.reg 7 = before.reg 7) (zero : after.reg 2 = before.reg 2)
    (one : after.reg 3 = before.reg 3) :
    TraversalStored graph layout source after logical channels := by
  refine {
    sourceRetained := ?_, nodeDimension := stored.nodeDimension,
    channelDimension := stored.channelDimension, allocation := ?_, completed := ?_,
    channelLedger := ?_, channelsUnique := stored.channelsUnique, flags := ?_,
    completedScope := stored.completedScope, depth := depth.trans stored.depth,
    zero := zero.trans stored.zero, one := one.trans stored.one }
  · rw [heap]; exact stored.sourceRetained
  · rw [heap]; exact stored.allocation
  · rw [heap]; exact stored.completed
  · rw [heap]; exact stored.channelLedger
  · rw [heap]; exact stored.flags

private theorem root_discover_execution (program : Program width 8)
    (graph : DAG n) (layout : SharedLayout) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (prefixCode : ∀ phase : Fin 4, program[base + phase.val]? =
      (rootPrefixCode width (base + 297) (base + 9))[phase.val]?)
    (dfsCode : ∀ phase : Fin 120, program[base + 4 + phase.val]? =
      (dfsFromCache width caller rows roots (base + 4) layout)[phase.val]?)
    (codeFits : base + 298 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (slot : Fin graph.roots.length) (initial : State width 8)
    (stored : TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      initial (emptyDFS graph) [])
    (position : initial.pc = word width base) (running : initial.halted = false)
    (countFits : graph.roots.length < 2 ^ width)
    (count : initial.reg 4 = word width (graph.roots.length - slot.val))
    (cursor : initial.reg 6 = word width (caller.size +
      (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards rows).length) + slot.val)) :
    ∃ (final : State width 8) (logical : DFSState graph) (labels : List (Channel n)) (ticks peak : Nat),
      Execution program initial final ticks peak ∧
      ticks ≤ 46 * freshWeight graph logical.completed + 21 ∧
      peak ≤ initial.liveWords + 3 * logical.completed.length + 4 ∧
      TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
        final logical labels ∧ logical.active = [] ∧
      logical.completed = discoverNode graph (graph.roots.get slot) [] ∧
      logical.completed.toFinset = graph.cone (graph.roots.get slot) ∧
      Postorder graph logical.completed ∧
      (∀ channel, channel ∈ labels ↔ channel ∈ graph.scope (graph.roots.get slot)) ∧
      (∀ address, address < layout.nodeMarkerBase → final.heap[address]? = initial.heap[address]?) ∧
      final.stack = word width (graph.roots.length - slot.val) :: initial.stack ∧
      final.output = initial.output ∧ final.reg 4 = word width 0 ∧
      final.reg 6 = word width (caller.size +
        (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
          (ForestIndexedOperands.rowGuards rows).length) + slot.val + 1) ∧
      final.reg 7 = word width 0 ∧ final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧
      final.pc = word width (base + 124) ∧ final.halted = false := by
  have slotBound := slot.isLt
  have remaining : graph.roots.length - slot.val = (graph.roots.length - (slot.val + 1)) + 1 := by omega
  obtain ⟨entered, enterTrace, enterHeap, enterStack, enterOutput, enterCount,
      enterRegisters, enterPosition, enterRunning⟩ :=
    root_prefix_execution program initial base (base + 297) (base + 9)
      (graph.roots.length - (slot.val + 1)) prefixCode position running (by omega) (by omega)
      (by omega) (by simpa only [← remaining] using count) stored.zero
  have enterStored := traversal_same_heap graph layout
      (ForestIndexedOperands.cacheHeap width caller rows roots) initial entered (emptyDFS graph) []
      stored enterHeap (enterRegisters 7 (by decide)) (enterRegisters 2 (by decide))
      (enterRegisters 3 (by decide))
  have enterCursor := (enterRegisters 6 (by decide)).trans cursor
  obtain ⟨final, logical, labels, ticks, peak, dfsTrace, dfsTicks, dfsPeak,
      finalStored, active, completed, cone, ordered, scope, lower, stack, output,
      finalCount, finalCursor, depth, zero, one, finalPosition, finalRunning⟩ :=
    root_query_execution program graph layout caller rows roots (base + 4) matched rootMatches
      sourceSize dfsCode (by omega) storageFits slot entered (emptyDFS graph) rfl rfl
      enterStored (by simpa only [Nat.add_assoc, Nat.reduceAdd] using enterPosition)
      enterRunning enterCount enterCursor
  have enteredLive : entered.liveWords = initial.liveWords + 1 := by
    simp only [State.liveWords, enterHeap, enterStack, enterOutput, List.length_cons]
    omega
  have joined := enterTrace.append dfsTrace
  refine ⟨final, logical, labels, 4 + ticks, max (initial.liveWords + 1) peak,
    joined, ?_, ?_, finalStored, active, completed, cone, ordered, scope, ?_, ?_,
    output.trans enterOutput, finalCount, finalCursor, depth, zero, one, ?_, finalRunning⟩
  · omega
  · rw [enteredLive] at dfsPeak
    omega
  · intro address below
    exact (lower address below).trans (congrArg (fun heap => heap[address]?) enterHeap)
  · rw [stack, enterStack, ← remaining]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPosition


private theorem root_warm_execution (program : Program width 8)
    (graph : DAG n) (layout : SharedLayout) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (prefixCode : ∀ phase : Fin 4, program[base + phase.val]? =
      (rootPrefixCode width (base + 297) (base + 9))[phase.val]?)
    (dfsCode : ∀ phase : Fin 120, program[base + 4 + phase.val]? =
      (dfsFromCache width caller rows roots (base + 4) layout)[phase.val]?)
    (postCode : ∀ phase : Fin 7, program[base + 124 + phase.val]? =
      (postQueryCode width layout.nodeLedgerBase layout.nodeCountSlot)[phase.val]?)
    (warmCode : ∀ phase : Fin 125, program[base + 131 + phase.val]? =
      (warmLedgerCode width (base + 131) layout.nodeValueBase layout.storageEnd
        (warmLayout caller rows layout))[phase.val]?)
    (codeFits : base + 298 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (slot : Fin graph.roots.length) (initial : State width 8)
    (assignment : Assignment n) (initialValues : Fin graph.nodeCount → Bool)
    (stored : TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      initial (emptyDFS graph) [])
    (table : ∀ node : Fin graph.nodeCount,
      initial.heap[layout.nodeValueBase + node.val]? = some (boolWord width (initialValues node)))
    (channels : ∀ channel : Channel n,
      initial.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)))
    (position : initial.pc = word width base) (running : initial.halted = false)
    (countFits : graph.roots.length < 2 ^ width)
    (count : initial.reg 4 = word width (graph.roots.length - slot.val))
    (cursor : initial.reg 6 = word width (caller.size +
      (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards rows).length) + slot.val)) :
    ∃ (final : State width 8) (logical : DFSState graph) (labels : List (Channel n))
      (ticks peak : Nat) (values : Fin graph.nodeCount → Bool),
      Execution program initial final ticks peak ∧
      ticks ≤ 92 * freshWeight graph logical.completed + 29 ∧
      peak ≤ initial.liveWords + 3 * logical.completed.length + 4 ∧
      logical.active = [] ∧ logical.completed.toFinset = graph.cone (graph.roots.get slot) ∧
      Postorder graph logical.completed ∧ labels.Nodup ∧
      (∀ channel, channel ∈ labels ↔ channel ∈ graph.scope (graph.roots.get slot)) ∧
      (∀ node ∈ logical.completed, values node = graph.eval assignment node) ∧
      (∀ node, final.heap[layout.nodeValueBase + node.val]? = some (boolWord width (values node))) ∧
      (∀ channel, final.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel))) ∧
      CachePrefix final.heap (ForestIndexedOperands.cacheHeap width caller rows roots) ∧
      CompletedStored layout final.heap graph logical.completed ∧
      ChannelsStored layout final.heap labels ∧
      (∀ node, final.heap[layout.nodeMarkerBase + node.val]? =
        some (word width (if node ∈ logical.completed then 1 else 0))) ∧
      final.heap.size = layout.storageEnd ∧
      final.stack = word width (caller.size +
        (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
          (ForestIndexedOperands.rowGuards rows).length) + slot.val + 1) ::
        word width (graph.roots.length - slot.val) :: initial.stack ∧
      final.output = initial.output ∧ final.reg 7 = word width (graph.roots.get slot).val ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧
      final.pc = word width (base + 256) ∧ final.halted = false := by
  let rootCursor := caller.size +
    (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards rows).length) + slot.val
  let source := ForestIndexedOperands.cacheHeap width caller rows roots
  obtain ⟨discovered, logical, labels, dfsTicks, dfsPeak, dfsTrace, dfsTime, dfsSpace,
      discoveredStored, active, completed, cone, ordered, scope, lower, stack, output,
      doneCount, nextCursor, depth, zero, one, nextPosition, nextRunning⟩ :=
    root_discover_execution program graph layout caller rows roots base matched rootMatches sourceSize
      prefixCode dfsCode codeFits storageFits slot initial stored position running countFits count cursor
  have allocation := discoveredStored.allocation
  have dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n :=
    ⟨stored.nodeDimension, stored.channelDimension⟩
  have rootSourceBound : rootCursor < source.size := by
    simp only [rootCursor, source, ForestIndexedOperands.cacheHeap_size]
    have rootLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
    have valid := slot.isLt
    omega
  have sourceBefore : layout.sourceEnd ≤ layout.nodeMarkerBase := by
    simp only [SharedLayout.nodeMarkerBase]; omega
  have rootBound : rootCursor < discovered.heap.size := by
    rw [allocation]
    have sourceBound : rootCursor < layout.sourceEnd := by simpa only [source, sourceSize] using rootSourceBound
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega
  have countBound : layout.nodeCountSlot < discovered.heap.size := by
    rw [allocation]; simp only [SharedLayout.storageEnd]; omega
  have countCell : discovered.heap[layout.nodeCountSlot]'countBound = word width logical.completed.length := by
    exact Option.some.inj ((Array.getElem?_eq_getElem countBound).symm.trans discoveredStored.completed.count)
  have rootCell : discovered.heap[rootCursor]'rootBound = word width (graph.roots.get slot).val :=
    retained_source_cell _ _ discoveredStored.sourceRetained _ _ rootSourceBound rootBound
      (ForestIndexedOperands.cache_declared_root_word caller graph rows roots rootMatches slot)
  have completedLength := postorder_length_bound graph logical.completed ordered
  have lengthFits : logical.completed.length < 2 ^ width := by
    have nodesBefore : graph.nodeCount ≤ layout.storageEnd := by
      simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
      rw [dimensions.1]; omega
    omega
  have cursorFits : rootCursor + 1 < 2 ^ width := by omega
  have rootFits : (graph.roots.get slot).val < 2 ^ width := by
    have valid := (graph.roots.get slot).isLt
    have nodesBefore : graph.nodeCount ≤ layout.storageEnd := by
      simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
      rw [dimensions.1]; omega
    omega
  obtain ⟨ready, setupTrace, setupHeap, setupStack, setupOutput, rootHeld,
      ledgerCursor, ledgerCount, setupZero, setupOne, setupPosition, setupRunning⟩ :=
    post_query_execution program discovered (base + 124) rootCursor (graph.roots.get slot).val
      layout.nodeLedgerBase layout.nodeCountSlot logical.completed.length postCode nextPosition nextRunning
      (by omega) (by omega) cursorFits (by
        simp only [SharedLayout.nodeLedgerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot] at *
        omega) lengthFits rootFits nextCursor rootBound countBound rootCell countCell
  have readyLedger : CompletedStored layout ready.heap graph logical.completed := by
    rw [setupHeap]; exact discoveredStored.completed
  have readyRetained : CachePrefix ready.heap source := by rw [setupHeap]; exact discoveredStored.sourceRetained
  have readyAllocation : ready.heap.size = layout.storageEnd := by rw [setupHeap]; exact allocation
  have readyTable : ∀ node : Fin graph.nodeCount,
      ready.heap[layout.nodeValueBase + node.val]? = some (boolWord width (initialValues node)) := by
    intro node
    rw [setupHeap, lower _ (by
      simp only [SharedLayout.nodeValueBase, SharedLayout.nodeMarkerBase]
      have valid := node.isLt; rw [dimensions.1]; omega)]
    exact table node
  have readyChannels : ∀ channel : Channel n,
      ready.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)) := by
    intro channel
    rw [setupHeap, lower _ (by
      simp only [SharedLayout.channelValueBase, SharedLayout.nodeMarkerBase]
      have valid := channel.isLt; rw [dimensions.2]; omega)]
    exact channels channel
  obtain ⟨final, warmTicks, warmPeak, values, warmTrace, warmTime, warmSpace, evaluated,
      finalTable, finalChannels, finalRetained, finalLedger, finalAllocation, upper,
      finalStack, finalOutput, finalRoot, finalZero, finalOne, finalPosition, finalRunning⟩ :=
    warm_ledger_execution program caller graph rows roots layout matched heads sourceSize dimensions
      assignment logical.completed ordered (base + 131) warmCode (by omega) storageFits ready initialValues
      readyRetained readyAllocation readyLedger readyTable readyChannels setupPosition setupRunning
      ledgerCount ledgerCursor (setupZero.trans zero) (setupOne.trans one)
  have discoveredLive : discovered.liveWords = initial.liveWords + 1 := by
    simp only [State.liveWords, allocation, stored.allocation, stack, output, List.length_cons]
    omega
  have readyLive : ready.liveWords = initial.liveWords + 2 := by
    have pushed : ready.liveWords = discovered.liveWords + 1 := by
      simp only [State.liveWords, setupHeap, setupStack, setupOutput, List.length_cons]
      omega
    rw [pushed, discoveredLive]
  have channelLedger : ChannelsStored layout final.heap labels := by
    constructor
    · rw [upper _ (by simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot]; omega), setupHeap]
      exact discoveredStored.channelLedger.count
    · intro index
      rw [upper _ (by simp only [SharedLayout.channelLedgerBase]; omega), setupHeap]
      exact discoveredStored.channelLedger.ledger index
    · intro channel
      rw [upper _ (by simp only [SharedLayout.channelMarkerBase]; omega), setupHeap]
      exact discoveredStored.channelLedger.flags channel
  have flags : ∀ node : Fin graph.nodeCount, final.heap[layout.nodeMarkerBase + node.val]? =
      some (word width (if node ∈ logical.completed then 1 else 0)) := by
    intro node
    rw [upper _ (by omega), setupHeap]
    simpa only [active, List.not_mem_nil, or_false] using discoveredStored.flags node
  refine ⟨final, logical, labels, dfsTicks + 7 + warmTicks,
    max (max dfsPeak (discovered.liveWords + 1)) warmPeak, values,
    (dfsTrace.append setupTrace).append warmTrace, ?_, ?_, active, cone, ordered,
    discoveredStored.channelsUnique, scope, evaluated, finalTable, finalChannels,
    finalRetained, finalLedger, channelLedger, flags, finalAllocation, ?_, ?_, ?_,
    finalZero, finalOne, ?_, finalRunning⟩
  · omega
  · rw [readyLive] at warmSpace
    have upperPeak := dfsSpace
    rw [discoveredLive]
    omega
  · rw [finalStack, setupStack, stack]
  · exact finalOutput.trans (setupOutput.trans output)
  · exact finalRoot.trans rootHeld
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPosition


private theorem root_reset_execution (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base : Nat)
    (dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n)
    (sourceSize : source.size = layout.sourceEnd)
    (nodeSetup : ∀ phase : Fin 3, program[base + 256 + phase.val]? =
      (ledgerSetupCode width layout.nodeLedgerBase layout.nodeCountSlot)[phase.val]?)
    (nodeCode : ∀ phase : Fin 12, program[base + 259 + phase.val]? =
      (resetNodesCode width (base + 259) layout.nodeMarkerBase layout.mapBase)[phase.val]?)
    (channelSetup : ∀ phase : Fin 3, program[base + 271 + phase.val]? =
      (ledgerSetupCode width layout.channelLedgerBase layout.channelCountSlot)[phase.val]?)
    (channelCode : ∀ phase : Fin 9, program[base + 274 + phase.val]? =
      (resetChannelsCode width (base + 274) layout.channelMarkerBase)[phase.val]?)
    (clearCode : ∀ phase : Fin 4, program[base + 283 + phase.val]? =
      (clearLedgerCountsCode width layout.nodeCountSlot layout.channelCountSlot)[phase.val]?)
    (codeFits : base + 298 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (nodes : List (Fin graph.nodeCount)) (labels : List (Channel n))
    (nodesUnique : nodes.Nodup) (labelsUnique : labels.Nodup)
    (initial : State width 8) (allocation : initial.heap.size = layout.storageEnd)
    (ledger : CompletedStored layout initial.heap graph nodes)
    (channels : ChannelsStored layout initial.heap labels)
    (position : initial.pc = word width (base + 256)) (running : initial.halted = false)
    (zero : initial.reg 2 = word width 0) (one : initial.reg 3 = word width 1) :
    ∃ final, Execution program initial final (12 * nodes.length + 9 * labels.length + 12) initial.liveWords ∧
      final.heap = resetHeap layout initial.heap nodes labels ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 7 = initial.reg 7 ∧ final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧
      final.pc = word width (base + 287) ∧ final.halted = false := by
  have nodesBound : nodes.length ≤ graph.nodeCount := by
    simpa only [Fintype.card_fin] using nodesUnique.length_le_card
  have labelsBound : labels.length ≤ n := by
    simpa only [Fintype.card_fin] using labelsUnique.length_le_card
  have nodeCountBound : layout.nodeCountSlot < initial.heap.size := by
    rw [allocation]; simp only [SharedLayout.storageEnd]; omega
  have channelCountBound : layout.channelCountSlot < initial.heap.size := by
    rw [allocation]; simp only [SharedLayout.storageEnd, SharedLayout.channelCountSlot]; omega
  have nodeLengthFits : nodes.length < 2 ^ width := by
    have sizeBound : graph.nodeCount ≤ layout.storageEnd := by
      simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
      rw [dimensions.1]; omega
    omega
  have labelLengthFits : labels.length < 2 ^ width := by
    have sizeBound : n ≤ layout.storageEnd := by
      simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
      rw [dimensions.2]; omega
    omega
  have nodeCell : initial.heap[layout.nodeCountSlot]'nodeCountBound = word width nodes.length := by
    exact Option.some.inj ((Array.getElem?_eq_getElem nodeCountBound).symm.trans ledger.count)
  obtain ⟨nodeReady, setupTrace, setupHeap, setupStack, setupOutput, setupCursor,
      setupCount, setupRegisters, setupPosition, setupRunning⟩ :=
    ledger_setup_execution program initial (base + 256) layout.nodeLedgerBase layout.nodeCountSlot
      nodes.length nodeSetup position running (by omega) (by omega) nodeCountBound nodeCell
  let resetNodes := nodes.map (Fin.cast dimensions.1.symm)
  have nodeReadyAllocation : nodeReady.heap.size = layout.storageEnd := by rw [setupHeap]; exact allocation
  have nodeStored : ScopeStored nodeReady.heap layout.nodeLedgerBase resetNodes := by
    rw [setupHeap]; exact completed_ledger_scope graph layout initial.heap nodes dimensions.1 ledger
  obtain ⟨nodeDone, nodeTrace, nodeHeap, nodeStack, nodeOutput, nodeCount, nodeCursor,
      nodeZero, nodeOne, nodeRoot, nodePosition, nodeRunning⟩ :=
    reset_node_suffix program layout (base + 259) nodeCode (by omega) storageFits resetNodes nodeReady
      layout.nodeLedgerBase nodeReadyAllocation nodeStored (Nat.le_refl _) (by
        simp only [resetNodes, List.length_map, SharedLayout.nodeLedgerBase, SharedLayout.storageEnd,
          SharedLayout.nodeCountSlot]
        have dimension := dimensions.1
        omega)
      (by simpa only [resetNodes, List.length_map] using nodeLengthFits) setupPosition setupRunning
      (by simpa only [resetNodes, List.length_map] using setupCount) setupCursor
      ((setupRegisters 2 (by decide) (by decide) (by decide)).trans zero)
      ((setupRegisters 3 (by decide) (by decide) (by decide)).trans one)
  have actualNodes : nodeDone.heap = clearNodes layout initial.heap nodes := by
    rw [nodeHeap, setupHeap]
    exact clearNodes_map_cast layout initial.heap dimensions.1.symm nodes
  have nodeDoneAllocation : nodeDone.heap.size = layout.storageEnd := by
    rw [actualNodes, clearNodes_size]; exact allocation
  have nodeClearFrame : ∀ address, layout.channelMarkerBase ≤ address →
      (address < layout.mapBase ∨ layout.nodeLedgerBase ≤ address) →
      nodeDone.heap[address]? = initial.heap[address]? := by
    intro address low outside
    rw [actualNodes]
    apply clearNodes_frame
    intro node member
    have valid := node.isLt
    have dimension := dimensions.1
    simp only [SharedLayout.channelMarkerBase, SharedLayout.mapBase,
      SharedLayout.nodeLedgerBase] at low outside
    simp only [SharedLayout.mapBase]
    rcases outside with before | after <;> constructor <;> omega
  have channelLedger : ChannelsStored layout nodeDone.heap labels := by
    constructor
    · rw [nodeClearFrame _ (by simp only [SharedLayout.channelCountSlot,
        SharedLayout.nodeCountSlot, SharedLayout.channelMarkerBase]; omega)
        (Or.inr (by simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot,
          SharedLayout.nodeLedgerBase]; omega))]
      exact channels.count
    · intro index
      rw [nodeClearFrame _ (by simp only [SharedLayout.channelLedgerBase,
        SharedLayout.channelMarkerBase]; omega)
        (Or.inr (by simp only [SharedLayout.channelLedgerBase, SharedLayout.nodeLedgerBase]; omega))]
      exact channels.ledger index
    · intro channel
      have valid := channel.isLt
      have dimension := dimensions.2
      rw [nodeClearFrame _ (by omega) (Or.inl (by
        simp only [SharedLayout.channelMarkerBase, SharedLayout.mapBase]; omega))]
      exact channels.flags channel
  have channelCountBound : layout.channelCountSlot < nodeDone.heap.size := by
    rw [nodeDoneAllocation]; simp only [SharedLayout.storageEnd, SharedLayout.channelCountSlot]; omega
  have channelCell : nodeDone.heap[layout.channelCountSlot]'channelCountBound = word width labels.length := by
    exact Option.some.inj ((Array.getElem?_eq_getElem channelCountBound).symm.trans channelLedger.count)
  obtain ⟨channelReady, channelSetupTrace, channelSetupHeap, channelSetupStack, channelSetupOutput,
      channelSetupCursor, channelSetupCount, channelSetupRegisters, channelSetupPosition, channelSetupRunning⟩ :=
    ledger_setup_execution program nodeDone (base + 271) layout.channelLedgerBase layout.channelCountSlot
      labels.length channelSetup nodePosition nodeRunning (by omega) (by omega) channelCountBound channelCell
  let resetLabels := labels.map (Fin.cast dimensions.2.symm)
  have channelReadyAllocation : channelReady.heap.size = layout.storageEnd := by
    rw [channelSetupHeap]; exact nodeDoneAllocation
  have labelStored : ScopeStored channelReady.heap layout.channelLedgerBase resetLabels := by
    rw [channelSetupHeap]; exact published_ledger_scope layout nodeDone.heap labels dimensions.2 channelLedger
  obtain ⟨cleared, channelTrace, channelHeap, channelStack, channelOutput, channelCount, channelCursor,
      channelZero, channelOne, channelRoot, channelPosition, channelRunning⟩ :=
    reset_channel_suffix program layout (base + 274) channelCode (by omega) storageFits resetLabels channelReady
      layout.channelLedgerBase channelReadyAllocation labelStored (Nat.le_refl _) (by
        simp only [resetLabels, List.length_map, SharedLayout.channelLedgerBase, SharedLayout.storageEnd,
          SharedLayout.nodeCountSlot]
        have dimension := dimensions.2
        omega)
      (by simpa only [resetLabels, List.length_map] using labelLengthFits) channelSetupPosition channelSetupRunning
      (by simpa only [resetLabels, List.length_map] using channelSetupCount) channelSetupCursor
      ((channelSetupRegisters 2 (by decide) (by decide) (by decide)).trans
        (nodeZero.trans ((setupRegisters 2 (by decide) (by decide) (by decide)).trans zero)))
      ((channelSetupRegisters 3 (by decide) (by decide) (by decide)).trans
        (nodeOne.trans ((setupRegisters 3 (by decide) (by decide) (by decide)).trans one)))
  have actualLabels : cleared.heap = clearChannels layout (clearNodes layout initial.heap nodes) labels := by
    rw [channelHeap, channelSetupHeap, actualNodes]
    exact clearChannels_map_cast layout _ dimensions.2.symm labels
  have clearedAllocation : cleared.heap.size = layout.storageEnd := by
    rw [actualLabels, clearChannels_size, clearNodes_size]; exact allocation
  have nodeCountBound : layout.nodeCountSlot < cleared.heap.size := by
    rw [clearedAllocation]; simp only [SharedLayout.storageEnd]; omega
  have channelCountBound : layout.channelCountSlot < cleared.heap.size := by
    rw [clearedAllocation]; simp only [SharedLayout.storageEnd, SharedLayout.channelCountSlot]; omega
  obtain ⟨final, clearTrace, finalHeap, finalStack, finalOutput, finalRegisters, finalPosition, finalRunning⟩ :=
    clear_counts_execution program cleared (base + 283) layout.nodeCountSlot layout.channelCountSlot clearCode
      channelPosition channelRunning (by omega) (by omega) nodeCountBound channelCountBound
      (channelZero.trans ((channelSetupRegisters 2 (by decide) (by decide) (by decide)).trans
        (nodeZero.trans ((setupRegisters 2 (by decide) (by decide) (by decide)).trans zero))))
  have semantic : final.heap = resetHeap layout initial.heap nodes labels := by
    have actualStores :
        (cleared.heap.setIfInBounds layout.nodeCountSlot (word width 0)).setIfInBounds
          layout.channelCountSlot (word width 0) =
        (cleared.heap.set layout.nodeCountSlot (word width 0) nodeCountBound).set
          layout.channelCountSlot (word width 0) (by simpa only [Array.size_set] using channelCountBound) := by
      simp only [Array.setIfInBounds_def, nodeCountBound, dite_eq_left, Array.size_set, channelCountBound]
    rw [finalHeap, ← actualStores, actualLabels]
    rfl
  have nodeReadyLive : nodeReady.liveWords = initial.liveWords := by
    simp only [State.liveWords, setupHeap, setupStack, setupOutput]
  have nodeDoneLive : nodeDone.liveWords = initial.liveWords := by
    simp only [State.liveWords, nodeDoneAllocation, allocation, nodeStack, setupStack, nodeOutput, setupOutput]
  have channelReadyLive : channelReady.liveWords = initial.liveWords := by
    have same : channelReady.liveWords = nodeDone.liveWords := by
      simp only [State.liveWords, channelSetupHeap, channelSetupStack, channelSetupOutput]
    exact same.trans nodeDoneLive
  have clearedLive : cleared.liveWords = initial.liveWords := by
    simp only [State.liveWords, clearedAllocation, allocation, channelStack, channelSetupStack,
      nodeStack, setupStack, channelOutput, channelSetupOutput, nodeOutput, setupOutput]
  refine ⟨final, ?_, semantic, ?_, ?_, ?_, ?_, ?_, finalPosition, finalRunning⟩
  · convert (((setupTrace.append nodeTrace).append channelSetupTrace).append channelTrace).append clearTrace using 1 <;>
      simp only [resetNodes, resetLabels, List.length_map, nodeReadyLive, nodeDoneLive,
        channelReadyLive, clearedLive, Nat.max_self] <;> omega
  · rw [finalStack, channelStack, channelSetupStack, nodeStack, setupStack]
  · rw [finalOutput, channelOutput, channelSetupOutput, nodeOutput, setupOutput]
  · exact (finalRegisters 7 (by decide)).trans (channelRoot.trans
      ((channelSetupRegisters 7 (by decide) (by decide) (by decide)).trans
        (nodeRoot.trans (setupRegisters 7 (by decide) (by decide) (by decide)))))
  · exact (finalRegisters 2 (by decide)).trans (channelZero.trans
      ((channelSetupRegisters 2 (by decide) (by decide) (by decide)).trans
        (nodeZero.trans ((setupRegisters 2 (by decide) (by decide) (by decide)).trans zero))))
  · exact (finalRegisters 3 (by decide)).trans (channelOne.trans
      ((channelSetupRegisters 3 (by decide) (by decide) (by decide)).trans
        (nodeOne.trans ((setupRegisters 3 (by decide) (by decide) (by decide)).trans one))))


private structure OrderedRootAt (program : Program width 8) (base : Nat)
    (caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (layout : SharedLayout) : Prop where
  prefixCode : ∀ phase : Fin 4, program[base + phase.val]? =
    (rootPrefixCode width (base + 297) (base + 9))[phase.val]?
  dfsCode : ∀ phase : Fin 120, program[base + 4 + phase.val]? =
    (dfsFromCache width caller rows roots (base + 4) layout)[phase.val]?
  postCode : ∀ phase : Fin 7, program[base + 124 + phase.val]? =
    (postQueryCode width layout.nodeLedgerBase layout.nodeCountSlot)[phase.val]?
  warmCode : ∀ phase : Fin 125, program[base + 131 + phase.val]? =
    (warmLedgerCode width (base + 131) layout.nodeValueBase layout.storageEnd
      (warmLayout caller rows layout))[phase.val]?
  nodeSetup : ∀ phase : Fin 3, program[base + 256 + phase.val]? =
    (ledgerSetupCode width layout.nodeLedgerBase layout.nodeCountSlot)[phase.val]?
  nodeCode : ∀ phase : Fin 12, program[base + 259 + phase.val]? =
    (resetNodesCode width (base + 259) layout.nodeMarkerBase layout.mapBase)[phase.val]?
  channelSetup : ∀ phase : Fin 3, program[base + 271 + phase.val]? =
    (ledgerSetupCode width layout.channelLedgerBase layout.channelCountSlot)[phase.val]?
  channelCode : ∀ phase : Fin 9, program[base + 274 + phase.val]? =
    (resetChannelsCode width (base + 274) layout.channelMarkerBase)[phase.val]?
  clearCode : ∀ phase : Fin 4, program[base + 283 + phase.val]? =
    (clearLedgerCountsCode width layout.nodeCountSlot layout.channelCountSlot)[phase.val]?
  emitCode : ∀ phase : Fin 4, program[base + 287 + phase.val]? =
    (memoEmitCode width layout.nodeValueBase)[phase.val]?
  backCode : ∀ phase : Fin 6, program[base + 291 + phase.val]? =
    (rootBackedgeCode width base)[phase.val]?
  doneCode : program[base + 297]? = some .halt

@[simp] private theorem rootPrefixCode_size (width done entry : Nat) :
    (rootPrefixCode width done entry).size = 4 := rfl
@[simp] private theorem postQueryCode_size (width ledger count : Nat) :
    (postQueryCode width ledger count).size = 7 := rfl
@[simp] private theorem ledgerSetupCode_size (width ledger count : Nat) :
    (ledgerSetupCode width ledger count).size = 3 := rfl
@[simp] private theorem memoEmitCode_size (width nodeBase : Nat) :
    (memoEmitCode width nodeBase).size = 4 := rfl
@[simp] private theorem rootBackedgeCode_size (width base : Nat) :
    (rootBackedgeCode width base).size = 6 := rfl
@[simp] private theorem dfsFromCache_size (width : Nat) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat) (layout : SharedLayout) :
    (dfsFromCache width caller rows roots base layout).size = 120 := by
  simp only [dfsFromCache, dfsProgram_size]

attribute [local irreducible] rootPrefixCode postQueryCode ledgerSetupCode memoEmitCode rootBackedgeCode
attribute [local irreducible] dfsFromCache warmLedgerCode

private theorem ordered_root_sections (program : Program width 8) (base : Nat)
    (caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (layout : SharedLayout)
    (physical : CodeAt8 program base (orderedRootCode width base caller rows roots layout)) :
    OrderedRootAt program base caller rows roots layout := by
  let p := rootPrefixCode width (base + 297) (base + 9)
  let d := dfsFromCache width caller rows roots (base + 4) layout
  let q := postQueryCode width layout.nodeLedgerBase layout.nodeCountSlot
  let w := warmLedgerCode width (base + 131) layout.nodeValueBase layout.storageEnd (warmLayout caller rows layout)
  let ns := ledgerSetupCode width layout.nodeLedgerBase layout.nodeCountSlot
  let nr := resetNodesCode width (base + 259) layout.nodeMarkerBase layout.mapBase
  let cs := ledgerSetupCode width layout.channelLedgerBase layout.channelCountSlot
  let cr := resetChannelsCode width (base + 274) layout.channelMarkerBase
  let z := clearLedgerCountsCode width layout.nodeCountSlot layout.channelCountSlot
  let e := memoEmitCode width layout.nodeValueBase
  let b := rootBackedgeCode width base
  have codeEq : orderedRootCode width base caller rows roots layout =
      p ++ (d ++ (q ++ (w ++ (ns ++ (nr ++ (cs ++ (cr ++ (z ++ (e ++ (b ++ #[.halt])))))))))) := by
    simp only [orderedRootCode, p, d, q, w, ns, nr, cs, cr, z, e, b,
      rootPrefixCode, postQueryCode, ledgerSetupCode, memoEmitCode, rootBackedgeCode,
      Nat.add_assoc, Nat.reduceAdd, Array.append_assoc]
  rw [codeEq] at physical
  have pp := codeAt8_prefix _ _ _ _ physical
  have dd := codeAt8_suffix _ _ _ _ physical
  have ds : d.size = 120 := by simp [d, dfsFromCache]
  have ws : w.size = 125 := by simp only [w, warmLedgerCode_size]
  have dPart := codeAt8_prefix _ _ _ _ dd
  have qq := codeAt8_suffix _ _ _ _ dd
  have qPart := codeAt8_prefix _ _ _ _ qq
  have ww := codeAt8_suffix _ _ _ _ qq
  have wPart := codeAt8_prefix _ _ _ _ ww
  have nn := codeAt8_suffix _ _ _ _ ww
  have nsPart := codeAt8_prefix _ _ _ _ nn
  have nrr := codeAt8_suffix _ _ _ _ nn
  have nrPart := codeAt8_prefix _ _ _ _ nrr
  have cc := codeAt8_suffix _ _ _ _ nrr
  have csPart := codeAt8_prefix _ _ _ _ cc
  have crr := codeAt8_suffix _ _ _ _ cc
  have crPart := codeAt8_prefix _ _ _ _ crr
  have zz := codeAt8_suffix _ _ _ _ crr
  have zPart := codeAt8_prefix _ _ _ _ zz
  have ee := codeAt8_suffix _ _ _ _ zz
  have ePart := codeAt8_prefix _ _ _ _ ee
  have bb := codeAt8_suffix _ _ _ _ ee
  have bPart := codeAt8_prefix _ _ _ _ bb
  have hh := codeAt8_suffix _ _ _ _ bb
  have ps : p.size = 4 := rootPrefixCode_size _ _ _
  have qs : q.size = 7 := postQueryCode_size _ _ _
  have nss : ns.size = 3 := ledgerSetupCode_size _ _ _
  have nrs : nr.size = 12 := resetNodesCode_size _ _ _ _
  have css : cs.size = 3 := ledgerSetupCode_size _ _ _
  have crs : cr.size = 9 := resetChannelsCode_size _ _ _
  have zs : z.size = 4 := clearLedgerCountsCode_size _ _ _
  have es : e.size = 4 := memoEmitCode_size _ _
  have bs : b.size = 6 := rootBackedgeCode_size _ _
  simp only [CodeAt8, p, d, q, w, ns, nr, cs, cr, z, e, b,
    rootPrefixCode_size, dfsFromCache_size, postQueryCode_size, warmLedgerCode_size,
    ledgerSetupCode_size, resetNodesCode_size, resetChannelsCode_size, clearLedgerCountsCode_size,
    memoEmitCode_size, rootBackedgeCode_size, Nat.add_assoc, Nat.reduceAdd]
    at pp dPart qPart wPart nsPart nrPart csPart crPart zPart ePart bPart hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [p, Nat.add_assoc] using pp
  · intro phase
    have valid : phase.val < d.size := by rw [ds]; exact phase.isLt
    have cell := dPart ⟨phase.val, valid⟩
    simpa only [d, Nat.add_assoc] using cell
  · simpa only [q, Nat.add_assoc] using qPart
  · intro phase
    have valid : phase.val < w.size := by rw [ws]; exact phase.isLt
    have cell := wPart ⟨phase.val, valid⟩
    simpa only [w, Nat.add_assoc] using cell
  · simpa only [ns, Nat.add_assoc] using nsPart
  · simpa only [nr, Nat.add_assoc] using nrPart
  · simpa only [cs, Nat.add_assoc] using csPart
  · simpa only [cr, Nat.add_assoc] using crPart
  · simpa only [z, Nat.add_assoc] using zPart
  · simpa only [e, Nat.add_assoc] using ePart
  · simpa only [b, Nat.add_assoc] using bPart
  · simpa using hh ⟨0, by change 0 < 1; decide⟩


theorem ordered_root_iteration (program : Program width 8)
    (graph : DAG n) (layout : SharedLayout) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (physical : CodeAt8 program base (orderedRootCode width base caller rows roots layout))
    (codeFits : base + 298 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (assignment : Assignment n) (slot : Fin graph.roots.length)
    (callerStack callerOutput : List (Word width)) (initial : State width 8)
    (invariant : OrderedRootInvariant graph layout
      (ForestIndexedOperands.cacheHeap width caller rows roots) assignment base
      (caller.size + (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards rows).length)) slot.val callerStack callerOutput initial)
    (countFits : graph.roots.length < 2 ^ width) :
    ∃ (final : State width 8) (logical : DFSState graph) (labels : List (Channel n)) (ticks peak : Nat),
      Execution program initial final ticks peak ∧
      ticks ≤ 113 * freshWeight graph logical.completed + 51 ∧
      peak ≤ initial.liveWords + 3 * logical.completed.length + 4 ∧
      logical.completed.toFinset = graph.cone (graph.roots.get slot) ∧
      (∀ channel, channel ∈ labels ↔ channel ∈ graph.scope (graph.roots.get slot)) ∧
      OrderedRootInvariant graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
        assignment base (caller.size + (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
          (ForestIndexedOperands.rowGuards rows).length)) (slot.val + 1) callerStack callerOutput final := by
  have sections := ordered_root_sections program base caller rows roots layout physical
  obtain ⟨initialValues, table⟩ := invariant.memo
  obtain ⟨warm, logical, labels, warmTicks, warmPeak, values, warmTrace, warmTime, warmSpace,
      active, cone, ordered, labelsUnique, scope, evaluated, finalTable, finalChannels,
      retained, ledger, channelLedger, flags, allocation, stack, output, rootHeld,
      zero, one, position, running⟩ :=
    root_warm_execution program graph layout caller rows roots base matched heads rootMatches sourceSize
      sections.prefixCode sections.dfsCode sections.postCode sections.warmCode codeFits storageFits
      slot initial assignment initialValues invariant.stored table invariant.assignmentTable
      invariant.position invariant.running countFits invariant.count invariant.cursor
  have dimensions : layout.nodeCount = graph.nodeCount ∧ layout.channels = n :=
    ⟨invariant.stored.nodeDimension, invariant.stored.channelDimension⟩
  obtain ⟨reset, resetTrace, resetHeapEq, resetStack, resetOutput, resetRoot, resetZero,
      resetOne, resetPosition, resetRunning⟩ :=
    root_reset_execution program graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      base dimensions sourceSize sections.nodeSetup sections.nodeCode sections.channelSetup
      sections.channelCode sections.clearCode codeFits storageFits logical.completed labels ordered.1
      labelsUnique warm allocation ledger channelLedger position running zero one
  have resetAllocation : reset.heap.size = layout.storageEnd := by
    rw [resetHeapEq, resetHeap_size]; exact allocation
  have rootBound : layout.nodeValueBase + (graph.roots.get slot).val < reset.heap.size := by
    rw [resetAllocation]
    have valid := (graph.roots.get slot).isLt
    have dimension := dimensions.1
    simp only [SharedLayout.nodeValueBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
      SharedLayout.nodeMarkerBase]
    omega
  have rootDone : graph.roots.get slot ∈ logical.completed := by
    apply List.mem_toFinset.mp
    rw [cone]
    exact graph.self_mem_cone _
  have rootCell : reset.heap[layout.nodeValueBase + (graph.roots.get slot).val]'rootBound =
      boolWord width (graph.eval assignment (graph.roots.get slot)) := by
    have wordCell : reset.heap[layout.nodeValueBase + (graph.roots.get slot).val]? =
        some (boolWord width (graph.eval assignment (graph.roots.get slot))) := by
      rw [resetHeapEq, resetHeap_lower_frame layout warm.heap logical.completed labels _ (by
        simp only [SharedLayout.nodeValueBase, SharedLayout.nodeMarkerBase]
        have valid := (graph.roots.get slot).isLt
        have dimension := dimensions.1
        omega), finalTable, evaluated _ rootDone]
    exact Option.some.inj ((Array.getElem?_eq_getElem rootBound).symm.trans wordCell)
  obtain ⟨emitted, emitTrace, emitHeap, emitStack, emitOutput, emitRegisters, emitPosition, emitRunning⟩ :=
    memo_emit_execution program reset (base + 287) layout.nodeValueBase (graph.roots.get slot).val
      (boolWord width (graph.eval assignment (graph.roots.get slot))) sections.emitCode resetPosition resetRunning
      (by omega) (by omega) rootBound (resetRoot.trans rootHeld) rootCell
  let rootCursor := caller.size +
    (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards rows).length) + slot.val + 1
  have remaining : graph.roots.length - slot.val = (graph.roots.length - (slot.val + 1)) + 1 := by
    have valid := slot.isLt; omega
  have savedStack : emitted.stack = word width rootCursor ::
      word width ((graph.roots.length - (slot.val + 1)) + 1) :: callerStack := by
    rw [emitStack, resetStack, stack, invariant.stack, remaining]
  obtain ⟨final, backTrace, backHeap, backStack, backOutput, backCount, backCursor,
      backDepth, backZero, backOne, backPosition, backRunning⟩ :=
    root_backedge_execution program emitted (base + 291) base rootCursor
      (graph.roots.length - (slot.val + 1)) callerStack sections.backCode emitPosition emitRunning
      (by omega) (by omega) (by have valid := slot.isLt; omega) savedStack
      ((emitRegisters 2 (by decide) (by decide)).trans resetZero)
  have finalHeap : final.heap = resetHeap layout warm.heap logical.completed labels := by
    rw [backHeap, emitHeap, resetHeapEq]
  have finalZero : final.reg 2 = word width 0 :=
    backZero.trans ((emitRegisters 2 (by decide) (by decide)).trans resetZero)
  have finalOne : final.reg 3 = word width 1 :=
    backOne.trans ((emitRegisters 3 (by decide) (by decide)).trans resetOne)
  have finalStored := reset_empty_stored graph layout
    (ForestIndexedOperands.cacheHeap width caller rows roots) warm.heap logical.completed labels
    dimensions sourceSize allocation retained flags channelLedger.flags final finalHeap backDepth finalZero finalOne
  have lowerFrame : ∀ address, address < layout.nodeMarkerBase → final.heap[address]? = warm.heap[address]? := by
    intro address below
    rw [finalHeap]
    exact resetHeap_lower_frame layout warm.heap logical.completed labels address below
  have finalMemo : ∃ vals : Fin graph.nodeCount → Bool, ∀ node,
      final.heap[layout.nodeValueBase + node.val]? = some (boolWord width (vals node)) := by
    refine ⟨values, ?_⟩
    intro node
    rw [lowerFrame _ (by
      have valid := node.isLt; have dimension := dimensions.1
      simp only [SharedLayout.nodeValueBase, SharedLayout.nodeMarkerBase]; omega)]
    exact finalTable node
  have assignmentTable : ∀ channel : Channel n,
      final.heap[layout.channelValueBase + channel.val]? = some (boolWord width (assignment channel)) := by
    intro channel
    rw [lowerFrame _ (by
      have valid := channel.isLt; have dimension := dimensions.2
      simp only [SharedLayout.channelValueBase, SharedLayout.nodeMarkerBase]; omega)]
    exact finalChannels channel
  have finalOutput : final.output =
      boolWord width (graph.eval assignment (graph.roots.get slot)) :: initial.output := by
    rw [backOutput, emitOutput, resetOutput, output]
  have successor : OrderedRootInvariant graph layout
      (ForestIndexedOperands.cacheHeap width caller rows roots) assignment base
      (caller.size + (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards rows).length)) (slot.val + 1) callerStack callerOutput final := by
    have visitedBound : slot.val + 1 ≤ graph.roots.length := by have valid := slot.isLt; omega
    refine {
      visitedBound := visitedBound,
      stored := finalStored, memo := finalMemo, assignmentTable := assignmentTable,
      count := backCount, cursor := backCursor, position := backPosition, running := backRunning,
      stack := backStack, output := ?_ }
    rw [finalOutput, invariant.output]
    simpa only [List.get_eq_getElem] using emitted_prefix_successor graph assignment slot.val slot.isLt callerOutput
  have warmLive : warm.liveWords = initial.liveWords + 2 := by
    simp only [State.liveWords, allocation, invariant.stored.allocation, stack, output,
      List.length_cons]
    omega
  have resetLive : reset.liveWords = warm.liveWords := by
    simp only [State.liveWords, resetAllocation, allocation, resetStack, resetOutput]
  have emittedLive : emitted.liveWords = initial.liveWords + 3 := by
    have emits : emitted.liveWords = reset.liveWords + 1 := by
      simp only [State.liveWords, emitHeap, emitStack, emitOutput, List.length_cons]
      omega
    rw [emits, resetLive, warmLive] <;> omega
  have rootWeight : labels.length ≤ freshWeight graph logical.completed :=
    produced_channel_charge graph logical (graph.roots.get slot) labels rootDone labelsUnique scope
  have nodeWeight := produced_node_charge graph logical.completed
  have joined := ((warmTrace.append resetTrace).append emitTrace).append backTrace
  refine ⟨final, logical, labels,
    warmTicks + (12 * logical.completed.length + 9 * labels.length + 12) + 4 + 6,
    max (max (max warmPeak warm.liveWords) (reset.liveWords + 1)) emitted.liveWords,
    joined, ?_, ?_, cone, scope, successor⟩
  · omega
  · rw [resetLive, warmLive, emittedLive]
    omega

def coneWeight (graph : DAG n) (root : Fin graph.nodeCount) : Nat :=
  ∑ node ∈ graph.cone root, localNodeWeight graph node

private theorem produced_weight_eq (graph : DAG n) (logical : DFSState graph)
    (root : Fin graph.nodeCount) (cone : logical.completed.toFinset = graph.cone root) :
    freshWeight graph logical.completed = coneWeight graph root := by
  unfold freshWeight coneWeight
  rw [← List.sum_toFinset (localNodeWeight graph) logical.completedUnique, cone]

private theorem ordered_root_suffix (program : Program width 8)
    (graph : DAG n) (layout : SharedLayout) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (physical : CodeAt8 program base (orderedRootCode width base caller rows roots layout))
    (codeFits : base + 298 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (assignment : Assignment n) (callerStack callerOutput : List (Word width))
    (remaining : List (Fin graph.nodeCount)) (visited : Nat)
    (tailEq : remaining = graph.roots.drop visited)
    (initial : State width 8)
    (invariant : OrderedRootInvariant graph layout
      (ForestIndexedOperands.cacheHeap width caller rows roots) assignment base
      (caller.size + (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards rows).length)) visited callerStack callerOutput initial)
    (countFits : graph.roots.length < 2 ^ width) :
    ∃ (final : State width 8) (ticks peak : Nat), Execution program initial final ticks peak ∧
      ticks ≤ 113 * (remaining.map (coneWeight graph)).sum + 51 * remaining.length + 2 ∧
      peak ≤ initial.liveWords + 3 * graph.nodeCount + remaining.length + 4 ∧
      TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
        final (emptyDFS graph) [] ∧
      (∃ vals : Fin graph.nodeCount → Bool, ∀ node,
        final.heap[layout.nodeValueBase + node.val]? = some (boolWord width (vals node))) ∧
      (∀ channel : Channel n, final.heap[layout.channelValueBase + channel.val]? =
        some (boolWord width (assignment channel))) ∧
      final.stack = callerStack ∧
      final.output = (graph.roots.map (fun node => boolWord width (graph.eval assignment node))).reverse ++ callerOutput ∧
      final.pc = word width (base + 298) ∧ final.halted = true := by
  have sections := ordered_root_sections program base caller rows roots layout physical
  induction remaining generalizing visited initial with
  | nil =>
      have lengthEq := congrArg List.length tailEq
      simp only [List.length_nil, List.length_drop] at lengthEq
      have visitedEq : visited = graph.roots.length := by
        have valid := invariant.visitedBound
        omega
      have testAt : program[base]? = some (.branchZero 4 (word width (base + 297))) := by
        simpa [rootPrefixCode] using sections.prefixCode ⟨0, by decide⟩
      obtain ⟨final, trace, heap, stack, output, regs, position, halted⟩ :=
        root_empty_halt program initial base (base + 297) testAt sections.doneCode
          invariant.position invariant.running (by omega) (by omega)
          (by simpa only [visitedEq, Nat.sub_self] using invariant.count)
      have stored := traversal_same_heap graph layout
          (ForestIndexedOperands.cacheHeap width caller rows roots) initial final (emptyDFS graph) []
          invariant.stored heap (congrFun regs 7) (congrFun regs 2) (congrFun regs 3)
      refine ⟨final, 2, initial.liveWords, trace, ?_, ?_, stored, ?_, ?_,
        stack.trans invariant.stack, ?_, ?_, halted⟩
      · simp
      · omega
      · rw [heap]; exact invariant.memo
      · rw [heap]; exact invariant.assignmentTable
      · rw [output, invariant.output, visitedEq, List.take_length]
      · simpa only [Nat.add_assoc, Nat.reduceAdd] using position
  | cons node rest ih =>
      have lengthEq := congrArg List.length tailEq
      simp only [List.length_cons, List.length_drop] at lengthEq
      have valid : visited < graph.roots.length := by omega
      have split := List.drop_eq_getElem_cons valid
      have exactTail : node :: rest = graph.roots[visited] :: graph.roots.drop (visited + 1) :=
        tailEq.trans split
      have headEq : node = graph.roots[visited] := (List.cons.inj exactTail).1
      have restEq : rest = graph.roots.drop (visited + 1) := (List.cons.inj exactTail).2
      let slot : Fin graph.roots.length := ⟨visited, valid⟩
      obtain ⟨next, logical, labels, firstTicks, firstPeak, firstTrace, firstTime, firstSpace,
          cone, scope, successor⟩ :=
        ordered_root_iteration program graph layout caller rows roots base matched heads rootMatches
          sourceSize physical codeFits storageFits assignment slot callerStack callerOutput initial invariant countFits
      have nodeEq : graph.roots.get slot = node := by
        simpa only [slot, List.get_eq_getElem] using headEq.symm
      have weightEq : freshWeight graph logical.completed = coneWeight graph node := by
        rw [produced_weight_eq graph logical _ cone, nodeEq]
      rw [weightEq] at firstTime
      have nodeCountBound : logical.completed.length ≤ graph.nodeCount := by
        simpa only [Fintype.card_fin] using logical.completedUnique.length_le_card
      have nextLive : next.liveWords = initial.liveWords + 1 := by
        have heapSize := successor.stored.allocation
        have initialSize := invariant.stored.allocation
        have outputSize := congrArg List.length successor.output
        have initialOutputSize := congrArg List.length invariant.output
        simp only [List.length_append, List.length_reverse, List.length_map,
          List.length_take] at outputSize initialOutputSize
        simp only [State.liveWords, heapSize, initialSize, successor.stack, invariant.stack]
        have visitedBound : visited + 1 ≤ graph.roots.length := by omega
        rw [Nat.min_eq_left visitedBound] at outputSize
        rw [Nat.min_eq_left (by omega)] at initialOutputSize
        omega
      obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, finalStored,
          finalMemo, finalAssignment, finalStack, finalOutput, finalPosition, finalHalted⟩ :=
        ih (visited + 1) restEq next successor
      refine ⟨final, firstTicks + restTicks, max firstPeak restPeak,
        firstTrace.append restTrace, ?_, ?_, finalStored, finalMemo, finalAssignment,
        finalStack, finalOutput, finalPosition, finalHalted⟩
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
      · rw [nextLive] at restSpace
        simp only [List.length_cons]
        omega

private def coldLowCode (width : Nat) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n) : Code width :=
  UniformDAGResources.code width n rows roots assignment ++ Initialize.code (word width 0) (scratchWords graph)

private theorem cold_low_execution (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (assignment : Assignment n) (suffix output : List (Word width))
    (address loaded temporary : Word width)
    (codeFits : (coldLowCode width graph rows roots assignment).length < 2 ^ width)
    (storageFits : (sparseLayout width graph rows roots).storageEnd < 2 ^ width) :
    ∃ (final : State width 4) (ticks peak : Nat),
      Execution (coldLowCode width graph rows roots assignment).toArray
        ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
          ((ForestIndexedOperands.inputPacket n 0 rows roots).map (word width) ++
            List.ofFn (fun channel => boolWord width (assignment channel)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 91 * graph.countedSize + 37 ∧
      peak ≤ 10 * graph.countedSize + 16 + suffix.length + output.length ∧
      final.heap =
        ForestInputPrefixStored.evaluationHeap (UniformDAGRun.packetHeaderHeap width n rows roots)
          rows roots assignment (graph.evalTable assignment) ++
            (List.replicate (scratchWords graph) (word width 0)).toArray ∧
      final.stack = suffix ∧ final.output = output ∧
      final.pc = word width (159 + 2 * n + 2 * scratchWords graph) ∧ final.halted = false := by
  let program := (coldLowCode width graph rows roots assignment).toArray
  have whole : BlockAt program 0 (coldLowCode width graph rows roots assignment) := by
    intro offset bound
    simp only [program, Nat.zero_add, List.getElem?_toArray]
  have denseBlock := BlockAt.prefix program 0
    (UniformDAGResources.code width n rows roots assignment)
    (Initialize.code (word width 0) (scratchWords graph)) whole
  have scratchBlock := BlockAt.suffix program 0
    (UniformDAGResources.code width n rows roots assignment)
    (Initialize.code (word width 0) (scratchWords graph)) whole
  have sourceBlock := BlockAt.prefix program 0 (ForestInputMetadata.fullCode width 0)
    (InputLoad.code n ++ UniformDAGLoop.code width (33 + 2 * n) 1
      (UniformDAGTypedNode.layout (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots assignment)) denseBlock
  have later := BlockAt.suffix program 0 (ForestInputMetadata.fullCode width 0)
    (InputLoad.code n ++ UniformDAGLoop.code width (33 + 2 * n) 1
      (UniformDAGTypedNode.layout (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots assignment)) denseBlock
  simp only [ForestInputMetadata.fullCode_length, Nat.zero_add] at later
  have channelBlock := BlockAt.prefix program 33 (InputLoad.code n) _ later
  have evaluatorBlock := BlockAt.suffix program 33 (InputLoad.code n) _ later
  simp only [InputLoad.code_length] at evaluatorBlock
  have denseFits : 0 + 33 + 2 * n + 126 < 2 ^ width := by
    simp only [coldLowCode, List.length_append, UniformDAGResources.code_length,
      Initialize.code_length] at codeFits
    omega
  have room : (ForestIndexedOperands.cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots)
      rows roots).size + n + graph.nodeCount ≤ 2 ^ width := by
    have layoutSize : (sparseLayout width graph rows roots).storageEnd =
        (ForestIndexedOperands.cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots)
          rows roots).size + 3 * n + 4 * graph.nodeCount + 2 := by
      simp only [sparseLayout, SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
        SharedLayout.nodeMarkerBase]
      omega
    rw [layoutSize] at storageFits
    omega
  obtain ⟨evaluated, denseTicks, densePeak, denseTrace, denseTime, denseSpace,
      denseHeap, denseStack, denseOutput, densePosition, denseRunning⟩ :=
    UniformDAGRun.cold_execution program graph rows roots matched heads rootMatches assignment suffix output
      address loaded temporary 0 denseFits room sourceBlock channelBlock evaluatorBlock
  have extendedRoom : evaluated.heap.size + scratchWords graph ≤ 2 ^ width := by
    rw [denseHeap]
    simp only [ForestInputPrefixStored.evaluationHeap_size, scratchWords]
    have layoutSize : (sparseLayout width graph rows roots).storageEnd =
        (ForestIndexedOperands.cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots)
          rows roots).size + 3 * n + 4 * graph.nodeCount + 2 := by
      simp only [sparseLayout, SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
        SharedLayout.nodeMarkerBase]
      omega
    rw [layoutSize] at storageFits
    omega
  simp only [UniformDAGResources.code_length, Nat.zero_add] at scratchBlock
  obtain ⟨final, scratchTrace, finalHeap, finalStack, finalOutput, finalPosition, finalRunning⟩ :=
    Initialize.code_execution program evaluated (word width 0) (159 + 2 * n) (scratchWords graph)
      (by convert densePosition using 1 <;> congr 1 <;> omega) denseRunning
      (by simpa only [coldLowCode, List.length_append, UniformDAGResources.code_length,
        Initialize.code_length] using codeFits) extendedRoom scratchBlock
  have evaluatedLive : evaluated.liveWords =
      10 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        n + graph.nodeCount + suffix.length + output.length := by
    rw [State.liveWords, denseHeap, denseStack, denseOutput]
    simp only [ForestInputPrefixStored.evaluationHeap_size, ForestIndexedOperands.cacheHeap_size,
      UniformDAGRun.packetHeaderHeap_size]
    obtain ⟨children, guards⟩ := ForestIndexedOperands.matched_incidence_lengths graph rows matched
    have rootLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
    rw [matched.length_eq, children, guards, rootLength]
    omega
  refine ⟨final, denseTicks + 2 * scratchWords graph,
    max densePeak (evaluated.liveWords + scratchWords graph), denseTrace.append scratchTrace,
    ?_, ?_, ?_, finalStack.trans denseStack, finalOutput.trans denseOutput, finalPosition, finalRunning⟩
  · have counted := graph.countedSize_eq
    simp only [scratchWords]
    omega
  · have counted := graph.countedSize_eq
    rw [evaluatedLive]
    simp only [scratchWords]
    omega
  · rw [finalHeap, denseHeap]

private def reuseStartupCode (width count cursor : Nat) : Program width 8 := #[
  .constant 2 (word width 0), .constant 3 (word width 1), .constant 7 (word width 0),
  .constant 4 (word width count), .constant 6 (word width cursor)]

private theorem reuse_startup_execution (program : Program width 8) (initial : State width 8)
    (base count cursor : Nat)
    (physical : ∀ phase : Fin 5, program[base + phase.val]? = (reuseStartupCode width count cursor)[phase.val]?)
    (position : initial.pc = word width base) (running : initial.halted = false)
    (fits : base + 5 < 2 ^ width) :
    ∃ final, Execution program initial final 5 initial.liveWords ∧
      final.heap = initial.heap ∧ final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧ final.reg 7 = word width 0 ∧
      final.reg 4 = word width count ∧ final.reg 6 = word width cursor ∧
      final.pc = word width (base + 5) ∧ final.halted = false := by
  let s1 := initial.advance.put 2 (word width 0)
  let s2 := s1.advance.put 3 (word width 1)
  let s3 := s2.advance.put 7 (word width 0)
  let s4 := s3.advance.put 4 (word width count)
  let final := s4.advance.put 6 (word width cursor)
  have p1 : s1.pc = word width (base + 1) := by
    simp only [s1, State.advance, State.put, position]
    rw [show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (base + 2) := by
    simp only [s2, State.advance, State.put, p1]
    rw [show (word width (base + 1)).val = base + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (base + 3) := by
    simp only [s3, State.advance, State.put, p2]
    rw [show (word width (base + 2)).val = base + 2 from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (base + 4) := by
    simp only [s4, State.advance, State.put, p3]
    rw [show (word width (base + 3)).val = base + 3 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program initial = some s1 := by
    rw [fetched program initial base (.constant 2 (word width 0)) position (by omega)
      (by simpa [reuseStartupCode] using physical ⟨0, by decide⟩)]
    simp [step, s1, running]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.constant 3 (word width 1)) p1 (by omega)
      (by simpa [reuseStartupCode] using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.constant 7 (word width 0)) p2 (by omega)
      (by simpa [reuseStartupCode] using physical ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.constant 4 (word width count)) p3 (by omega)
      (by simpa [reuseStartupCode] using physical ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.advance, State.put, running]
  have t4 : programStep program s4 = some final := by
    rw [fetched program s4 (base + 4) (.constant 6 (word width cursor)) p4 (by omega)
      (by simpa [reuseStartupCode] using physical ⟨4, by decide⟩)]
    simp [step, final, s4, s3, s2, s1, State.advance, State.put, running]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.cons t4 (Execution.refl (p := program) final)))))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, running⟩
  · simpa [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Nat.max_self] using trace
  · simp [final, s4, s3, s2, s1, State.advance, State.put]
  · simp [final, s4, s3, s2, s1, State.advance, State.put]
  · simp [final, s4, s3, s2, s1, State.advance, State.put]
  · simp [final, s4, s3, s2, s1, State.advance, State.put]
  · simp [final, s4, s3, s2, s1, State.advance, State.put]
  · change word width (s4.pc.val + 1) = word width (base + 5)
    rw [p4, show (word width (base + 4)).val = base + 4 from Nat.mod_eq_of_lt (by omega)]

private theorem cold_scratch_invariant (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (assignment : Assignment n)
    (state : State width 8)
    (physical : state.heap =
      ForestInputPrefixStored.evaluationHeap (UniformDAGRun.packetHeaderHeap width n rows roots)
        rows roots assignment (graph.evalTable assignment) ++
          (List.replicate (scratchWords graph) (word width 0)).toArray)
    (depth : state.reg 7 = word width 0) (zero : state.reg 2 = word width 0)
    (one : state.reg 3 = word width 1) :
    TraversalStored graph (sparseLayout width graph rows roots)
      (ForestIndexedOperands.cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots)
      state (emptyDFS graph) [] ∧
    (∀ node : Fin graph.nodeCount,
      state.heap[(sparseLayout width graph rows roots).nodeValueBase + node.val]? =
        some (boolWord width (graph.evalTable assignment node))) ∧
    (∀ channel : Channel n,
      state.heap[(sparseLayout width graph rows roots).channelValueBase + channel.val]? =
        some (boolWord width (assignment channel))) := by
  let caller := UniformDAGRun.packetHeaderHeap width n rows roots
  let layout := sparseLayout width graph rows roots
  let source := ForestIndexedOperands.cacheHeap width caller rows roots
  let evaluated := ForestInputPrefixStored.evaluationHeap caller rows roots assignment (graph.evalTable assignment)
  have evaluatedSize : evaluated.size = layout.nodeMarkerBase := by
    simp only [evaluated, ForestInputPrefixStored.evaluationHeap_size, layout, sparseLayout,
      SharedLayout.nodeMarkerBase, caller]
  have physicalHeap : state.heap = evaluated ++
      (List.replicate (scratchWords graph) (word width 0)).toArray := physical
  have allocation : state.heap.size = layout.storageEnd := by
    rw [physical]
    simp only [Array.size_append, List.size_toArray, List.length_replicate,
      ForestInputPrefixStored.evaluationHeap_size, scratchWords, layout, sparseLayout,
      SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega
  have scratchCell : ∀ address, layout.nodeMarkerBase ≤ address → address < layout.storageEnd →
      state.heap[address]? = some (word width 0) := by
    intro address after before
    rw [physicalHeap, Array.getElem?_append_right (by rw [evaluatedSize]; exact after)]
    simp only [List.getElem?_toArray, List.getElem?_replicate]
    have sizeEq : layout.storageEnd = evaluated.size + scratchWords graph := by
      simp only [evaluatedSize, layout, sparseLayout, SharedLayout.storageEnd,
        SharedLayout.nodeCountSlot, scratchWords]
      omega
    rw [ite_eq_left (by omega)]
  have retained : CachePrefix state.heap source := by
    intro address
    have sourceBound := address.isLt
    have bound : address.val < evaluated.size := by
      simp only [evaluated, ForestInputPrefixStored.evaluationHeap_size]
      change address.val < source.size + n + graph.nodeCount
      omega
    rw [physicalHeap, Array.getElem?_append_left bound, Array.getElem?_eq_getElem bound]
    congr 1
    exact UniformDAGSource.cache_cell caller rows roots assignment (graph.evalTable assignment)
      address.val sourceBound
  have stored : TraversalStored graph layout source state (emptyDFS graph) [] := by
    refine {
      sourceRetained := retained
      nodeDimension := rfl
      channelDimension := rfl
      allocation := allocation
      completed := ?_
      channelLedger := ?_
      channelsUnique := List.nodup_nil
      flags := ?_
      completedScope := ?_
      depth := depth
      zero := zero
      one := one }
    · refine ⟨?_, ?_, ?_⟩
      · simpa only [emptyDFS, List.length_nil] using scratchCell layout.nodeCountSlot
          (by simp only [SharedLayout.nodeCountSlot]; omega) (by simp only [SharedLayout.storageEnd]; omega)
      · intro position; exact Fin.elim0 position
      · intro position; exact Fin.elim0 position
    · refine ⟨?_, ?_, ?_⟩
      · simpa only [List.length_nil] using scratchCell layout.channelCountSlot
          (by simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot]; omega)
          (by simp only [SharedLayout.channelCountSlot, SharedLayout.storageEnd]; omega)
      · intro position; exact Fin.elim0 position
      · intro channel
        simpa only [List.not_mem_nil, ite_false] using scratchCell
          (layout.channelMarkerBase + channel.val)
          (by simp only [SharedLayout.channelMarkerBase]; omega)
          (by have valid := channel.isLt
              simp only [layout, sparseLayout, SharedLayout.channelMarkerBase,
                SharedLayout.storageEnd, SharedLayout.nodeCountSlot]; omega)
    · intro node
      simpa only [emptyDFS, List.not_mem_nil, or_false, ite_false] using scratchCell
        (layout.nodeMarkerBase + node.val) (by omega)
        (by have valid := node.isLt
            simp only [layout, sparseLayout, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]; omega)
    · intro node member
      simp only [emptyDFS, List.not_mem_nil] at member
  refine ⟨stored, ?_, ?_⟩
  · intro node
    have bound : layout.nodeValueBase + node.val < evaluated.size := by
      have valid := node.isLt
      simp only [evaluatedSize, layout, sparseLayout, SharedLayout.nodeValueBase,
        SharedLayout.nodeMarkerBase]
      omega
    rw [physicalHeap, Array.getElem?_append_left bound, Array.getElem?_eq_getElem bound]
    congr 1
    simpa only [evaluated, ForestInputPrefixStored.evaluationHeap, caller, layout, sparseLayout,
      SharedLayout.nodeValueBase, ForestInputPrefixStored.channelHeap_size] using
      ForestInputStored.value_cell (ForestInputPrefixStored.channelHeap caller rows roots assignment)
        (graph.evalTable assignment) node
  · intro channel
    have bound : layout.channelValueBase + channel.val < evaluated.size := by
      have valid := channel.isLt
      simp only [evaluatedSize, layout, sparseLayout, SharedLayout.channelValueBase,
        SharedLayout.nodeMarkerBase]
      omega
    rw [physicalHeap, Array.getElem?_append_left bound, Array.getElem?_eq_getElem bound]
    congr 1
    simpa only [layout, sparseLayout, SharedLayout.channelValueBase] using
      UniformDAGSource.channel_cell caller rows roots assignment (graph.evalTable assignment) channel

def coneIncidenceSize (graph : DAG n) (root : Fin graph.nodeCount) : Nat :=
  ∑ node ∈ graph.cone root,
    (1 + (graph.node node).children.length + (graph.node node).guardLabels.length)

/-- Every repeated original child/guard occurrence contributes to its cone's
charge. Declared ambient channels contribute only to the once-only prefix. -/
private theorem cone_weight_charge (graph : DAG n) (root : Fin graph.nodeCount) :
    coneWeight graph root ≤ 2 * coneIncidenceSize graph root := by
  unfold coneWeight coneIncidenceSize
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro node member
  exact local_weight_le graph node

private theorem roots_weight_charge (graph : DAG n) :
    (graph.roots.map (coneWeight graph)).sum ≤
      2 * (graph.roots.map (coneIncidenceSize graph)).sum := by
  have allLists : ∀ nodes : List (Fin graph.nodeCount),
      (nodes.map (coneWeight graph)).sum ≤ 2 * (nodes.map (coneIncidenceSize graph)).sum := by
    intro nodes
    induction nodes with
    | nil => simp
    | cons node rest ih =>
        simp only [List.map_cons, List.sum_cons] at *
        have own := cone_weight_charge graph node
        omega
  exact allLists graph.roots

attribute [local irreducible] orderedRootCode coldReuseCode coldLowCode

/-- One resident program loads and evaluates the source once, initializes the
shared sparse scratch once, and then executes every original root occurrence
through DFS, warm postorder evaluation, touched reset, and fetched emission. -/
theorem cold_ordered_execution (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (assignment : Assignment n)
    (suffix output : List (Word (reuseWidth graph)))
    (address loaded temporary : Word (reuseWidth graph)) (saved : Fin 8 → Word (reuseWidth graph)) :
    ∃ (final : State (reuseWidth graph) 8) (ticks peak : Nat),
      Execution (coldReuseCode (reuseWidth graph) graph rows roots assignment)
        (widenState
          ((ForestCounter.counterState (#[] : Array (Word (reuseWidth graph))) 0 address loaded temporary).frame
            ((ForestIndexedOperands.inputPacket n 0 rows roots).map (word (reuseWidth graph)) ++
              List.ofFn (fun channel => boolWord (reuseWidth graph) (assignment channel)) ++ suffix) output)
          saved)
        final ticks peak ∧
      ticks ≤ 91 * graph.countedSize +
        113 * (graph.roots.map (coneWeight graph)).sum + 51 * graph.roots.length + 44 ∧
      peak + programWords (coldReuseCode (reuseWidth graph) graph rows roots assignment) ≤
        38 * graph.countedSize + 1884 + suffix.length + output.length ∧
      TraversalStored graph (sparseLayout (reuseWidth graph) graph rows roots)
        (ForestIndexedOperands.cacheHeap (reuseWidth graph)
          (UniformDAGRun.packetHeaderHeap (reuseWidth graph) n rows roots) rows roots)
        final (emptyDFS graph) [] ∧
      final.stack = suffix ∧
      final.output = (graph.roots.map (fun node => boolWord (reuseWidth graph)
        (graph.eval assignment node))).reverse ++ output ∧
      final.halted = true := by
  let width := reuseWidth graph
  let caller := UniformDAGRun.packetHeaderHeap width n rows roots
  let layout := sparseLayout width graph rows roots
  let low := (coldLowCode width graph rows roots assignment).toArray
  let program := coldReuseCode width graph rows roots assignment
  let outer := low.size + 5
  let rootStart := caller.size +
    (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards rows).length)
  have capacity := reuse_capacity graph
  have storageFits := reuse_storage_fits graph rows roots matched rootMatches
  have codeFits := reuse_code_fits graph rows roots assignment
  have lowEq : low = UniformDAGResources.program width n rows roots assignment ++
      (Initialize.code (word width 0) (scratchWords graph)).toArray := by
    simp only [low, coldLowCode, List.append_toArray, UniformDAGResources.program]
  have programEq : program = widenProgram low ++
      (reuseStartupCode width roots.length rootStart ++ orderedRootCode width outer caller rows roots layout) := by
    simp only [program, coldReuseCode, ← lowEq, outer, caller, layout, rootStart,
      reuseStartupCode, Array.append_assoc, Nat.add_assoc]
  have resident : CodeAt8 program 0 (widenProgram low ++
      (reuseStartupCode width roots.length rootStart ++ orderedRootCode width outer caller rows roots layout)) := by
    intro phase
    have same := congrArg (fun code => code[phase.val]?) programEq
    simpa only [Nat.zero_add] using same
  have lowAt := codeAt8_prefix program 0 (widenProgram low) _ resident
  have later := codeAt8_suffix program 0 (widenProgram low) _ resident
  have widenSize : (widenProgram low).size = low.size := by simp only [widenProgram, Array.size_map]
  simp only [widenSize, Nat.zero_add] at later
  have startupAt := codeAt8_prefix program low.size (reuseStartupCode width roots.length rootStart) _ later
  have driverAt := codeAt8_suffix program low.size (reuseStartupCode width roots.length rootStart) _ later
  have startupSize : (reuseStartupCode width roots.length rootStart).size = 5 := rfl
  simp only [startupSize] at driverAt
  have fullSize : program.size = low.size + 5 + 298 := by
    rw [programEq]
    simp only [Array.size_append, widenSize, startupSize, orderedRootCode_size]
  have lowFits : (coldLowCode width graph rows roots assignment).length < 2 ^ width := by
    have codeBound : program.size < 2 ^ width := codeFits
    rw [fullSize] at codeBound
    simpa only [low, List.size_toArray] using (by omega : low.size < 2 ^ width)
  obtain ⟨cold, coldTicks, coldPeak, coldTrace, coldTime, coldSpace,
      coldHeap, coldStack, coldOutput, coldPosition, coldRunning⟩ :=
    cold_low_execution graph rows roots matched heads rootMatches assignment suffix output
      address loaded temporary lowFits storageFits
  have widenedPhysical : ∀ phase : Fin low.size, program[0 + phase.val]? =
      some (widenInstruction low[phase.val]) := by
    intro phase
    have cell := lowAt ⟨phase.val, by rw [widenSize]; exact phase.isLt⟩
    simpa only [widenProgram, Array.getElem?_map, Array.getElem?_eq_getElem phase.isLt,
      Option.map_some, Nat.zero_add] using cell
  have lifted := widen_handler_execution program 0 low widenedPhysical _ _ coldTicks coldPeak
    (by simpa only [Array.replicate_zero, Array.empty_append, low] using coldTrace) coldRunning saved
  have lowSize : low.size = 159 + 2 * n + 2 * scratchWords graph := by
    simp only [low, coldLowCode, List.size_toArray, List.length_append,
      UniformDAGResources.code_length, Initialize.code_length]
  have startupPC : (widenState cold saved).pc = word width low.size := by
    simpa only [widenState, lowSize] using coldPosition
  obtain ⟨ready, startupTrace, readyHeap, readyStack, readyOutput, readyZero,
      readyOne, readyDepth, readyCount, readyCursor, readyPosition, readyRunning⟩ :=
    reuse_startup_execution program (widenState cold saved) low.size roots.length rootStart startupAt
      startupPC coldRunning (by have bound : program.size < 2 ^ width := codeFits; rw [fullSize] at bound; omega)
  have physicalHeap : ready.heap =
      ForestInputPrefixStored.evaluationHeap caller rows roots assignment (graph.evalTable assignment) ++
        (List.replicate (scratchWords graph) (word width 0)).toArray := by
    rw [readyHeap]
    exact coldHeap
  obtain ⟨stored, table, assignmentTable⟩ :=
    cold_scratch_invariant graph rows roots assignment ready physicalHeap readyDepth readyZero readyOne
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  have rootCountFits : graph.roots.length < 2 ^ width := by
    have capacityWidth : 4096 * (graph.countedSize + 1) < 2 ^ width := capacity
    have counted := graph.countedSize_eq
    omega
  have readyInvariant : OrderedRootInvariant graph layout
      (ForestIndexedOperands.cacheHeap width caller rows roots) assignment outer rootStart 0 suffix output ready := by
    refine {
      visitedBound := Nat.zero_le _
      stored := stored
      memo := ⟨graph.evalTable assignment, table⟩
      assignmentTable := assignmentTable
      count := ?_
      cursor := ?_
      position := readyPosition
      running := readyRunning
      stack := ?_
      output := ?_ }
    · simpa only [rootLength, Nat.sub_zero] using readyCount
    · simpa only [Nat.add_zero] using readyCursor
    · exact readyStack.trans coldStack
    · simpa only [List.take_zero, List.map_nil, List.reverse_nil, List.nil_append] using
        readyOutput.trans coldOutput
  obtain ⟨final, rootTicks, rootPeak, rootTrace, rootTime, rootSpace,
      finalStored, finalMemo, finalAssignment, finalStack, finalOutput, finalPosition, finalHalted⟩ :=
    ordered_root_suffix program graph layout caller rows roots outer matched heads rootMatches rfl driverAt
      (by have bound : program.size < 2 ^ width := codeFits; rw [fullSize] at bound; exact bound)
      storageFits assignment suffix output graph.roots 0 (by simp only [List.drop_zero]) ready readyInvariant rootCountFits
  have readyLive : ready.liveWords ≤ 10 * graph.countedSize + 16 + suffix.length + output.length := by
    have storageBound := sparseLayout_storage_le width graph rows roots matched rootMatches
    simp only [State.liveWords, stored.allocation, readyInvariant.stack, readyInvariant.output,
      List.take_zero, List.map_nil, List.reverse_nil, List.nil_append]
    omega
  have denseLive : (widenState cold saved).liveWords = ready.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have rootPeakBound : rootPeak ≤ 14 * graph.countedSize + 20 + suffix.length + output.length := by
    have counted := graph.countedSize_eq
    omega
  have residentWords : programWords program ≤ 24 * graph.countedSize + 1864 := by
    have counted := graph.countedSize_eq
    simp only [programWords, program, coldReuseCode_size]
    omega
  refine ⟨final, coldTicks + 5 + rootTicks,
      max (max (coldPeak + 4) (widenState cold saved).liveWords) rootPeak,
      (lifted.append startupTrace).append rootTrace, ?_, ?_, finalStored, finalStack, finalOutput, finalHalted⟩
  · omega
  · change max (max (coldPeak + 4) (widenState cold saved).liveWords) rootPeak +
      programWords program ≤ 38 * graph.countedSize + 1884 + suffix.length + output.length
    rw [denseLive]
    omega

/-- The incidence form of the complete program bound separates its once-only
source/ambient preprocessing from each original root occurrence's cone work. -/
theorem cold_sparse_execution (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (assignment : Assignment n)
    (suffix output : List (Word (reuseWidth graph)))
    (address loaded temporary : Word (reuseWidth graph)) (saved : Fin 8 → Word (reuseWidth graph)) :
    ∃ (final : State (reuseWidth graph) 8) (ticks peak : Nat),
      Execution (coldReuseCode (reuseWidth graph) graph rows roots assignment)
        (widenState
          ((ForestCounter.counterState (#[] : Array (Word (reuseWidth graph))) 0 address loaded temporary).frame
            ((ForestIndexedOperands.inputPacket n 0 rows roots).map (word (reuseWidth graph)) ++
              List.ofFn (fun channel => boolWord (reuseWidth graph) (assignment channel)) ++ suffix) output)
          saved)
        final ticks peak ∧
      ticks ≤ 142 * graph.countedSize +
        226 * (graph.roots.map (coneIncidenceSize graph)).sum + 44 ∧
      peak + programWords (coldReuseCode (reuseWidth graph) graph rows roots assignment) ≤
        38 * graph.countedSize + 1884 + suffix.length + output.length ∧
      TraversalStored graph (sparseLayout (reuseWidth graph) graph rows roots)
        (ForestIndexedOperands.cacheHeap (reuseWidth graph)
          (UniformDAGRun.packetHeaderHeap (reuseWidth graph) n rows roots) rows roots)
        final (emptyDFS graph) [] ∧
      final.stack = suffix ∧
      final.output = (graph.roots.map (fun node => boolWord (reuseWidth graph)
        (graph.eval assignment node))).reverse ++ output ∧
      final.halted = true := by
  obtain ⟨final, ticks, peak, trace, time, space, stored, stack, finalOutput, halted⟩ :=
    cold_ordered_execution graph rows roots matched heads rootMatches assignment suffix output
      address loaded temporary saved
  have weighted := roots_weight_charge graph
  have counted := graph.countedSize_eq
  exact ⟨final, ticks, peak, trace, by omega, space, stored, stack, finalOutput, halted⟩

end Controller.Cost.SparseConeReuse
