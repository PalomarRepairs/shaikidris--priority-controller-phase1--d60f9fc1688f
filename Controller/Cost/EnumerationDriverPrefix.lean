module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverInitial

@[expose] public section

/-! Exact runtime prefix states and their local mask-update refinements. -/
namespace Controller.Cost.EnumerationDriverPrefix
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

structure Ready (parameters : Parameters) (packet : Array (Word width))
    (depth cursor : Nat) (partialSet : Finset (Fin parameters.channels)) (state : State width 8) : Prop where
  heap : state.heap = packet ++ (EnumerationMasks.maskList width parameters.buses parameters.bridge.target depth partialSet).toArray
  counter : state.reg 3 = word width cursor
  stack : state.stack = []
  running : state.halted = false

theorem initial_masks (parameters : Parameters) (width : Nat) :
    EnumerationDriverCode.initWords parameters width =
      EnumerationMasks.maskList width parameters.buses parameters.bridge.target 0 ∅ := by
  simp [EnumerationDriverCode.initWords, EnumerationPrefixOracle.masks,
    EnumerationMasks.maskList, fixedTrue, fixedFalse]

/-- The two indexed cells are different, so their machine writes commute. -/
theorem set_cells_comm (parameters : Parameters) (words : List (Word width)) (cursor : Nat) (first second : Word width) :
    (words.set cursor first).set (parameters.channels + cursor) second =
      (words.set (parameters.channels + cursor) second).set cursor first := by
  have positive : 0 < parameters.channels := by have := parameters.bridge.target.isLt; omega
  exact List.set_comm first second (by omega)

/-- Entry to the actual oracle for a free false-child test. The saved cursor is
its parent's depth; the mask words encode the queried depth plus one. -/
theorem false_child_entry (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry call depth : Nat) (packet : Array (Word width)) (partialSet : Finset (Fin parameters.channels))
    (ready : Ready parameters packet depth depth partialSet state) (bounded : Bounded depth partialSet)
    (lower : depth < parameters.channels) (position : state.pc = word width entry)
    (heapFits : state.heap.size < 2 ^ width) (room : entry + 7 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry
      (EnumerationDriverControl.selectCode width (packet.size + parameters.channels) true 1 call)) :
    ∃ final, Execution program state final 7 state.liveWords ∧
      Ready parameters packet (depth + 1) depth partialSet final ∧
      final.pc = word width call ∧ final.reg 5 = word width 1 ∧ final.output = state.output := by
  obtain ⟨final, trace, heap, stack, output, pc, running, cursor, mode⟩ :=
    EnumerationDriverControl.select_execution program state entry parameters.channels depth 1 call packet
      (EnumerationMasks.maskList width parameters.buses parameters.bridge.target depth partialSet) true
      position ready.running ready.counter (by simp only [EnumerationMasks.maskList_length]; omega)
      ready.heap heapFits room present
  refine ⟨final, trace, ⟨?_, cursor, stack.trans ready.stack, running⟩, pc, mode, output⟩
  rw [EnumerationMasks.complete_flag width parameters.buses parameters.bridge.target depth partialSet lower bounded]
  exact heap

/-- Runtime ordering of sibling writes matches the existing D08 mask identity. -/
theorem sibling_mask (parameters : Parameters) (width cursor : Nat) (previous : Finset (Fin parameters.channels))
    (lower : cursor < parameters.channels) (absent : (⟨cursor, lower⟩ : Fin parameters.channels) ∉ previous) :
    ((EnumerationMasks.maskList width parameters.buses parameters.bridge.target (cursor + 1) (fixedTrue (cursor + 1) previous)).set cursor
        (boolWord width true)).set (parameters.channels + cursor) (boolWord width false) =
      EnumerationMasks.maskList width parameters.buses parameters.bridge.target (cursor + 1)
        (insert ⟨cursor, lower⟩ (fixedTrue cursor previous)) := by
  rw [set_cells_comm parameters]
  exact (EnumerationMasks.seek_try width parameters.buses parameters.bridge.target cursor previous lower absent).symm

/-- The forced target is already stored in the baseline; advancing over it
requires no oracle query and inserts the same channel into the semantic prefix. -/
theorem forced_entry (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry descend depth : Nat) (packet : Array (Word width)) (partialSet : Finset (Fin parameters.channels))
    (ready : Ready parameters packet depth depth partialSet state) (bounded : Bounded depth partialSet)
    (lower : depth < parameters.channels) (one : parameters.buses = 1) (target : parameters.bridge.target.val = depth)
    (position : state.pc = word width entry) (fits : depth + 1 < 2 ^ width) (room : entry + 4 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (EnumerationDriverControl.incrementCode width descend)) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      Ready parameters packet (depth + 1) (depth + 1) (insert ⟨depth, lower⟩ partialSet) final ∧
      final.pc = word width descend ∧ final.output = state.output := by
  obtain ⟨final, trace, cursor, heap, stack, output, pc, running, frame⟩ :=
    EnumerationDriverControl.increment_execution program state entry depth descend position ready.running ready.counter fits room present
  have unchanged := EnumerationMasks.forced_skip width parameters.buses parameters.bridge.target depth partialSet lower one target
  have maskEq : EnumerationMasks.maskList width parameters.buses parameters.bridge.target (depth + 1) (insert ⟨depth, lower⟩ partialSet) =
      EnumerationMasks.maskList width parameters.buses parameters.bridge.target depth partialSet := unchanged.resolve_right (fun bad => bad bounded)
  refine ⟨final, trace, ⟨?_, cursor, stack.trans ready.stack, running⟩, pc, output⟩
  rw [maskEq]; exact heap.trans ready.heap

/-- A sibling query follows the hardware's baseline-first write order and saves
its parent's cursor; its mask words encode the tested true sibling. -/
theorem sibling_entry (parameters : Parameters) (program : Program width 8) (state : State width 8)
    (entry call cursor : Nat) (packet : Array (Word width)) (previous : Finset (Fin parameters.channels))
    (lower : cursor < parameters.channels) (absent : (⟨cursor, lower⟩ : Fin parameters.channels) ∉ previous)
    (ready : Ready parameters packet (cursor + 1) cursor (fixedTrue (cursor + 1) previous) state)
    (position : state.pc = word width entry) (heapFits : state.heap.size < 2 ^ width) (room : entry + 11 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (EnumerationDriverControl.pairModeCode width packet.size
      (packet.size + parameters.channels) true false 2 call)) :
    ∃ final, Execution program state final 11 state.liveWords ∧
      Ready parameters packet (cursor + 1) cursor (insert ⟨cursor, lower⟩ (fixedTrue cursor previous)) final ∧
      final.pc = word width call ∧ final.reg 5 = word width 2 ∧ final.output = state.output := by
  obtain ⟨final, trace, heap, stack, output, pc, running, counter, mode⟩ :=
    EnumerationDriverControl.pair_mode_execution program state entry 0 parameters.channels cursor 2 call packet
      (EnumerationMasks.maskList width parameters.buses parameters.bridge.target (cursor + 1) (fixedTrue (cursor + 1) previous)) true false
      position ready.running ready.counter (by simp only [EnumerationMasks.maskList_length]; omega)
      (by simp only [EnumerationMasks.maskList_length]; omega) ready.heap heapFits room (by simpa using present)
  refine ⟨final, trace, ⟨?_, counter, stack.trans ready.stack, running⟩, pc, mode, output⟩
  rw [Nat.zero_add, sibling_mask parameters width cursor previous lower absent] at heap
  exact heap


end Controller.Cost.EnumerationDriverPrefix
