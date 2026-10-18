module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RawTransferLoops
public import Controller.Cost.ForestIndexedOperands
public import Controller.Cost.UniformDAGRun
public import Controller.Cost.ForestZeroCallerWiden
public import Mathlib.Tactic.FinCases
public import Controller.Cost.ForestWeightedIndexed
public import Controller.Cost.CompilerArrayTrace
public import Controller.Cost.ForestZeroSourcePlan
public import Controller.Cost.UniformDAGResources
public import Controller.Cost.Forest

@[expose] public section

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

/-- Descending original root cells are read once. Register four counts retained
roots; pushes produce their original forward order, including duplicate IDs. -/
def code (width entry done : Nat) (healthy : Bool) : Program width 8 :=
  #[.branchZero 2 (word width done), .add 1 1 3, .load 6 1,
    .add 0 6 5, .load 0 0, .branchZero 0 (word width (entry + 8)),
    (if healthy then .push 6 else .add 4 4 3),
    .branchZero 7 (word width (entry + 9)),
    (if healthy then .add 4 4 3 else .push 6),
    .add 2 2 3, .branchZero 7 (word width entry)]

@[simp] theorem code_size (width entry done : Nat) (healthy : Bool) :
    (code width entry done healthy).size = 11 := by cases healthy <;> rfl

def CodeAt (program : Program width 8) (entry done : Nat) (healthy : Bool) : Prop :=
  ∀ phase : Fin 11, program[entry + phase.val]? = (code width entry done healthy)[phase.val]?

/-- The resident cells, rather than an evaluation oracle, determine selection. -/
def selected (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool)
    (roots : List (Word width)) : List (Word width) :=
  roots.filter (fun root => ((heap[valueBase + root.val]?.map (fun value => value.val != 0)).getD false) == healthy)

@[simp] theorem selected_nil (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool) :
    selected heap valueBase healthy [] = [] := rfl

theorem selected_length (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool)
    (roots : List (Word width)) : (selected heap valueBase healthy roots).length ≤ roots.length := by
  exact List.length_filter_le _ _

theorem selected_append (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool)
    (left right : List (Word width)) :
    selected heap valueBase healthy (left ++ right) =
      selected heap valueBase healthy left ++ selected heap valueBase healthy right := by
  exact List.filter_append left right

/-- Source and node-value separation is checked before either indexed read. -/
structure Stored (heap : Array (Word width)) (rootBase valueBase : Nat)
    (roots : List (Word width)) : Prop where
  rootBound : rootBase + roots.length ≤ heap.size
  rootCell : ∀ index : Fin roots.length, heap[rootBase + index.val]? = some roots[index.val]
  valueBound : ∀ root ∈ roots, valueBase + root.val < heap.size
  valueFits : valueBase < 2 ^ width

/-- Loop termination tests the actual remaining-count register before reading
any root or value cell. The empty case costs one fetched instruction. -/
theorem zero_execution (program : Program width 8) (entry done : Nat) (healthy : Bool)
    (state : State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (zero : state.reg 2 = word width 0)
    (room : entry < 2 ^ width) (present : CodeAt program entry done healthy) :
    Execution program state { state.advance with pc := word width done } 1 state.liveWords := by
  have found : program[entry]? = some (.branchZero 2 (word width done)) := by
    simpa [code] using present ⟨0, by decide⟩
  have transition : programStep program state = some { state.advance with pc := word width done } := by
    rw [fetched program state entry _ position room found]
    simp [step, running, zero, word]
  simpa only [State.advance, State.liveWords, Nat.max_self] using
    Execution.cons transition (Execution.refl { state.advance with pc := word width done })

/-- One active iteration's first five instructions read the current original
root ID and then its physical evaluated-value cell. -/
theorem read_execution (program : Program width 8) (entry done : Nat) (healthy : Bool)
    (state : State width 8) (cursor remaining : Nat) (root value : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 11 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorReg : state.reg 1 = word width (cursor + 1))
    (countReg : state.reg 2 = word width (remaining + 1))
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (rootBound : cursor < state.heap.size) (rootCell : state.heap[cursor]? = some root)
    (addressBound : root.val + (state.reg 5).val < state.heap.size)
    (addressFits : root.val + (state.reg 5).val < 2 ^ width)
    (valueCell : state.heap[root.val + (state.reg 5).val]? = some value)
    (present : CodeAt program entry done healthy) :
    let first := state.advance.advance.put 1 (word width cursor)
    let second := first.advance.put 6 root
    let third := second.advance.put 0 (word width (root.val + (state.reg 5).val))
    let final := third.advance.put 0 value
    Execution program state final 5 state.liveWords ∧
      final.pc = word width (entry + 5) ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output := by
  let s1 := state.advance
  let s2 := s1.advance.put 1 (word width cursor)
  let s3 := s2.advance.put 6 root
  let s4 := s3.advance.put 0 (word width (root.val + (state.reg 5).val))
  let s5 := s4.advance.put 0 value
  have addressFitsAt : ∀ offset ≤ 11, entry + offset < 2 ^ width := by
    intro offset bound
    exact lt_of_le_of_lt (Nat.add_le_add_left bound entry) room
  have pc0 : state.pc.val = entry := by rw [position]; exact Nat.mod_eq_of_lt (addressFitsAt 0 (by decide))
  have pc1 : s1.pc = word width (entry + 1) := advance_position state position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using advance_position s1 pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using advance_position s2 pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    simpa [s4, State.put, Nat.add_assoc] using advance_position s3 pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    simpa [s5, State.put, Nat.add_assoc] using advance_position s4 pc4 (by omega)
  have countVal : (state.reg 2).val = remaining + 1 := by rw [countReg]; exact Nat.mod_eq_of_lt countFits
  have cursorVal : (state.reg 1).val = cursor + 1 := by rw [cursorReg]; exact Nat.mod_eq_of_lt cursorFits
  have maskVal : (state.reg 3).val = 2 ^ width - 1 := by rw [maskReg]; exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry _ position (by omega)
      (by simpa [code] using present ⟨0, by decide⟩)]
    simp [step, running, countVal, s1]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) _ pc1 (by omega)
      (by simpa [code] using present ⟨1, by decide⟩)]
    simp only [step, s1, State.advance, running, Bool.false_eq_true, ite_false, cursorVal, maskVal]
    rw [decrement_word]
    simp only [s2, s1, State.advance, running]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) _ pc2 (by omega)
      (by simpa [code] using present ⟨2, by decide⟩)]
    have cursorAt : (s2.reg 1).val = cursor := by simp [s2, State.put, word, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width)]
    have found : state.heap[cursor] = root := by simpa [Array.getElem?_eq_getElem rootBound] using rootCell
    have cursorWord : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
    simp [step, s2, s1, State.advance, State.put, running, cursorWord, rootBound, found, s3]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) _ pc3 (by omega)
      (by simpa [code] using present ⟨3, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running, s4]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) _ pc4 (by omega)
      (by simpa [code] using present ⟨4, by decide⟩)]
    have addressAt : (s4.reg 0).val = root.val + (state.reg 5).val := by simp [s4, State.put, word, Nat.mod_eq_of_lt addressFits]
    have found : state.heap[root.val + (state.reg 5).val] = value := by
      simpa [Array.getElem?_eq_getElem addressBound] using valueCell
    have addressWord : (word width (root.val + (state.reg 5).val)).val = root.val + (state.reg 5).val :=
      Nat.mod_eq_of_lt addressFits
    simp [step, s4, s3, s2, s1, State.advance, State.put, running, addressWord, addressBound, found, s5]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.cons t4 (Execution.refl s5)))))
  refine ⟨?_, pc5, rfl, rfl, rfl⟩
  simpa only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, Nat.max_self] using trace


/-- Changing the root column changes only the fifth global header count. Node
column addresses retain cold origin five, so no child or guard ID is relocated. -/
theorem projected_input_packet (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) :
    ForestIndexedOperands.inputPacket channels 0 rows roots =
      [channels, rows.length, (ForestIndexedOperands.rowChildren rows).length,
        (ForestIndexedOperands.rowGuards rows).length, roots.length] ++
      ForestIndexedOperands.packetPrefix 5 rows ++ roots := by
  rw [ForestIndexedOperands.inputPacket, ForestIndexedOperands.packet_prefix_roots]
  simp only [ForestIndexedOperands.globalHeader, ForestIndexedOperands.countSource_value,
    Nat.zero_add, Nat.zero_add, List.append_assoc]

/-- The descending traversal pushes each retained occurrence before its
already processed suffix. This is the forward filtered list, not a set. -/
theorem selected_stack_append (heap : Array (Word width)) (valueBase : Nat)
    (healthy : Bool) (before after stack : List (Word width)) :
    selected heap valueBase healthy before ++ (selected heap valueBase healthy after ++ stack) =
      selected heap valueBase healthy (before ++ after) ++ stack := by
  rw [selected_append, List.append_assoc]


/-- Header zero is copied after the positive-offset reverse-save block. Its
address comes from the retained zero register, not an implicit heap lookup. -/
def prependHeaderCode (width : Nat) : Program width 8 := #[.load 5 0, .push 5]

theorem prepend_header_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (header : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 0 = word width 0) (heapNonempty : 0 < state.heap.size)
    (headerCell : state.heap[0]? = some header) (room : entry + 2 < 2 ^ width)
    (present : RawTransferLoops.CodeAt program entry (prependHeaderCode width)) :
    ∃ final, Execution program state final 2 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = header :: state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 2) ∧
      final.halted = false ∧
      (∀ register : Fin 8, register ≠ 5 → final.reg register = state.reg register) := by
  let middle := state.advance.put 5 header
  let final := { middle.advance with stack := header :: state.stack }
  have first : programStep program state = some middle := by
    rw [fetched program state entry _ position (by omega)
      (by simpa [prependHeaderCode] using present ⟨0, by simp [prependHeaderCode]⟩)]
    have found : state.heap[0] = header := by
      simpa [Array.getElem?_eq_getElem heapNonempty] using headerCell
    simp [step, running, zero, word, heapNonempty, found, middle]
  have middlePC : middle.pc = word width (entry + 1) := by
    simpa [middle, State.put] using advance_position state position (by omega)
  have last : programStep program middle = some final := by
    rw [fetched program middle (entry + 1) _ middlePC (by omega)
      (by simpa [prependHeaderCode] using present ⟨1, by simp [prependHeaderCode]⟩)]
    simp [step, middle, State.advance, State.put, running, final]
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords + 1 := by
    simp only [final, middle, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have trace := Execution.cons first (Execution.cons last (Execution.refl final))
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, running, ?_⟩
  · simpa only [middleLive, finalLive, Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + 1)] using trace
  · simpa [final, State.put, Nat.add_assoc] using advance_position middle middlePC (by omega)
  · intro register different
    simp [final, middle, State.advance, State.put, different]


/-- The runtime remaining and selected counters use the same fetched decrement
instruction, with an explicit positive natural representation before wrapping. -/
theorem decrement_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (destination : Fin 8) (value : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry < 2 ^ width) (fits : value + 1 < 2 ^ width)
    (counter : state.reg destination = word width (value + 1))
    (mask : state.reg 3 = word width (2 ^ width - 1))
    (present : program[entry]? = some (.add destination destination 3)) :
    Execution program state (state.advance.put destination (word width value))
      1 state.liveWords := by
  have countValue : (state.reg destination).val = value + 1 := by
    rw [counter]
    exact Nat.mod_eq_of_lt fits
  have maskValue : (state.reg 3).val = 2 ^ width - 1 := by
    rw [mask]
    exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
  have transition : programStep program state =
      some (state.advance.put destination (word width value)) := by
    rw [fetched program state entry _ position room present]
    simp only [step, running, Bool.false_eq_true, ite_false, countValue, maskValue]
    rw [decrement_word]
  simpa only [State.advance, State.put, State.liveWords, Nat.max_self] using
    Execution.cons transition (Execution.refl (state.advance.put destination (word width value)))


private theorem decrement_transition (program : Program width 8) (entry : Nat)
    (state : State width 8) (destination : Fin 8) (value : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry < 2 ^ width) (fits : value + 1 < 2 ^ width)
    (counter : state.reg destination = word width (value + 1))
    (mask : state.reg 3 = word width (2 ^ width - 1))
    (present : program[entry]? = some (.add destination destination 3)) :
    programStep program state = some (state.advance.put destination (word width value)) := by
  have countValue : (state.reg destination).val = value + 1 := by
    rw [counter]; exact Nat.mod_eq_of_lt fits
  have maskValue : (state.reg 3).val = 2 ^ width - 1 := by
    rw [mask]; exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
  rw [fetched program state entry _ position room present]
  simp only [step, running, Bool.false_eq_true, ite_false, countValue, maskValue]
  rw [decrement_word]

private theorem tail_zero_include (program : Program width 8) (entry done : Nat)
    (state : State width 8) (remaining kept : Nat)
    (position : state.pc = word width (entry + 5)) (running : state.halted = false)
    (room : entry + 11 < 2 ^ width)
    (remainingFits : remaining + 1 < 2 ^ width) (keptFits : kept + 1 < 2 ^ width)
    (remainingReg : state.reg 2 = word width (remaining + 1))
    (keptReg : state.reg 4 = word width (kept + 1))
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (zeroReg : state.reg 7 = word width 0)
    (bit : (state.reg 0).val = 0) (present : CodeAt program entry done false) :
    ∃ final peak, Execution program state final 4 peak ∧
      peak ≤ state.liveWords + 1 ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.reg 6 :: state.stack ∧ final.output = state.output ∧
      final.reg 2 = word width remaining ∧ final.reg 4 = word width (kept + 1) ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 4 → final.reg register = state.reg register) := by
  let s1 : State width 8 := { state.advance with pc := word width (entry + 8) }
  let s2 : State width 8 := { s1.advance with stack := s1.reg 6 :: s1.stack }
  let s3 : State width 8 := s2.advance.put 2 (word width remaining)
  let s4 : State width 8 := { s3.advance with pc := word width entry }
  have addressFits : ∀ offset ≤ 11, entry + offset < 2 ^ width := by
    intro offset bound; exact lt_of_le_of_lt (Nat.add_le_add_left bound entry) room
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 5) _ position (addressFits 5 (by decide))
      (by simpa [code] using present ⟨5, by decide⟩)]
    simp [step, s1, s4, s3, s2, s1, State.advance, State.put, running, bit]
  have pc1 : s1.pc = word width (entry + 8) := by
    rfl
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 8) _ pc1 (addressFits 8 (by decide))
      (by simpa [code] using present ⟨8, by decide⟩)]
    simp [step, s2, s4, s3, s2, s1, State.advance, State.put, running]
  have pc2 : s2.pc = word width (entry + 9) := by
    simpa only [s2, State.put, Nat.add_assoc] using advance_position s1 pc1 (addressFits 8 (by decide))
  have t2 : programStep program s2 = some s3 := by
    exact decrement_transition program (entry + 9) s2 2 remaining pc2
      (by simp only [s4, s3, s2, s1, State.advance, State.put, running]) (addressFits 9 (by decide)) remainingFits
      (by simpa [s4, s3, s2, s1, State.advance, State.put] using remainingReg)
      (by simpa [s4, s3, s2, s1, State.advance, State.put] using maskReg)
      (by simpa [code] using present ⟨9, by decide⟩)
  have pc3 : s3.pc = word width (entry + 10) := by
    simpa only [s3, State.put, Nat.add_assoc] using advance_position s2 pc2 (addressFits 9 (by decide))
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 10) _ pc3 (addressFits 10 (by decide))
      (by simpa [code] using present ⟨10, by decide⟩)]
    simp [step, s4, s4, s3, s2, s1, State.advance, State.put, running, zeroReg, word]
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live2 : s2.liveWords = state.liveWords + 1 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live3 : s3.liveWords = state.liveWords + 1 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live4 : s4.liveWords = state.liveWords + 1 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s4))))
  refine ⟨s4, state.liveWords + 1, ?_, le_rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, Nat.add_zero, Nat.max_self, Nat.max_eq_right (Nat.le_add_right _ _)] using trace
  · simp only [s4, s3, s2, s1, State.advance, State.put, running]
  · simp only [s4, s3, s2, s1, State.advance, State.put]
  · simp [s4, s3, s2, s1, State.advance, State.put]
  · simp [s4, s3, s2, s1, State.advance, State.put, keptReg]
  · intro register notTwo notFour
    simp [s4, s3, s2, s1, State.advance, State.put, notTwo, notFour]

private theorem tail_zero_discard (program : Program width 8) (entry done : Nat)
    (state : State width 8) (remaining kept : Nat)
    (position : state.pc = word width (entry + 5)) (running : state.halted = false)
    (room : entry + 11 < 2 ^ width)
    (remainingFits : remaining + 1 < 2 ^ width) (keptFits : kept + 1 < 2 ^ width)
    (remainingReg : state.reg 2 = word width (remaining + 1))
    (keptReg : state.reg 4 = word width (kept + 1))
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (zeroReg : state.reg 7 = word width 0)
    (bit : (state.reg 0).val = 0) (present : CodeAt program entry done true) :
    ∃ final peak, Execution program state final 4 peak ∧
      peak ≤ state.liveWords + 0 ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 2 = word width remaining ∧ final.reg 4 = word width (kept) ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 4 → final.reg register = state.reg register) := by
  let s1 : State width 8 := { state.advance with pc := word width (entry + 8) }
  let s2 : State width 8 := s1.advance.put 4 (word width kept)
  let s3 : State width 8 := s2.advance.put 2 (word width remaining)
  let s4 : State width 8 := { s3.advance with pc := word width entry }
  have addressFits : ∀ offset ≤ 11, entry + offset < 2 ^ width := by
    intro offset bound; exact lt_of_le_of_lt (Nat.add_le_add_left bound entry) room
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 5) _ position (addressFits 5 (by decide))
      (by simpa [code] using present ⟨5, by decide⟩)]
    simp [step, s1, s4, s3, s2, s1, State.advance, State.put, running, bit]
  have pc1 : s1.pc = word width (entry + 8) := by
    rfl
  have t1 : programStep program s1 = some s2 := by
    exact decrement_transition program (entry + 8) s1 4 kept pc1
      (by simp only [s4, s3, s2, s1, State.advance, State.put, running]) (addressFits 8 (by decide)) keptFits
      (by simpa only [s4, s3, s2, s1, State.advance, State.put] using keptReg)
      (by simpa [s4, s3, s2, s1, State.advance, State.put] using maskReg)
      (by simpa [code] using present ⟨8, by decide⟩)
  have pc2 : s2.pc = word width (entry + 9) := by
    simpa only [s2, State.put, Nat.add_assoc] using advance_position s1 pc1 (addressFits 8 (by decide))
  have t2 : programStep program s2 = some s3 := by
    exact decrement_transition program (entry + 9) s2 2 remaining pc2
      (by simp only [s4, s3, s2, s1, State.advance, State.put, running]) (addressFits 9 (by decide)) remainingFits
      (by simpa [s4, s3, s2, s1, State.advance, State.put] using remainingReg)
      (by simpa [s4, s3, s2, s1, State.advance, State.put] using maskReg)
      (by simpa [code] using present ⟨9, by decide⟩)
  have pc3 : s3.pc = word width (entry + 10) := by
    simpa only [s3, State.put, Nat.add_assoc] using advance_position s2 pc2 (addressFits 9 (by decide))
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 10) _ pc3 (addressFits 10 (by decide))
      (by simpa [code] using present ⟨10, by decide⟩)]
    simp [step, s4, s4, s3, s2, s1, State.advance, State.put, running, zeroReg, word]
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s4))))
  refine ⟨s4, state.liveWords + 0, ?_, le_rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, Nat.add_zero, Nat.max_self, Nat.max_eq_right (Nat.le_add_right _ _)] using trace
  · simp only [s4, s3, s2, s1, State.advance, State.put, running]
  · simp only [s4, s3, s2, s1, State.advance, State.put]
  · simp [s4, s3, s2, s1, State.advance, State.put]
  · simp [s4, s3, s2, s1, State.advance, State.put, keptReg]
  · intro register notTwo notFour
    simp [s4, s3, s2, s1, State.advance, State.put, notTwo, notFour]

private theorem tail_nonzero_include (program : Program width 8) (entry done : Nat)
    (state : State width 8) (remaining kept : Nat)
    (position : state.pc = word width (entry + 5)) (running : state.halted = false)
    (room : entry + 11 < 2 ^ width)
    (remainingFits : remaining + 1 < 2 ^ width) (keptFits : kept + 1 < 2 ^ width)
    (remainingReg : state.reg 2 = word width (remaining + 1))
    (keptReg : state.reg 4 = word width (kept + 1))
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (zeroReg : state.reg 7 = word width 0)
    (bit : (state.reg 0).val ≠ 0) (present : CodeAt program entry done true) :
    ∃ final peak, Execution program state final 5 peak ∧
      peak ≤ state.liveWords + 1 ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.reg 6 :: state.stack ∧ final.output = state.output ∧
      final.reg 2 = word width remaining ∧ final.reg 4 = word width (kept + 1) ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 4 → final.reg register = state.reg register) := by
  let s1 : State width 8 := state.advance
  let s2 : State width 8 := { s1.advance with stack := s1.reg 6 :: s1.stack }
  let s3 : State width 8 := { s2.advance with pc := word width (entry + 9) }
  let s4 : State width 8 := s3.advance.put 2 (word width remaining)
  let s5 : State width 8 := { s4.advance with pc := word width entry }
  have addressFits : ∀ offset ≤ 11, entry + offset < 2 ^ width := by
    intro offset bound; exact lt_of_le_of_lt (Nat.add_le_add_left bound entry) room
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 5) _ position (addressFits 5 (by decide))
      (by simpa [code] using present ⟨5, by decide⟩)]
    simp [step, s1, s5, s4, s3, s2, s1, State.advance, State.put, running, bit]
  have pc1 : s1.pc = word width (entry + 6) := by
    simpa only [s1, State.put, Nat.add_assoc] using advance_position state position (addressFits 5 (by decide))
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 6) _ pc1 (addressFits 6 (by decide))
      (by simpa [code] using present ⟨6, by decide⟩)]
    simp [step, s2, s5, s4, s3, s2, s1, State.advance, State.put, running]
  have pc2 : s2.pc = word width (entry + 7) := by
    simpa only [s2, State.put, Nat.add_assoc] using advance_position s1 pc1 (addressFits 6 (by decide))
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 7) _ pc2 (addressFits 7 (by decide))
      (by simpa [code] using present ⟨7, by decide⟩)]
    simp [step, s3, s5, s4, s3, s2, s1, State.advance, State.put, running, zeroReg, word]
  have pc3 : s3.pc = word width (entry + 9) := by
    rfl
  have t3 : programStep program s3 = some s4 := by
    exact decrement_transition program (entry + 9) s3 2 remaining pc3
      (by simp only [s5, s4, s3, s2, s1, State.advance, State.put, running]) (addressFits 9 (by decide)) remainingFits
      (by simpa [s5, s4, s3, s2, s1, State.advance, State.put] using remainingReg)
      (by simpa [s5, s4, s3, s2, s1, State.advance, State.put] using maskReg)
      (by simpa [code] using present ⟨9, by decide⟩)
  have pc4 : s4.pc = word width (entry + 10) := by
    simpa only [s4, State.put, Nat.add_assoc] using advance_position s3 pc3 (addressFits 9 (by decide))
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 10) _ pc4 (addressFits 10 (by decide))
      (by simpa [code] using present ⟨10, by decide⟩)]
    simp [step, s5, s5, s4, s3, s2, s1, State.advance, State.put, running, zeroReg, word]
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live2 : s2.liveWords = state.liveWords + 1 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live3 : s3.liveWords = state.liveWords + 1 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live4 : s4.liveWords = state.liveWords + 1 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live5 : s5.liveWords = state.liveWords + 1 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.refl s5)))))
  refine ⟨s5, state.liveWords + 1, ?_, le_rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, Nat.add_zero, Nat.max_self, Nat.max_eq_right (Nat.le_add_right _ _)] using trace
  · simp only [s5, s4, s3, s2, s1, State.advance, State.put, running]
  · simp only [s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s5, s4, s3, s2, s1, State.advance, State.put, keptReg]
  · intro register notTwo notFour
    simp [s5, s4, s3, s2, s1, State.advance, State.put, notTwo, notFour]

private theorem tail_nonzero_discard (program : Program width 8) (entry done : Nat)
    (state : State width 8) (remaining kept : Nat)
    (position : state.pc = word width (entry + 5)) (running : state.halted = false)
    (room : entry + 11 < 2 ^ width)
    (remainingFits : remaining + 1 < 2 ^ width) (keptFits : kept + 1 < 2 ^ width)
    (remainingReg : state.reg 2 = word width (remaining + 1))
    (keptReg : state.reg 4 = word width (kept + 1))
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (zeroReg : state.reg 7 = word width 0)
    (bit : (state.reg 0).val ≠ 0) (present : CodeAt program entry done false) :
    ∃ final peak, Execution program state final 5 peak ∧
      peak ≤ state.liveWords + 0 ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 2 = word width remaining ∧ final.reg 4 = word width (kept) ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 4 → final.reg register = state.reg register) := by
  let s1 : State width 8 := state.advance
  let s2 : State width 8 := s1.advance.put 4 (word width kept)
  let s3 : State width 8 := { s2.advance with pc := word width (entry + 9) }
  let s4 : State width 8 := s3.advance.put 2 (word width remaining)
  let s5 : State width 8 := { s4.advance with pc := word width entry }
  have addressFits : ∀ offset ≤ 11, entry + offset < 2 ^ width := by
    intro offset bound; exact lt_of_le_of_lt (Nat.add_le_add_left bound entry) room
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 5) _ position (addressFits 5 (by decide))
      (by simpa [code] using present ⟨5, by decide⟩)]
    simp [step, s1, s5, s4, s3, s2, s1, State.advance, State.put, running, bit]
  have pc1 : s1.pc = word width (entry + 6) := by
    simpa only [s1, State.put, Nat.add_assoc] using advance_position state position (addressFits 5 (by decide))
  have t1 : programStep program s1 = some s2 := by
    exact decrement_transition program (entry + 6) s1 4 kept pc1
      (by simp only [s5, s4, s3, s2, s1, State.advance, State.put, running]) (addressFits 6 (by decide)) keptFits
      (by simpa only [s5, s4, s3, s2, s1, State.advance, State.put] using keptReg)
      (by simpa [s5, s4, s3, s2, s1, State.advance, State.put] using maskReg)
      (by simpa [code] using present ⟨6, by decide⟩)
  have pc2 : s2.pc = word width (entry + 7) := by
    simpa only [s2, State.put, Nat.add_assoc] using advance_position s1 pc1 (addressFits 6 (by decide))
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 7) _ pc2 (addressFits 7 (by decide))
      (by simpa [code] using present ⟨7, by decide⟩)]
    simp [step, s3, s5, s4, s3, s2, s1, State.advance, State.put, running, zeroReg, word]
  have pc3 : s3.pc = word width (entry + 9) := by
    rfl
  have t3 : programStep program s3 = some s4 := by
    exact decrement_transition program (entry + 9) s3 2 remaining pc3
      (by simp only [s5, s4, s3, s2, s1, State.advance, State.put, running]) (addressFits 9 (by decide)) remainingFits
      (by simpa [s5, s4, s3, s2, s1, State.advance, State.put] using remainingReg)
      (by simpa [s5, s4, s3, s2, s1, State.advance, State.put] using maskReg)
      (by simpa [code] using present ⟨9, by decide⟩)
  have pc4 : s4.pc = word width (entry + 10) := by
    simpa only [s4, State.put, Nat.add_assoc] using advance_position s3 pc3 (addressFits 9 (by decide))
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 10) _ pc4 (addressFits 10 (by decide))
      (by simpa [code] using present ⟨10, by decide⟩)]
    simp [step, s5, s5, s4, s3, s2, s1, State.advance, State.put, running, zeroReg, word]
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have live5 : s5.liveWords = state.liveWords + 0 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, List.length_cons] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.refl s5)))))
  refine ⟨s5, state.liveWords + 0, ?_, le_rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, Nat.add_zero, Nat.max_self, Nat.max_eq_right (Nat.le_add_right _ _)] using trace
  · simp only [s5, s4, s3, s2, s1, State.advance, State.put, running]
  · simp only [s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s5, s4, s3, s2, s1, State.advance, State.put, keptReg]
  · intro register notTwo notFour
    simp [s5, s4, s3, s2, s1, State.advance, State.put, notTwo, notFour]


def keeps (value : Word width) (healthy : Bool) : Bool := (value.val != 0) == healthy

private theorem tail_execution (program : Program width 8) (entry done : Nat)
    (healthy : Bool) (state : State width 8) (remaining kept : Nat)
    (position : state.pc = word width (entry + 5)) (running : state.halted = false)
    (room : entry + 11 < 2 ^ width)
    (remainingFits : remaining + 1 < 2 ^ width) (keptFits : kept + 1 < 2 ^ width)
    (remainingReg : state.reg 2 = word width (remaining + 1))
    (keptReg : state.reg 4 = word width (kept + 1))
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (zeroReg : state.reg 7 = word width 0) (present : CodeAt program entry done healthy) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 5 ∧
      peak ≤ state.liveWords + (if keeps (state.reg 0) healthy then 1 else 0) ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.heap = state.heap ∧
      final.stack = (if keeps (state.reg 0) healthy then state.reg 6 :: state.stack else state.stack) ∧
      final.output = state.output ∧ final.reg 2 = word width remaining ∧
      final.reg 4 = word width (kept + (if keeps (state.reg 0) healthy then 1 else 0)) ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 4 → final.reg register = state.reg register) := by
  cases healthy with
  | false =>
    by_cases zero : (state.reg 0).val = 0
    · obtain ⟨final, peak, trace, bound, pc, active, heap, stack, output, count, selectedCount, frame⟩ :=
        tail_zero_include program entry done state remaining kept position running room
          remainingFits keptFits remainingReg keptReg maskReg zeroReg zero present
      refine ⟨final, 4, peak, trace, by decide, ?_⟩
      simpa [keeps, zero] using And.intro bound
        (And.intro pc (And.intro active (And.intro heap (And.intro stack
          (And.intro output (And.intro count (And.intro selectedCount frame)))))))
    · obtain ⟨final, peak, trace, bound, pc, active, heap, stack, output, count, selectedCount, frame⟩ :=
        tail_nonzero_discard program entry done state remaining kept position running room
          remainingFits keptFits remainingReg keptReg maskReg zeroReg zero present
      refine ⟨final, 5, peak, trace, by decide, ?_⟩
      simpa [keeps, zero] using And.intro bound
        (And.intro pc (And.intro active (And.intro heap (And.intro stack
          (And.intro output (And.intro count (And.intro selectedCount frame)))))))
  | true =>
    by_cases zero : (state.reg 0).val = 0
    · obtain ⟨final, peak, trace, bound, pc, active, heap, stack, output, count, selectedCount, frame⟩ :=
        tail_zero_discard program entry done state remaining kept position running room
          remainingFits keptFits remainingReg keptReg maskReg zeroReg zero present
      refine ⟨final, 4, peak, trace, by decide, ?_⟩
      simpa [keeps, zero] using And.intro bound
        (And.intro pc (And.intro active (And.intro heap (And.intro stack
          (And.intro output (And.intro count (And.intro selectedCount frame)))))))
    · obtain ⟨final, peak, trace, bound, pc, active, heap, stack, output, count, selectedCount, frame⟩ :=
        tail_nonzero_include program entry done state remaining kept position running room
          remainingFits keptFits remainingReg keptReg maskReg zeroReg zero present
      refine ⟨final, 5, peak, trace, by decide, ?_⟩
      simpa [keeps, zero] using And.intro bound
        (And.intro pc (And.intro active (And.intro heap (And.intro stack
          (And.intro output (And.intro count (And.intro selectedCount frame)))))))

private theorem round_execution (program : Program width 8) (entry done : Nat)
    (healthy : Bool) (state : State width 8) (cursor remaining kept : Nat)
    (root value : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 11 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width) (keptFits : kept + 1 < 2 ^ width)
    (cursorReg : state.reg 1 = word width (cursor + 1))
    (countReg : state.reg 2 = word width (remaining + 1))
    (keptReg : state.reg 4 = word width (kept + 1))
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (zeroReg : state.reg 7 = word width 0)
    (rootBound : cursor < state.heap.size) (rootCell : state.heap[cursor]? = some root)
    (addressBound : root.val + (state.reg 5).val < state.heap.size)
    (addressFits : root.val + (state.reg 5).val < 2 ^ width)
    (valueCell : state.heap[root.val + (state.reg 5).val]? = some value)
    (present : CodeAt program entry done healthy) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 10 ∧
      peak ≤ state.liveWords + (if keeps value healthy then 1 else 0) ∧
      final.pc = word width entry ∧ final.halted = false ∧ final.heap = state.heap ∧
      final.stack = (if keeps value healthy then root :: state.stack else state.stack) ∧
      final.output = state.output ∧ final.reg 1 = word width cursor ∧
      final.reg 2 = word width remaining ∧
      final.reg 4 = word width (kept + (if keeps value healthy then 1 else 0)) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        register ≠ 4 → register ≠ 6 → final.reg register = state.reg register) := by
  let first := state.advance.advance.put 1 (word width cursor)
  let second := first.advance.put 6 root
  let third := second.advance.put 0 (word width (root.val + (state.reg 5).val))
  let readState := third.advance.put 0 value
  obtain ⟨readTrace, readPC, readHeap, readStack, readOutput⟩ :=
    read_execution program entry done healthy state cursor remaining root value position running room
      cursorFits countFits cursorReg countReg maskReg rootBound rootCell addressBound addressFits valueCell present
  have readZero : readState.reg 0 = value := by simp [readState, State.put]
  have readRoot : readState.reg 6 = root := by simp [readState, third, second, State.put, State.advance]
  have readCursor : readState.reg 1 = word width cursor := by
    simp [readState, third, second, first, State.put, State.advance]
  have readFrame : ∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 6 →
      readState.reg register = state.reg register := by
    intro register notZero notOne notSix
    simp [readState, third, second, first, State.put, State.advance, notZero, notOne, notSix]
  obtain ⟨final, ticks, peak, tailTrace, tickBound, peakBound, pc, active, heap, stack,
      output, count, selectedCount, frame⟩ :=
    tail_execution program entry done healthy readState remaining kept readPC running room countFits keptFits
      (by rw [readFrame 2 (by decide) (by decide) (by decide)]; exact countReg)
      (by rw [readFrame 4 (by decide) (by decide) (by decide)]; exact keptReg)
      (by rw [readFrame 3 (by decide) (by decide) (by decide)]; exact maskReg)
      (by rw [readFrame 7 (by decide) (by decide) (by decide)]; exact zeroReg) present
  have readStackEq : readState.stack = state.stack := rfl
  have readLive : readState.liveWords = state.liveWords := rfl
  refine ⟨final, 5 + ticks, max state.liveWords peak, readTrace.append tailTrace, by omega,
    ?_, pc, active, heap.trans readHeap, ?_, output.trans readOutput, ?_, count, ?_, ?_⟩
  · rw [readLive, readZero] at peakBound
    exact max_le (Nat.le_add_right _ _) peakBound
  · simpa only [readZero, readRoot, readStackEq] using stack
  · rw [frame 1 (by decide) (by decide)]
    exact readCursor
  · simpa only [readZero] using selectedCount
  · intro register notZero notOne notTwo notFour notSix
    exact (frame register notTwo notFour).trans (readFrame register notZero notOne notSix)

/-- The selection predicate reads the actual indexed cell. -/
theorem selected_last (heap : Array (Word width)) (valueBase : Nat) (healthy : Bool)
    (before : List (Word width)) (root value : Word width)
    (cell : heap[valueBase + root.val]? = some value) :
    selected heap valueBase healthy (before ++ [root]) =
      selected heap valueBase healthy before ++ (if keeps value healthy then [root] else []) := by
  rw [selected_append]
  simp [selected, List.filter_cons, cell, keeps]


/-- The whole fixed loop retains every occurrence selected by its actual node
value. Its selected-count register and ordered stack are proved together. -/
theorem loop_execution (program : Program width 8) (entry done rootBase valueBase : Nat)
    (healthy : Bool) (roots : List (Word width)) :
    ∀ extra : Nat, ∀ state : State width 8,
      state.pc = word width entry → state.halted = false → entry + 11 < 2 ^ width →
      state.heap.size ≤ 2 ^ width → Stored state.heap rootBase valueBase roots →
      rootBase + roots.length < 2 ^ width → roots.length + extra < 2 ^ width →
      state.reg 1 = word width (rootBase + roots.length) →
      state.reg 2 = word width roots.length → state.reg 4 = word width (roots.length + extra) →
      state.reg 3 = word width (2 ^ width - 1) → state.reg 5 = word width valueBase →
      state.reg 7 = word width 0 → CodeAt program entry done healthy →
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 10 * roots.length + 1 ∧
      peak ≤ state.liveWords + (selected state.heap valueBase healthy roots).length ∧
      final.pc = word width done ∧ final.halted = false ∧ final.heap = state.heap ∧
      final.stack = selected state.heap valueBase healthy roots ++ state.stack ∧
      final.output = state.output ∧ final.reg 1 = word width rootBase ∧
      final.reg 2 = word width 0 ∧
      final.reg 4 = word width (extra + (selected state.heap valueBase healthy roots).length) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        register ≠ 4 → register ≠ 6 → final.reg register = state.reg register) := by
  induction roots using List.reverseRecOn with
  | nil =>
    intro extra state position running room heapFits stored cursorFits keptFits cursorReg countReg
      keptReg maskReg valueReg zeroReg present
    let final := { state.advance with pc := word width done }
    have trace : Execution program state final 1 state.liveWords :=
      zero_execution program entry done healthy state position running (by simpa using countReg)
        (by omega) present
    refine ⟨final, 1, state.liveWords, trace, by simp, by simp, rfl, running, rfl,
      by simp [final, State.advance], rfl, ?_, ?_, ?_, ?_⟩
    · simpa [final, State.advance] using cursorReg
    · simpa [final, State.advance] using countReg
    · simpa [final, State.advance] using keptReg
    · intro register notZero notOne notTwo notFour notSix; rfl
  | append_singleton before root ih =>
    intro extra state position running room heapFits stored cursorFits keptFits cursorReg countReg
      keptReg maskReg valueReg zeroReg present
    have lengthEq : (before ++ [root]).length = before.length + 1 := by simp
    have rootPresent : root ∈ before ++ [root] := by simp
    have rootBound : rootBase + before.length < state.heap.size := by
      have bound := stored.rootBound
      rw [lengthEq] at bound
      omega
    have rootCell : state.heap[rootBase + before.length]? = some root := by
      simpa using stored.rootCell ⟨before.length, by rw [lengthEq]; omega⟩
    have valueBound : valueBase + root.val < state.heap.size := stored.valueBound root rootPresent
    let value := state.heap[valueBase + root.val]
    have valueCell : state.heap[valueBase + root.val]? = some value :=
      Array.getElem?_eq_getElem valueBound
    have valueBaseVal : (word width valueBase).val = valueBase := Nat.mod_eq_of_lt stored.valueFits
    let picked : Nat := if keeps value healthy then 1 else 0
    obtain ⟨middle, firstTicks, firstPeak, first, firstTime, firstBound, middlePC, middleRunning,
        middleHeap, middleStack, middleOutput, middleCursor, middleCount, middleKept, middleFrame⟩ :=
      round_execution program entry done healthy state (rootBase + before.length) before.length
        (before.length + extra) root value position running room
        (by rw [lengthEq] at cursorFits; omega) (by rw [lengthEq] at cursorFits; omega)
        (by rw [lengthEq] at keptFits; omega)
        (by simpa only [lengthEq, Nat.add_assoc] using cursorReg)
        (by simpa only [lengthEq] using countReg)
        (by simpa only [lengthEq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using keptReg)
        maskReg zeroReg rootBound rootCell
        (by
          rw [valueReg, valueBaseVal]
          simpa only [Nat.add_comm] using valueBound)
        (by
          rw [valueReg, valueBaseVal]
          omega)
        (by
          rw [valueReg, valueBaseVal]
          simpa only [Nat.add_comm] using valueCell) present
    have prefixStored : Stored state.heap rootBase valueBase before := by
      refine ⟨by have bound := stored.rootBound; rw [lengthEq] at bound; omega, ?_, ?_, stored.valueFits⟩
      · intro index
        simpa only [List.getElem_append_left index.isLt] using
          stored.rootCell ⟨index.val, by rw [lengthEq]; omega⟩
      · intro source member
        exact stored.valueBound source (List.mem_append_left _ member)
    have middleStored : Stored middle.heap rootBase valueBase before := by
      rw [middleHeap]
      exact prefixStored
    have pickedBound : picked ≤ 1 := by unfold picked; split <;> omega
    have middleKeptEq : middle.reg 4 = word width (before.length + (extra + picked)) := by
      simpa only [picked, Nat.add_assoc] using middleKept
    obtain ⟨final, lastTicks, lastPeak, last, lastTime, lastBound, finalPC, finalRunning,
        finalHeap, finalStack, finalOutput, finalCursor, finalCount, finalKept, finalFrame⟩ :=
      ih (extra + picked) middle middlePC middleRunning room (by rw [middleHeap]; exact heapFits)
        middleStored (by rw [lengthEq] at cursorFits; omega) (by rw [lengthEq] at keptFits; omega)
        middleCursor middleCount middleKeptEq
        (by rw [middleFrame 3 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact maskReg)
        (by rw [middleFrame 5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact valueReg)
        (by rw [middleFrame 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact zeroReg)
        present
    have selectedEq := selected_last state.heap valueBase healthy before root value valueCell
    have selectedLength : (selected state.heap valueBase healthy (before ++ [root])).length =
        (selected state.heap valueBase healthy before).length + picked := by
      rw [selectedEq, List.length_append]
      unfold picked
      split <;> simp_all only [List.length_singleton, List.length_nil]
    have middleLive : middle.liveWords = state.liveWords + picked := by
      simp only [State.liveWords, middleHeap, middleOutput, middleStack]
      unfold picked
      split <;> simp_all only [List.length_cons] <;> omega
    rw [middleHeap] at lastBound finalStack finalKept
    refine ⟨final, firstTicks + lastTicks, max firstPeak lastPeak, first.append last,
      by rw [lengthEq]; omega, ?_, finalPC, finalRunning, finalHeap.trans middleHeap,
      ?_, finalOutput.trans middleOutput, finalCursor, finalCount, ?_, ?_⟩
    · rw [selectedLength]
      change firstPeak ≤ state.liveWords + picked at firstBound
      rw [middleLive] at lastBound
      exact max_le (by omega) (by omega)
    · rw [selectedEq, finalStack, middleStack]
      cases chosen : keeps value healthy <;> simp only [chosen, Bool.false_eq_true, ite_false,
        ite_true, List.append_nil, List.append_assoc, List.singleton_append]
    · rw [selectedLength]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalKept
    · intro register notZero notOne notTwo notFour notSix
      exact (finalFrame register notZero notOne notTwo notFour notSix).trans
        (middleFrame register notZero notOne notTwo notFour notSix)

/-- With the runtime selected counter initialized from the original root
count, the final register-four word is exactly the filtered occurrence count. -/
theorem execution (program : Program width 8) (entry done rootBase valueBase : Nat)
    (healthy : Bool) (roots : List (Word width)) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 11 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (stored : Stored state.heap rootBase valueBase roots)
    (cursorFits : rootBase + roots.length < 2 ^ width)
    (cursorReg : state.reg 1 = word width (rootBase + roots.length))
    (countReg : state.reg 2 = word width roots.length)
    (selectedReg : state.reg 4 = word width roots.length)
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (valueReg : state.reg 5 = word width valueBase) (zeroReg : state.reg 7 = word width 0)
    (present : CodeAt program entry done healthy) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 10 * roots.length + 1 ∧
      peak ≤ state.liveWords + (selected state.heap valueBase healthy roots).length ∧
      final.pc = word width done ∧ final.halted = false ∧ final.heap = state.heap ∧
      final.stack = selected state.heap valueBase healthy roots ++ state.stack ∧
      final.output = state.output ∧ final.reg 1 = word width rootBase ∧ final.reg 2 = word width 0 ∧
      final.reg 4 = word width (selected state.heap valueBase healthy roots).length ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        register ≠ 4 → register ≠ 6 → final.reg register = state.reg register) := by
  simpa only [Nat.add_zero, Nat.zero_add] using loop_execution program entry done rootBase valueBase
    healthy roots 0 state position running room heapFits stored cursorFits (by omega)
    cursorReg countReg (by simpa using selectedReg) maskReg valueReg zeroReg present

/-- Prefix-copy preparation writes the executed selected count into header four.
The first projection retains the original count in register two; the second
retains the already derived full-heap release count instead. -/
def prepareCode (width : Nat) (rememberOriginal : Bool) : Program width 8 :=
  #[.constant 0 (word width 4),
    (if rememberOriginal then .load 2 0 else .copy 2 2), .store 0 4,
    .add 0 1 3, .copy 1 0, .copy 7 3, .constant 6 (word width 0)]

@[simp] theorem prepareCode_size (width : Nat) (rememberOriginal : Bool) :
    (prepareCode width rememberOriginal).size = 7 := by cases rememberOriginal <;> rfl

private theorem prepare_execution (program : Program width 8) (entry : Nat)
    (rememberOriginal : Bool) (state : State width 8) (rootBase : Nat) (oldHeader : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 7 < 2 ^ width) (basePositive : 5 ≤ rootBase)
    (baseFits : rootBase < 2 ^ width) (headerBound : 4 < state.heap.size)
    (headerCell : state.heap[4]? = some oldHeader)
    (cursorReg : state.reg 1 = word width rootBase)
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (present : RawTransferLoops.CodeAt program entry (prepareCode width rememberOriginal)) :
    ∃ final, Execution program state final 7 state.liveWords ∧
      final.pc = word width (entry + 7) ∧ final.halted = false ∧
      final.heap = state.heap.setIfInBounds 4 (state.reg 4) ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.reg 0 = word width (rootBase - 1) ∧
      final.reg 1 = word width (rootBase - 1) ∧
      final.reg 2 = (if rememberOriginal then oldHeader else state.reg 2) ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) ∧
      (∀ register : Fin 8, register = 3 ∨ register = 4 ∨ register = 5 →
        final.reg register = state.reg register) := by
  let s1 := state.advance.put 0 (word width 4)
  let s2 := s1.advance.put 2 (if rememberOriginal then oldHeader else state.reg 2)
  let s3 := { s2.advance with heap := state.heap.setIfInBounds 4 (state.reg 4) }
  let s4 := s3.advance.put 0 (word width (rootBase - 1))
  let s5 := s4.advance.put 1 (word width (rootBase - 1))
  let s6 := s5.advance.put 7 (word width (2 ^ width - 1))
  let s7 := s6.advance.put 6 (word width 0)
  have addressFits : ∀ offset ≤ 7, entry + offset < 2 ^ width := by
    intro offset bound; exact lt_of_le_of_lt (Nat.add_le_add_left bound entry) room
  have fourValue : (word width 4).val = 4 := Nat.mod_eq_of_lt (by omega)
  have baseValue : (state.reg 1).val = rootBase := by rw [cursorReg]; exact Nat.mod_eq_of_lt baseFits
  have maskValue : (state.reg 3).val = 2 ^ width - 1 := by
    rw [maskReg]; exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
  have baseDecrement : word width (rootBase + (2 ^ width - 1)) = word width (rootBase - 1) := by
    have same : rootBase - 1 + 1 = rootBase := by omega
    simpa only [same] using decrement_word width (rootBase - 1)
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry _ position (addressFits 0 (by decide))
      (by simpa [prepareCode] using present ⟨0, by simp⟩)]
    simp [step, running, s1]
  have pc1 : s1.pc = word width (entry + 1) := by
    simpa [s1, State.put] using advance_position state position (addressFits 0 (by decide))
  have t1 : programStep program s1 = some s2 := by
    cases rememberOriginal <;>
      rw [fetched program s1 (entry + 1) _ pc1 (addressFits 1 (by decide))
        (by simpa [prepareCode] using present ⟨1, by simp⟩)]
    · simp [step, s2, s1, State.advance, State.put, running]
    · have found : state.heap[4] = oldHeader := by
        simpa [Array.getElem?_eq_getElem headerBound] using headerCell
      simp [step, s2, s1, State.advance, State.put, running, fourValue, headerBound, found]
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using advance_position s1 pc1 (addressFits 1 (by decide))
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) _ pc2 (addressFits 2 (by decide))
      (by simpa [prepareCode] using present ⟨2, by simp⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running, fourValue,
      headerBound, Array.setIfInBounds]
  have pc3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using advance_position s2 pc2 (addressFits 2 (by decide))
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) _ pc3 (addressFits 3 (by decide))
      (by simpa [prepareCode] using present ⟨3, by simp⟩)]
    simp only [step, s3, s2, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, Fin.reduceEq, ite_true, baseValue, maskValue]
    rw [baseDecrement]
    simp only [s4, s3, s2, s1, State.advance, State.put, running]
  have pc4 : s4.pc = word width (entry + 4) := by
    simpa [s4, State.put, Nat.add_assoc] using advance_position s3 pc3 (addressFits 3 (by decide))
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) _ pc4 (addressFits 4 (by decide))
      (by simpa [prepareCode] using present ⟨4, by simp⟩)]
    simp [step, s5, s4, s3, s2, s1, State.advance, State.put, running]
  have pc5 : s5.pc = word width (entry + 5) := by
    simpa [s5, State.put, Nat.add_assoc] using advance_position s4 pc4 (addressFits 4 (by decide))
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) _ pc5 (addressFits 5 (by decide))
      (by simpa [prepareCode] using present ⟨5, by simp⟩)]
    simp [step, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, maskReg]
  have pc6 : s6.pc = word width (entry + 6) := by
    simpa [s6, State.put, Nat.add_assoc] using advance_position s5 pc5 (addressFits 5 (by decide))
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) _ pc6 (addressFits 6 (by decide))
      (by simpa [prepareCode] using present ⟨6, by simp⟩)]
    simp [step, s7, running, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  have finalPC : s7.pc = word width (entry + 7) := by
    simpa [s7, State.put, Nat.add_assoc] using advance_position s6 pc6 (addressFits 6 (by decide))
  have live1 : s1.liveWords = state.liveWords := rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have live3 : s3.liveWords = state.liveWords := by simp [s3, s2, s1, State.liveWords, State.advance, State.put]
  have live4 : s4.liveWords = state.liveWords := by
    change s3.liveWords = state.liveWords
    exact live3
  have live5 : s5.liveWords = state.liveWords := by
    change s4.liveWords = state.liveWords
    exact live4
  have live6 : s6.liveWords = state.liveWords := by
    change s5.liveWords = state.liveWords
    exact live5
  have live7 : s7.liveWords = state.liveWords := by
    change s6.liveWords = state.liveWords
    exact live6
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3
    (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.refl s7)))))))
  refine ⟨s7, ?_, finalPC, running, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, live6, live7, Nat.max_self] using trace
  · simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · intro register member
    rcases member with rfl | rfl | rfl <;>
      simp [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]

/-- Source-prefix correspondence exposes physical cells including the count
header. Its node and incidence words do not depend on the retained roots. -/
def prefixWords (width channels : Nat) (rows : List ForestIndexedOperands.Row)
    (count : Nat) : List (Word width) :=
  [word width channels, word width rows.length,
    word width (ForestIndexedOperands.rowChildren rows).length,
    word width (ForestIndexedOperands.rowGuards rows).length, word width count] ++
    (ForestIndexedOperands.packetPrefix 5 rows).map (word width)

@[simp] theorem prefixWords_length (channels count : Nat) (rows : List ForestIndexedOperands.Row) :
    (prefixWords width channels rows count).length =
      5 + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards rows).length := by
  simp [prefixWords, ForestIndexedOperands.packetPrefix_length]
  omega

structure PrefixStored (heap : Array (Word width)) (channels : Nat)
    (rows : List ForestIndexedOperands.Row) (count : Nat) : Prop where
  bound : (prefixWords width channels rows count).length ≤ heap.size
  cell : ∀ index : Fin (prefixWords width channels rows count).length,
    heap[index.val]? = some (prefixWords width channels rows count)[index.val]

theorem prefix_store_count (heap : Array (Word width)) (channels oldCount newCount : Nat)
    (rows : List ForestIndexedOperands.Row) (stored : PrefixStored heap channels rows oldCount) :
    PrefixStored (heap.setIfInBounds 4 (word width newCount)) channels rows newCount := by
  have oldLength := prefixWords_length (width := width) channels oldCount rows
  have newLength := prefixWords_length (width := width) channels newCount rows
  have fourBound : 4 < heap.size := by have := stored.bound; rw [oldLength] at this; omega
  have oldBound := stored.bound
  rw [oldLength] at oldBound
  refine ⟨by simpa only [Array.size_setIfInBounds, newLength] using oldBound, ?_⟩
  intro index
  rw [Array.getElem?_setIfInBounds]
  by_cases atCount : index.val = 4
  · simp [atCount, fourBound, prefixWords]
  · have oldValid : index.val < (prefixWords width channels rows oldCount).length := by
      simpa only [oldLength, newLength] using index.isLt
    rw [ite_eq_right (Ne.symm atCount), stored.cell ⟨index.val, oldValid⟩]
    have same : (prefixWords width channels rows oldCount)[index.val] =
        (prefixWords width channels rows newCount)[index.val] := by
      by_cases first : index.val < 5
      · have alternatives : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨ index.val = 3 := by omega
        rcases alternatives with h | h | h | h <;> simp [prefixWords, h]
      · simp only [prefixWords]
        rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt first),
          List.getElem_append_right (by simpa using Nat.le_of_not_lt first)]
        rfl
    exact congrArg some same

/-- Copy a resident prefix without relocating its row addresses. Header zero is
read after the reverse-save loop, whose positive base is one. Both executions
preserve the original-count or release-count word in register two. -/
theorem prefix_copy_execution (program : Program width 8) (entry headerEntry : Nat)
    (state : State width 8) (channels count : Nat) (rows : List ForestIndexedOperands.Row)
    (stored : PrefixStored state.heap channels rows count)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 6 < 2 ^ width) (headerRoom : headerEntry + 2 < 2 ^ width)
    (fits : (prefixWords width channels rows count).length < 2 ^ width)
    (lengthReg : state.reg 0 = word width ((prefixWords width channels rows count).length - 1))
    (cursorReg : state.reg 1 = word width ((prefixWords width channels rows count).length - 1))
    (maskReg : state.reg 7 = word width (2 ^ width - 1))
    (zeroReg : state.reg 6 = word width 0)
    (saveAt : RawTransferLoops.CodeAt program entry
      (RawTransferLoops.reverseSaveCode width entry headerEntry))
    (headerAt : RawTransferLoops.CodeAt program headerEntry (prependHeaderCode width)) :
    ∃ final peak, Execution program state final
        (6 * ((prefixWords width channels rows count).length - 1) + 3) peak ∧
      peak ≤ state.liveWords + (prefixWords width channels rows count).length ∧
      final.heap = state.heap ∧
      final.stack = prefixWords width channels rows count ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (headerEntry + 2) ∧
      final.halted = false ∧ final.reg 2 = state.reg 2 ∧
      final.reg 3 = state.reg 3 ∧ final.reg 4 = state.reg 4 ∧
      final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let packet := prefixWords width channels rows count
  have packetPositive : 0 < packet.length := by
    dsimp only [packet]
    rw [prefixWords_length]
    omega
  have packetFits : packet.length < 2 ^ width := fits
  have packetBound : packet.length ≤ state.heap.size := stored.bound
  have tailLength : packet.tail.length = packet.length - 1 := List.length_tail
  have tailCells : ∀ index : Nat, ∀ bound : index < packet.tail.length,
      state.heap[1 + index]? = some packet.tail[index] := by
    intro index bound
    have valid : 1 + index < packet.length := by rw [tailLength] at bound; omega
    have found := stored.cell ⟨1 + index, valid⟩
    simpa only [packet, List.getElem_tail, Nat.add_comm] using found
  obtain ⟨middle, savePeak, save, saveBound, middleHeap, middleStack, middleOutput,
      middlePC, middleRunning, middleZero, middleFrame⟩ :=
    RawTransferLoops.reverse_save_execution program entry headerEntry 1 packet.tail state
      position running room (by decide) (by rw [tailLength]; omega)
      (by rw [tailLength]; omega) (by simpa only [tailLength, packet] using lengthReg)
      (by
        have addressEq : 1 + packet.tail.length - 1 = packet.length - 1 := by
          rw [tailLength]
          omega
        rw [addressEq]
        exact cursorReg)
      maskReg zeroReg tailCells saveAt
  have zeroCell : middle.heap[0]? = some (word width channels) := by
    rw [middleHeap]
    simpa [prefixWords] using stored.cell ⟨0, packetPositive⟩
  obtain ⟨final, header, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    prepend_header_execution program headerEntry middle (word width channels)
      middlePC middleRunning middleZero (by rw [middleHeap]; omega)
      zeroCell headerRoom headerAt
  have middleLive : middle.liveWords = state.liveWords + packet.tail.length := by
    simp only [State.liveWords, middleHeap, middleStack, middleOutput, List.length_append]
    omega
  refine ⟨final, max savePeak (middle.liveWords + 1), ?_, ?_,
    finalHeap.trans middleHeap, ?_, finalOutput.trans middleOutput,
    finalPC, finalRunning, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tailLength, packet, Nat.add_assoc] using save.append header
  · change max savePeak (middle.liveWords + 1) ≤ state.liveWords + packet.length
    rw [middleLive]
    rw [tailLength] at saveBound ⊢
    exact Nat.max_le.mpr ⟨by omega, by omega⟩
  · rw [finalStack, middleStack]
    change word width channels :: (packet.tail ++ state.stack) = packet ++ state.stack
    have packetHead : packet = word width channels :: packet.tail := by rfl
    rw [packetHead]
    rfl
  all_goals first
    | exact (finalFrame _ (by decide)).trans (middleFrame _ (by decide) (by decide) (by decide))

/-- Actual selected-count write and ordered prefix copy form a reloadable packet
on top of the selected roots already pushed by the filter loop. -/
theorem prepare_copy_execution (program : Program width 8) (entry saveEntry headerEntry : Nat)
    (rememberOriginal : Bool) (state : State width 8) (channels oldCount newCount : Nat)
    (rows : List ForestIndexedOperands.Row)
    (stored : PrefixStored state.heap channels rows oldCount)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 7 < 2 ^ width) (saveRoom : saveEntry + 6 < 2 ^ width)
    (headerRoom : headerEntry + 2 < 2 ^ width) (adjacent : entry + 7 = saveEntry)
    (prefixFits : (prefixWords width channels rows oldCount).length < 2 ^ width)
    (cursorReg : state.reg 1 = word width (prefixWords width channels rows oldCount).length)
    (maskReg : state.reg 3 = word width (2 ^ width - 1))
    (selectedReg : state.reg 4 = word width newCount)
    (prepareAt : RawTransferLoops.CodeAt program entry (prepareCode width rememberOriginal))
    (saveAt : RawTransferLoops.CodeAt program saveEntry
      (RawTransferLoops.reverseSaveCode width saveEntry headerEntry))
    (headerAt : RawTransferLoops.CodeAt program headerEntry (prependHeaderCode width)) :
    ∃ final peak, Execution program state final
        (6 * (prefixWords width channels rows newCount).length + 4) peak ∧
      peak ≤ state.liveWords + (prefixWords width channels rows newCount).length ∧
      final.heap = state.heap.setIfInBounds 4 (word width newCount) ∧
      final.stack = prefixWords width channels rows newCount ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (headerEntry + 2) ∧
      final.halted = false ∧
      final.reg 2 = (if rememberOriginal then word width oldCount else state.reg 2) ∧
      final.reg 3 = state.reg 3 ∧ final.reg 4 = word width newCount ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) := by
  have sameLength : (prefixWords width channels rows newCount).length =
      (prefixWords width channels rows oldCount).length := by
    rw [prefixWords_length, prefixWords_length]
  have positive : 5 ≤ (prefixWords width channels rows oldCount).length := by
    rw [prefixWords_length]
    omega
  have headerBound : 4 < state.heap.size := by have := stored.bound; omega
  have headerCell : state.heap[4]? = some (word width oldCount) := by
    simpa [prefixWords] using stored.cell ⟨4, by omega⟩
  obtain ⟨middle, prepared, middlePC, middleRunning, middleHeap, middleStack, middleOutput,
      middleZero, middleCursor, middleRemember, middleSix, middleMask, middleFrame⟩ :=
    prepare_execution program entry rememberOriginal state
      (prefixWords width channels rows oldCount).length (word width oldCount)
      position running room positive prefixFits headerBound headerCell cursorReg maskReg prepareAt
  have middleStored : PrefixStored middle.heap channels rows newCount := by
    rw [middleHeap, selectedReg]
    exact prefix_store_count state.heap channels oldCount newCount rows stored
  obtain ⟨final, copyPeak, copied, copyBound, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalTwo, finalThree, finalFour, finalSix, finalSeven⟩ :=
    prefix_copy_execution program saveEntry headerEntry middle channels newCount rows middleStored
      (by simpa only [adjacent] using middlePC) middleRunning saveRoom headerRoom
      (by rw [sameLength]; exact prefixFits)
      (by rw [sameLength]; exact middleZero)
      (by rw [sameLength]; exact middleCursor) middleMask middleSix saveAt headerAt
  have middleLive : middle.liveWords = state.liveWords := by
    simp only [State.liveWords, middleHeap, Array.size_setIfInBounds, middleStack, middleOutput]
  refine ⟨final, max state.liveWords copyPeak, ?_, ?_, ?_, ?_,
    finalOutput.trans middleOutput, finalPC, finalRunning,
    finalTwo.trans middleRemember,
    finalThree.trans (middleFrame 3 (Or.inl rfl)), ?_,
    finalSix.trans middleSix, finalSeven.trans middleMask⟩
  · have scalar : 7 + (6 * ((prefixWords width channels rows newCount).length - 1) + 3) =
        6 * (prefixWords width channels rows newCount).length + 4 := by omega
    simpa only [scalar] using prepared.append copied
  · rw [middleLive] at copyBound
    exact Nat.max_le.mpr ⟨by omega, copyBound⟩
  · rw [finalHeap, middleHeap, selectedReg]
  · rw [finalStack, middleStack]
  · exact finalFour.trans ((middleFrame 4 (Or.inr (Or.inl rfl))).trans selectedReg)

/-- The copied prefix is the initial segment of the original packet, before its
root-occurrence column. Changing the selected count does not relocate any row. -/
theorem prefix_packet (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) :
    (ForestIndexedOperands.inputPacket channels 0 rows roots).map (word width) =
      prefixWords width channels rows roots.length ++ roots.map (word width) := by
  simp only [ForestIndexedOperands.inputPacket, Nat.zero_add,
    ForestIndexedOperands.packet_prefix_roots, List.map_append,
    ForestIndexedOperands.globalHeader, ForestIndexedOperands.countSource_value,
    Nat.zero_add, List.map_cons, List.map_nil, prefixWords, List.append_assoc]

private theorem values_source_option (heap : Array (Word width)) (values : Fin m → Bool)
    (index : Nat) (valid : index < heap.size) :
    (ForestInputStored.withValues heap values)[index]? = heap[index]? := by
  unfold ForestInputStored.withValues
  exact Array.getElem?_append_left valid

/-- Actual appended arrays retain the source prefix read by the projection
kernel. The node table is the output of the checked evaluator. -/
theorem evaluation_prefix_stored (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (assignment : Fin channels → Bool) (nodes : Fin k → Bool) :
    PrefixStored
      (ForestInputPrefixStored.evaluationHeap
        (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
      channels rows roots.length := by
  let before := prefixWords width channels rows roots.length
  let source := ForestIndexedOperands.cacheHeap width
    (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots
  have sourceEq : source = before.toArray ++ (roots.map (word width)).toArray := by
    dsimp only [source, before]
    rw [← UniformDAGRun.input_packet_cache, prefix_packet, List.append_toArray]
  have sizeBound : before.length ≤ source.size := by rw [sourceEq]; simp
  refine ⟨by
    change before.length ≤ _
    simp only [ForestInputPrefixStored.evaluationHeap_size]
    change before.length ≤ source.size + channels + k
    omega, ?_⟩
  intro index
  have inSource : index.val < source.size := lt_of_lt_of_le index.isLt sizeBound
  have inChannels : index.val < (ForestInputPrefixStored.channelHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment).size := by
    simp only [ForestInputPrefixStored.channelHeap_size]
    change index.val < source.size + channels
    omega
  change (ForestInputStored.withValues (ForestInputStored.withValues source assignment) nodes)[index.val]? =
    some (before[index.val]'(index.isLt))
  rw [values_source_option (ForestInputStored.withValues source assignment) nodes index.val (by
    simp only [ForestInputStored.withValues_size]
    omega), values_source_option source assignment index.val inSource,
    sourceEq, Array.getElem?_append_left (by
      simpa only [List.size_toArray] using (show index.val < before.length from index.isLt)),
    Array.getElem?_eq_getElem (by
      simpa only [List.size_toArray] using (show index.val < before.length from index.isLt))]
  rfl

/-- Root occurrences keep their original IDs after the real evaluator appends
channel and node tables. Repeated roots require separate stored positions. -/
theorem evaluation_roots_stored (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (assignment : Fin channels → Bool) (nodes : Fin k → Bool)
    (rootIds : ∀ root ∈ roots, root < k)
    (heapFits : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes).size < 2 ^ width) :
    Stored
      (ForestInputPrefixStored.evaluationHeap
        (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
      (prefixWords width channels rows roots.length).length
      (ForestInputPrefixStored.channelHeap
        (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment).size
      (roots.map (word width)) := by
  let source := ForestIndexedOperands.cacheHeap width
    (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots
  let channel := ForestInputPrefixStored.channelHeap
    (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment
  have sourceEq : source = (prefixWords width channels rows roots.length).toArray ++
      (roots.map (word width)).toArray := by
    dsimp only [source]
    rw [← UniformDAGRun.input_packet_cache, prefix_packet, List.append_toArray]
  have sourceSize : source.size = (prefixWords width channels rows roots.length).length + roots.length := by
    rw [sourceEq]
    simp
  have channelSize : channel.size = source.size + channels := by
    exact ForestInputPrefixStored.channelHeap_size _ _ _ _
  have fullSize : (ForestInputStored.withValues channel nodes).size = source.size + channels + k := by
    rw [ForestInputStored.withValues_size, channelSize]
  refine ⟨by
    simp only [List.length_map, ForestInputPrefixStored.evaluationHeap_size]
    change (prefixWords width channels rows roots.length).length + roots.length ≤ source.size + channels + k
    omega, ?_, ?_, by
      change channel.size < 2 ^ width
      change (ForestInputStored.withValues channel nodes).size < 2 ^ width at heapFits
      rw [ForestInputStored.withValues_size] at heapFits
      omega⟩
  · intro index
    have sourceBound : (prefixWords width channels rows roots.length).length + index.val < source.size := by
      rw [sourceSize]
      have valid := index.isLt
      simp only [List.length_map] at valid
      omega
    have channelBound : (prefixWords width channels rows roots.length).length + index.val < channel.size := by omega
    change (ForestInputStored.withValues channel nodes)[
      (prefixWords width channels rows roots.length).length + index.val]? = _
    rw [values_source_option channel nodes _ channelBound]
    change (ForestInputStored.withValues source assignment)[
      (prefixWords width channels rows roots.length).length + index.val]? = _
    rw [values_source_option source assignment _ sourceBound, sourceEq,
      Array.getElem?_append_right (by simp), List.size_toArray, Nat.add_sub_cancel_left,
      Array.getElem?_eq_getElem (by simpa using index.isLt)]
    rfl
  · intro root member
    obtain ⟨original, inRoots, rfl⟩ := List.mem_map.mp member
    have valid := rootIds original inRoots
    have originalFits : original < 2 ^ width := by
      have fullFits : (ForestInputStored.withValues channel nodes).size < 2 ^ width := heapFits
      rw [fullSize] at fullFits
      omega
    have originalValue : (word width original).val = original := Nat.mod_eq_of_lt originalFits
    change channel.size + (word width original).val < (ForestInputStored.withValues channel nodes).size
    rw [originalValue, ForestInputStored.withValues_size]
    omega


/-- Both classifications read node/incidence/channel counts from the original
source headers. On the second pass register two retains the original root count,
so the modified selected-count header four is never used as an original count. -/
def setupCode (width : Nat) (firstPass : Bool) : Program width 8 :=
  #[(if firstPass then .constant 0 (word width 4) else .copy 2 2),
    (if firstPass then .load 2 0 else .copy 2 2),
    .copy 4 2,
    .constant 0 (word width 1), .load 1 0,
    .add 1 1 1, .copy 5 1, .add 1 1 1, .add 1 1 5,
    .constant 0 (word width 2), .load 5 0, .add 1 1 5,
    .constant 0 (word width 3), .load 5 0, .add 1 1 5,
    .constant 0 (word width 5), .add 1 1 0,
    .add 1 1 2, .copy 5 1,
    .constant 0 (word width 0), .load 0 0, .add 5 5 0,
    .constant 3 (word width (2 ^ width - 1)), .constant 7 (word width 0)]

@[simp] theorem setupCode_size (width : Nat) (firstPass : Bool) :
    (setupCode width firstPass).size = 24 := by cases firstPass <;> rfl

/-- The source directory fixes the addresses of the original root cells and
appended node values. These are the natural projections of the loaded packet. -/
def rootStart (rows : List ForestIndexedOperands.Row) : Nat :=
  5 + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
    (ForestIndexedOperands.rowGuards rows).length

def sourceValueStart (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) : Nat := rootStart rows + roots.length + channels

@[simp] theorem rootStart_eq_prefix (channels count : Nat) (rows : List ForestIndexedOperands.Row) :
    rootStart rows = (prefixWords width channels rows count).length := by
  exact (prefixWords_length channels count rows).symm

/-- Once the second filter completes, its value-base register still points to
node zero. The count loaded from source header one reaches the actual final heap
end; the fetched copy saves that count across the second prefix-copy phase. -/
def saveHeapCountCode (width : Nat) : Program width 8 :=
  #[.constant 0 (word width 1), .load 0 0, .add 2 5 0]

@[simp] theorem saveHeapCountCode_size (width : Nat) :
    (saveHeapCountCode width).size = 3 := rfl

/-- Release count is loaded from the preserved runtime register, not supplied by
packet-copy semantics. -/
def releasePreparationCode : Program width 8 := #[.copy 0 2]

@[simp] theorem releasePreparationCode_size : (releasePreparationCode (width := width)).size = 1 := rfl

/-- The filter reads the node-value cell whose original ID occurs in each source
root position. Its result has the same ordering and duplicate occurrences as
filtering the original root stream by the completed evaluator's values. -/
theorem selected_source_values (heap : Array (Word width)) (valueBase : Nat)
    (healthy : Bool) (roots : List Nat) (values : Nat → Bool)
    (oneFits : 1 < 2 ^ width)
    (rootFits : ∀ root ∈ roots, root < 2 ^ width)
    (cells : ∀ root ∈ roots, heap[valueBase + root]? = some (boolWord width (values root))) :
    selected heap valueBase healthy (roots.map (word width)) =
      (roots.filter (fun root => values root == healthy)).map (word width) := by
  unfold selected
  rw [List.filter_map]
  apply congrArg (List.map (word width))
  apply List.filter_congr
  intro root member
  have rootValue : (word width root).val = root := Nat.mod_eq_of_lt (rootFits root member)
  simp only [Function.comp_apply, rootValue, cells root member, Option.map_some, Option.getD_some]
  cases value : values root <;>
    simp [boolWord, value, word, Nat.mod_eq_of_lt oneFits, Nat.zero_mod]

/-- Stores to the selected-count header leave every root occurrence and every
node-value cell intact. The second physical filter therefore reads the original
stream even though its query count header has changed. -/
theorem stored_count_header_frame (heap : Array (Word width)) (rootBase valueBase : Nat)
    (roots : List (Word width)) (stored : Stored heap rootBase valueBase roots)
    (rootStartBound : 5 ≤ rootBase) (valueStartBound : 5 ≤ valueBase)
    (count : Word width) : Stored (heap.setIfInBounds 4 count) rootBase valueBase roots := by
  refine ⟨by simpa only [Array.size_setIfInBounds] using stored.rootBound, ?_, ?_, stored.valueFits⟩
  · intro index
    rw [Array.getElem?_setIfInBounds, ite_eq_right (by omega : 4 ≠ rootBase + index.val)]
    exact stored.rootCell index
  · intro root member
    simpa only [Array.size_setIfInBounds] using stored.valueBound root member

/-- Node count is loaded from source header one and added to the retained
node-table base. The saved release word equals the executed heap size. -/
theorem save_heap_count_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (valueBase nodes : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (headerBound : 1 < state.heap.size)
    (headerCell : state.heap[1]? = some (word width nodes))
    (geometry : state.heap.size = valueBase + nodes)
    (heapFits : state.heap.size < 2 ^ width)
    (valueReg : state.reg 5 = word width valueBase)
    (present : RawTransferLoops.CodeAt program entry (saveHeapCountCode width)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 2 = word width state.heap.size ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 2 → final.reg register = state.reg register) := by
  let one := state.advance.put 0 (word width 1)
  let two := one.advance.put 0 (word width nodes)
  let final := two.advance.put 2 (word width state.heap.size)
  have fits : ∀ offset ≤ 3, entry + offset < 2 ^ width := by
    intro offset bound
    exact lt_of_le_of_lt (Nat.add_le_add_left bound entry) room
  have oneValue : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have nodeValue : (word width nodes).val = nodes := Nat.mod_eq_of_lt (by omega)
  have baseValue : (state.reg 5).val = valueBase := by
    rw [valueReg]
    exact Nat.mod_eq_of_lt (by omega)
  have first : programStep program state = some one := by
    rw [fetched program state entry _ position (fits 0 (by decide))
      (by simpa [saveHeapCountCode] using present ⟨0, by simp [saveHeapCountCode]⟩)]
    simp [step, running, one]
  have onePC : one.pc = word width (entry + 1) := by
    simpa [one, State.put] using advance_position state position (fits 0 (by decide))
  have second : programStep program one = some two := by
    rw [fetched program one (entry + 1) _ onePC (fits 1 (by decide))
      (by simpa [saveHeapCountCode] using present ⟨1, by simp [saveHeapCountCode]⟩)]
    have found : state.heap[1] = word width nodes := by
      simpa only [Array.getElem?_eq_getElem headerBound, Option.some.injEq] using headerCell
    simp [step, one, two, State.put, State.advance, running, oneValue, headerBound, found]
  have twoPC : two.pc = word width (entry + 2) := by
    simpa [two, State.put, Nat.add_assoc] using advance_position one onePC (fits 1 (by decide))
  have third : programStep program two = some final := by
    rw [fetched program two (entry + 2) _ twoPC (fits 2 (by decide))
      (by simpa [saveHeapCountCode] using present ⟨2, by simp [saveHeapCountCode]⟩)]
    simp only [step, two, one, State.put, State.advance, running, Bool.false_eq_true,
      ite_false, Fin.reduceEq, ite_true, baseValue, nodeValue]
    rw [← geometry]
    simp only [final, two, one, State.put, State.advance, running]
  have oneLive : one.liveWords = state.liveWords := rfl
  have twoLive : two.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  have joined := Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl final)))
  refine ⟨final, by simpa only [oneLive, twoLive, finalLive, Nat.max_self] using joined,
    ?_, running, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [final, State.put, Nat.add_assoc] using advance_position two twoPC (fits 2 (by decide))
  · simp [final, State.put]
  · intro register zero twoNe
    simp [final, two, one, State.put, State.advance, zero, twoNe]

/-- The count retained through both physical prefix copies is read by the
release loop. The source heap is discarded only after both packets are saved. -/
theorem release_saved_heap_execution (program : Program width 8) (entry releaseEntry done : Nat)
    (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 1 < 2 ^ width) (releaseRoom : releaseEntry + 4 < 2 ^ width)
    (adjacent : entry + 1 = releaseEntry) (heapFits : state.heap.size < 2 ^ width)
    (countReg : state.reg 2 = word width state.heap.size)
    (maskReg : state.reg 7 = word width (2 ^ width - 1))
    (zeroReg : state.reg 6 = word width 0)
    (copyAt : program[entry]? = some (.copy 0 2))
    (releaseAt : RawTransferLoops.CodeAt program releaseEntry
      (RawTransferLoops.countedReleaseCode width releaseEntry done)) :
    ∃ final peak, Execution program state final (4 * state.heap.size + 2) peak ∧
      peak ≤ state.liveWords ∧ final.heap = #[] ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 := by
  let prepared := state.advance.put 0 (word width state.heap.size)
  have stepCopy : programStep program state = some prepared := by
    rw [fetched program state entry _ position (by omega) copyAt]
    simp [step, running, countReg, prepared]
  have preparedPC : prepared.pc = word width releaseEntry := by
    rw [← adjacent]
    simpa [prepared, State.put] using advance_position state position (by omega)
  have preparedZero : prepared.reg 0 = word width state.heap.size := by simp [prepared, State.put]
  have preparedLive : prepared.liveWords = state.liveWords := rfl
  have initial : Execution program state prepared 1 state.liveWords := by
    simpa only [preparedLive, Nat.max_self] using Execution.cons stepCopy (Execution.refl prepared)
  obtain ⟨final, lastPeak, last, lastBound, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalZero, finalFrame⟩ :=
    RawTransferLoops.counted_release_execution program releaseEntry done state.heap.size prepared
      preparedPC running releaseRoom rfl heapFits preparedZero
      (by simpa [prepared, State.put, State.advance] using maskReg)
      (by simpa [prepared, State.put, State.advance] using zeroReg) releaseAt
  refine ⟨final, max state.liveWords lastPeak, ?_, ?_, finalHeap, finalStack,
    finalOutput, finalPC, finalRunning, finalZero⟩
  · have total : 1 + (4 * state.heap.size + 1) = 4 * state.heap.size + 2 := by omega
    simpa only [total] using initial.append last
  · rw [preparedLive] at lastBound
    exact Nat.max_le.mpr ⟨le_rfl, lastBound⟩

/-- Classification setup reads only the four immutable source-count headers.
Header four is deliberately excluded because it changes between projections. -/
structure ShapeStored (heap : Array (Word width)) (channels nodes children guards : Nat) : Prop where
  bound : 5 ≤ heap.size
  channelsCell : heap[0]? = some (word width channels)
  nodesCell : heap[1]? = some (word width nodes)
  childrenCell : heap[2]? = some (word width children)
  guardsCell : heap[3]? = some (word width guards)

theorem shape_of_prefix (heap : Array (Word width)) (channels count : Nat)
    (rows : List ForestIndexedOperands.Row) (stored : PrefixStored heap channels rows count) :
    ShapeStored heap channels rows.length (ForestIndexedOperands.rowChildren rows).length
      (ForestIndexedOperands.rowGuards rows).length := by
  have prefixLength : 5 ≤ (prefixWords width channels rows count).length := by
    rw [prefixWords_length]
    omega
  refine ⟨by have := stored.bound; omega, ?_, ?_, ?_, ?_⟩
  · simpa [prefixWords] using stored.cell ⟨0, by omega⟩
  · simpa [prefixWords] using stored.cell ⟨1, by omega⟩
  · simpa [prefixWords] using stored.cell ⟨2, by omega⟩
  · simpa [prefixWords] using stored.cell ⟨3, by omega⟩

theorem shape_count_header_frame (heap : Array (Word width)) (channels nodes children guards : Nat)
    (stored : ShapeStored heap channels nodes children guards) (count : Word width) :
    ShapeStored (heap.setIfInBounds 4 count) channels nodes children guards := by
  refine ⟨by simpa only [Array.size_setIfInBounds] using stored.bound, ?_, ?_, ?_, ?_⟩
  all_goals rw [Array.getElem?_setIfInBounds, ite_eq_right (by decide)]
  · exact stored.channelsCell
  · exact stored.nodesCell
  · exact stored.childrenCell
  · exact stored.guardsCell

/-- The release endpoint is read from the same source geometry as the setup.
It is the size of the real completed evaluation heap, not an external count. -/
theorem source_heap_end (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (assignment : Fin channels → Bool) (nodes : Fin rows.length → Bool) :
    (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes).size =
      sourceValueStart channels rows roots + rows.length := by
  simp only [ForestInputPrefixStored.evaluationHeap_size, ForestIndexedOperands.cacheHeap_size,
    UniformDAGRun.packetHeaderHeap_size, ForestIndexedOperands.serializedRows_length,
    sourceValueStart, rootStart]

/-- The two classifications partition occurrences, including repeated IDs.
Consequently their saved root words occupy exactly the original root count. -/
theorem selected_partition_length (heap : Array (Word width)) (valueBase : Nat)
    (roots : List (Word width)) :
    (selected heap valueBase true roots).length +
      (selected heap valueBase false roots).length = roots.length := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
    cases bit : (heap[valueBase + root.val]?.map (fun value => value.val != 0)).getD false <;>
      simp [selected, List.filter_cons, bit] at ih ⊢ <;> omega

/-- Writing a projected count cannot affect the completed node-value table.
The second filter reads the same physical bits as the first. -/
theorem selected_count_header_frame (heap : Array (Word width)) (valueBase : Nat)
    (healthy : Bool) (roots : List (Word width)) (above : 5 ≤ valueBase) (count : Word width) :
    selected (heap.setIfInBounds 4 count) valueBase healthy roots =
      selected heap valueBase healthy roots := by
  unfold selected
  apply List.filter_congr
  intro root member
  rw [Array.getElem?_setIfInBounds, ite_eq_right (by omega : 4 ≠ valueBase + root.val)]

/-- Projection stack space includes two source prefixes but only one copy of
all root occurrences. The original eval heap remains until those copies finish. -/
theorem projected_packets_length (heap : Array (Word width)) (channels : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List (Word width)) (valueBase : Nat) :
    (prefixWords width channels rows (selected heap valueBase true roots).length ++
        selected heap valueBase true roots ++
        prefixWords width channels rows (selected heap valueBase false roots).length ++
        selected heap valueBase false roots).length =
      2 * (5 + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards rows).length) + roots.length := by
  simp only [List.length_append, prefixWords_length]
  have partition := selected_partition_length heap valueBase roots
  omega

/-- Two fetched instructions read a source-count cell. This block is used for
all count-header reads in the setup, with a physical index and allocated cell. -/
private theorem read_source_count_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (index : Nat) (destination : Fin 8) (value : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (indexFits : index < 2 ^ width)
    (valid : index < state.heap.size) (cell : state.heap[index]? = some value)
    (constantAt : program[entry]? = some (.constant 0 (word width index)))
    (loadAt : program[entry + 1]? = some (.load destination 0)) :
    let final := (state.advance.put 0 (word width index)).advance.put destination value
    Execution program state final 2 state.liveWords ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg destination = value ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ destination →
        final.reg register = state.reg register) := by
  let middle := state.advance.put 0 (word width index)
  let final := middle.advance.put destination value
  have first : programStep program state = some middle := by
    rw [fetched program state entry _ position (by omega) constantAt]
    simp [step, running, middle]
  have middlePC : middle.pc = word width (entry + 1) := by
    simpa [middle, State.put] using advance_position state position (by omega)
  have address : (middle.reg 0).val = index := by
    simp only [middle, State.put, ite_true]
    exact Nat.mod_eq_of_lt indexFits
  have found : state.heap[index] = value := by
    simpa only [Array.getElem?_eq_getElem valid, Option.some.injEq] using cell
  have second : programStep program middle = some final := by
    rw [fetched program middle (entry + 1) _ middlePC (by omega) loadAt]
    simp [step, middle, final, State.put, State.advance, running, word,
      Nat.mod_eq_of_lt indexFits, valid, found]
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨by simpa only [middleLive, finalLive, Nat.max_self] using
    Execution.cons first (Execution.cons second (Execution.refl final)), ?_, running,
    rfl, rfl, rfl, ?_, ?_⟩
  · change middle.advance.pc = word width (entry + 2)
    simpa only [Nat.add_assoc] using advance_position middle middlePC (by omega)
  · simp [final, State.put]
  · intro register zero other
    simp [final, middle, State.put, State.advance, zero, other]

/-- A scalar addition is one fetched RAM instruction. Only its two resident
register values are decoded; later phases establish the no-wrap bounds needed
when the result is read again. -/
private theorem add_register_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (destination left right : Fin 8) (a b : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 1 < 2 ^ width) (aFits : a < 2 ^ width) (bFits : b < 2 ^ width)
    (leftReg : state.reg left = word width a) (rightReg : state.reg right = word width b)
    (present : program[entry]? = some (.add destination left right)) :
    let final := state.advance.put destination (word width (a + b))
    Execution program state final 1 state.liveWords ∧
      final.pc = word width (entry + 1) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg destination = word width (a + b) ∧
      (∀ register : Fin 8, register ≠ destination → final.reg register = state.reg register) := by
  let final := state.advance.put destination (word width (a + b))
  have leftValue : (state.reg left).val = a := by rw [leftReg]; exact Nat.mod_eq_of_lt aFits
  have rightValue : (state.reg right).val = b := by rw [rightReg]; exact Nat.mod_eq_of_lt bFits
  have transition : programStep program state = some final := by
    rw [fetched program state entry _ position (by omega) present]
    simp only [step, running, Bool.false_eq_true, ite_false, leftValue, rightValue]
    rfl
  have live : final.liveWords = state.liveWords := rfl
  refine ⟨by simpa only [live, Nat.max_self] using Execution.cons transition (Execution.refl final),
    ?_, running, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [final, State.put] using advance_position state position (by omega)
  · simp [final, State.put]
  · intro register different
    simp [final, State.put, State.advance, different]

/-- Pure arithmetic of the actual source headers bounds every intermediate
address in the fixed setup by the completed original evaluation heap end. -/
theorem setup_intermediate_bounds (channels nodes children guards roots : Nat)
    (capacity : 5 + 6 * nodes + children + guards + roots + channels + nodes < 2 ^ width) :
    nodes < 2 ^ width ∧ 2 * nodes < 2 ^ width ∧ 4 * nodes < 2 ^ width ∧
      6 * nodes < 2 ^ width ∧ 6 * nodes + children < 2 ^ width ∧
      6 * nodes + children + guards < 2 ^ width ∧
      5 + 6 * nodes + children + guards < 2 ^ width ∧
      5 + 6 * nodes + children + guards + roots < 2 ^ width ∧
      5 + 6 * nodes + children + guards + roots + channels < 2 ^ width ∧
      children < 2 ^ width ∧ guards < 2 ^ width ∧ roots < 2 ^ width ∧
      channels < 2 ^ width ∧ 5 < 2 ^ width := by omega

/-- The six-instruction node-header block computes the physical six-word row
column extent. Its count comes from source header one. -/
private theorem node_extent_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (nodes : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 6 < 2 ^ width) (extentFits : 6 * nodes < 2 ^ width)
    (oneFits : 1 < 2 ^ width) (valid : 1 < state.heap.size)
    (cell : state.heap[1]? = some (word width nodes))
    (atCode : RawTransferLoops.CodeAt program entry
      #[.constant 0 (word width 1), .load 1 0, .add 1 1 1,
        .copy 5 1, .add 1 1 1, .add 1 1 5]) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.pc = word width (entry + 6) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 1 = word width (6 * nodes) ∧ final.reg 5 = word width (2 * nodes) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 5 →
        final.reg register = state.reg register) := by
  let two := (state.advance.put 0 (word width 1)).advance.put 1 (word width nodes)
  obtain ⟨readTrace, twoPC, twoRunning, twoHeap, twoStack, twoOutput, twoReg, twoFrame⟩ :=
    read_source_count_execution program entry state 1 1 (word width nodes)
      position running (by omega) oneFits valid cell
      (by simpa using atCode ⟨0, by simp [setupCode, saveHeapCountCode]⟩)
      (by simpa using atCode ⟨1, by simp [setupCode, saveHeapCountCode]⟩)
  let three := two.advance.put 1 (word width (nodes + nodes))
  obtain ⟨doubleTrace, threePC, threeRunning, threeHeap, threeStack, threeOutput, threeReg, threeFrame⟩ :=
    add_register_execution program (entry + 2) two 1 1 1 nodes nodes twoPC twoRunning
      (by omega) (by omega) (by omega) twoReg twoReg
      (by simpa [Nat.add_assoc] using atCode ⟨2, by simp [setupCode, saveHeapCountCode]⟩)
  let four := three.advance.put 5 (word width (2 * nodes))
  have threeTwice : three.reg 1 = word width (2 * nodes) := by
    simpa only [two_mul] using threeReg
  have copyStep : programStep program three = some four := by
    rw [fetched program three (entry + 3) _ threePC (by omega)
      (by simpa [Nat.add_assoc] using atCode ⟨3, by simp [setupCode, saveHeapCountCode]⟩)]
    simp [step, four, three, two, State.put, State.advance, running, two_mul]
  have fourPC : four.pc = word width (entry + 4) := by
    simpa [four, State.put, Nat.add_assoc] using advance_position three threePC (by omega)
  have fourRunning : four.halted = false := threeRunning
  have fourOne : four.reg 1 = word width (2 * nodes) := by
    simpa [four, State.put, State.advance] using threeTwice
  have fourFive : four.reg 5 = word width (2 * nodes) := by simp [four, State.put]
  let five := four.advance.put 1 (word width (2 * nodes + 2 * nodes))
  obtain ⟨doubleAgain, fivePC, fiveRunning, fiveHeap, fiveStack, fiveOutput, fiveReg, fiveFrame⟩ :=
    add_register_execution program (entry + 4) four 1 1 1 (2 * nodes) (2 * nodes)
      fourPC fourRunning (by omega) (by omega) (by omega) fourOne fourOne
      (by simpa [Nat.add_assoc] using atCode ⟨4, by simp [setupCode, saveHeapCountCode]⟩)
  have fiveFour : five.reg 1 = word width (4 * nodes) := by
    have scalar : 2 * nodes + 2 * nodes = 4 * nodes := by omega
    change word width (2 * nodes + 2 * nodes) = word width (4 * nodes)
    exact congrArg (word width) scalar
  have fiveFive : five.reg 5 = word width (2 * nodes) :=
    (fiveFrame 5 (by decide)).trans fourFive
  let final := five.advance.put 1 (word width (4 * nodes + 2 * nodes))
  obtain ⟨last, finalPC, finalRunning, finalHeap, finalStack, finalOutput, finalOne, finalFrame⟩ :=
    add_register_execution program (entry + 5) five 1 1 5 (4 * nodes) (2 * nodes)
      fivePC fiveRunning (by omega) (by omega) (by omega) fiveFour fiveFive
      (by simpa [Nat.add_assoc] using atCode ⟨5, by simp [setupCode, saveHeapCountCode]⟩)
  have twoLive : two.liveWords = state.liveWords := rfl
  have threeLive : three.liveWords = state.liveWords := rfl
  have fourLive : four.liveWords = state.liveWords := rfl
  have fiveLive : five.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  have copyTrace : Execution program three four 1 state.liveWords := by
    simpa only [fourLive, threeLive, Nat.max_self] using Execution.cons copyStep (Execution.refl four)
  have joined := ((readTrace.append doubleTrace).append copyTrace).append (doubleAgain.append last)
  refine ⟨final, ?_, ?_, finalRunning, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa only [twoLive, threeLive, fourLive, fiveLive, finalLive, Nat.max_self] using joined
  · simpa only [Nat.add_assoc] using finalPC
  · have scalar : 4 * nodes + 2 * nodes = 6 * nodes := by omega
    change word width (4 * nodes + 2 * nodes) = word width (6 * nodes)
    exact congrArg (word width) scalar
  · exact (finalFrame 5 (by decide)).trans fiveFive
  · intro register n0 n1 n5
    simp only [final, five, four, three, two, State.put, State.advance, ite_eq_right n1,
      ite_eq_right n5, ite_eq_right n0]

/-- A three-instruction count/address block loads an incidence or channel count
from the original header and adds it to the live cursor. -/
private theorem read_add_count_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (index : Nat) (destination temporary : Fin 8) (before count : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (indexFits : index < 2 ^ width)
    (valid : index < state.heap.size) (cell : state.heap[index]? = some (word width count))
    (beforeFits : before < 2 ^ width) (countFits : count < 2 ^ width)
    (beforeReg : state.reg destination = word width before)
    (destinationZero : destination ≠ 0) (distinct : destination ≠ temporary)
    (atCode : RawTransferLoops.CodeAt program entry
      #[.constant 0 (word width index), .load temporary 0, .add destination destination temporary]) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg destination = word width (before + count) ∧
      final.reg temporary = word width count ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ temporary → register ≠ destination →
        final.reg register = state.reg register) := by
  let middle := (state.advance.put 0 (word width index)).advance.put temporary (word width count)
  obtain ⟨readTrace, middlePC, middleRunning, middleHeap, middleStack, middleOutput,
      middleValue, middleFrame⟩ :=
    read_source_count_execution program entry state index temporary (word width count)
      position running (by omega) indexFits valid cell
      (by simpa using atCode ⟨0, by simp [setupCode, saveHeapCountCode]⟩)
      (by simpa using atCode ⟨1, by simp [setupCode, saveHeapCountCode]⟩)
  have middleDestination : middle.reg destination = word width before :=
    (middleFrame destination destinationZero distinct).trans beforeReg
  let final := middle.advance.put destination (word width (before + count))
  obtain ⟨last, finalPC, finalRunning, finalHeap, finalStack, finalOutput, finalValue, finalFrame⟩ :=
    add_register_execution program (entry + 2) middle destination destination temporary before count
      middlePC middleRunning (by omega) beforeFits countFits middleDestination middleValue
      (by simpa [Nat.add_assoc] using atCode ⟨2, by simp [setupCode, saveHeapCountCode]⟩)
  have middleLive : middle.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, ?_, finalRunning,
    finalHeap.trans middleHeap, finalStack.trans middleStack, finalOutput.trans middleOutput,
    finalValue, (finalFrame temporary (Ne.symm distinct)).trans middleValue, ?_⟩
  · simpa only [middleLive, Nat.max_self] using readTrace.append last
  · simpa only [Nat.add_assoc] using finalPC
  · intro register zero temp dest
    exact (finalFrame register dest).trans (middleFrame register zero temp)

/-- Original root count is physically loaded on the first pass, and retained in
register two on the second pass. The selected-count header can therefore change
without altering the second traversal's original occurrence count. -/
private theorem root_count_execution (program : Program width 8) (entry : Nat)
    (firstPass : Bool) (state : State width 8) (roots : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (fourFits : 4 < 2 ^ width) (valid : 4 < state.heap.size)
    (initialCount : firstPass = true → state.heap[4]? = some (word width roots))
    (retained : firstPass = false → state.reg 2 = word width roots)
    (atCode : RawTransferLoops.CodeAt program entry
      #[(if firstPass then .constant 0 (word width 4) else .copy 2 2),
        (if firstPass then .load 2 0 else .copy 2 2), .copy 4 2]) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 2 = word width roots ∧ final.reg 4 = word width roots ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 2 → register ≠ 4 →
        final.reg register = state.reg register) := by
  let one := if firstPass then state.advance.put 0 (word width 4)
    else state.advance.put 2 (word width roots)
  let two := one.advance.put 2 (word width roots)
  let final := two.advance.put 4 (word width roots)
  have first : programStep program state = some one := by
    cases flag : firstPass
    · rw [fetched program state entry _ position (by omega)
        (by simpa [flag] using atCode ⟨0, by simp [setupCode, saveHeapCountCode]⟩)]
      simp [step, running, one, flag, retained flag]
    · rw [fetched program state entry _ position (by omega)
        (by simpa [flag] using atCode ⟨0, by simp [setupCode, saveHeapCountCode]⟩)]
      simp [step, running, one, flag]
  have onePC : one.pc = word width (entry + 1) := by
    cases firstPass <;> simpa [one, State.put] using advance_position state position (by omega)
  have second : programStep program one = some two := by
    cases flag : firstPass
    · rw [fetched program one (entry + 1) _ onePC (by omega)
        (by simpa [flag] using atCode ⟨1, by simp [setupCode, saveHeapCountCode]⟩)]
      simp [step, one, two, flag, State.put, State.advance, running]
    · rw [fetched program one (entry + 1) _ onePC (by omega)
        (by simpa [flag] using atCode ⟨1, by simp [setupCode, saveHeapCountCode]⟩)]
      have fourValue : (word width 4).val = 4 := Nat.mod_eq_of_lt fourFits
      have found : state.heap[4] = word width roots := by
        simpa only [Array.getElem?_eq_getElem valid, Option.some.injEq] using initialCount flag
      simp [step, one, two, flag, State.put, State.advance, running, fourValue, valid, found]
  have twoPC : two.pc = word width (entry + 2) := by
    simpa [two, State.put, Nat.add_assoc] using advance_position one onePC (by omega)
  have twoCount : two.reg 2 = word width roots := by simp [two, State.put]
  have third : programStep program two = some final := by
    rw [fetched program two (entry + 2) _ twoPC (by omega)
      (by simpa using atCode ⟨2, by simp [setupCode, saveHeapCountCode]⟩)]
    have twoRunning : two.halted = false := by cases firstPass <;> simpa [two, one, State.put, State.advance] using running
    simp only [step, twoRunning, Bool.false_eq_true, ite_false, twoCount]
    rfl
  have oneLive : one.liveWords = state.liveWords := by cases firstPass <;> rfl
  have twoLive : two.liveWords = state.liveWords := by
    change one.liveWords = state.liveWords
    exact oneLive
  have finalLive : final.liveWords = state.liveWords := by
    change two.liveWords = state.liveWords
    exact twoLive
  refine ⟨final, by simpa only [oneLive, twoLive, finalLive, Nat.max_self] using
    (Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl final)))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [final, State.put, Nat.add_assoc] using advance_position two twoPC (by omega)
  · cases firstPass <;> simpa [final, two, one, State.put, State.advance] using running
  · cases firstPass <;> rfl
  · cases firstPass <;> rfl
  · cases firstPass <;> rfl
  · change two.reg 2 = word width roots
    exact twoCount
  · simp [final, State.put]
  · intro register zero count selected
    cases firstPass <;> simp [final, two, one, State.put, State.advance, zero, count, selected]

private theorem constant_add_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (destination temporary : Fin 8) (before addend : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (beforeFits : before < 2 ^ width) (addendFits : addend < 2 ^ width)
    (beforeReg : state.reg destination = word width before) (distinct : destination ≠ temporary)
    (atCode : RawTransferLoops.CodeAt program entry
      #[.constant temporary (word width addend), .add destination destination temporary]) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg destination = word width (before + addend) ∧
      (∀ register : Fin 8, register ≠ temporary → register ≠ destination →
        final.reg register = state.reg register) := by
  let middle := state.advance.put temporary (word width addend)
  have first : programStep program state = some middle := by
    rw [fetched program state entry _ position (by omega)
      (by simpa using atCode ⟨0, by simp [setupCode, saveHeapCountCode]⟩)]
    simp [step, running, middle]
  have middlePC : middle.pc = word width (entry + 1) := by
    simpa [middle, State.put] using advance_position state position (by omega)
  have middleValue : middle.reg temporary = word width addend := by simp [middle, State.put]
  have middleBase : middle.reg destination = word width before := by
    simpa [middle, State.put, State.advance, distinct] using beforeReg
  let final := middle.advance.put destination (word width (before + addend))
  obtain ⟨last, finalPC, finalRunning, finalHeap, finalStack, finalOutput, finalValue, finalFrame⟩ :=
    add_register_execution program (entry + 1) middle destination destination temporary before addend
      middlePC running (by omega) beforeFits addendFits middleBase middleValue
      (by simpa using atCode ⟨1, by simp [setupCode, saveHeapCountCode]⟩)
  have middleLive : middle.liveWords = state.liveWords := rfl
  have firstTrace : Execution program state middle 1 state.liveWords := by
    simpa only [middleLive, Nat.max_self] using Execution.cons first (Execution.refl middle)
  refine ⟨final, by simpa only [middleLive, Nat.max_self] using firstTrace.append last,
    ?_, finalRunning, finalHeap, finalStack, finalOutput, finalValue, ?_⟩
  · simpa only [Nat.add_assoc] using finalPC
  · intro register temp dest
    exact (finalFrame register dest).trans (by simp [middle, State.put, State.advance, temp])

private theorem root_end_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (base count : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (baseFits : base < 2 ^ width) (countFits : count < 2 ^ width)
    (baseReg : state.reg 1 = word width base) (countReg : state.reg 2 = word width count)
    (atCode : RawTransferLoops.CodeAt program entry #[.add 1 1 2, .copy 5 1]) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 1 = word width (base + count) ∧ final.reg 5 = word width (base + count) ∧
      (∀ register : Fin 8, register ≠ 1 → register ≠ 5 → final.reg register = state.reg register) := by
  let middle := state.advance.put 1 (word width (base + count))
  obtain ⟨first, middlePC, middleRunning, middleHeap, middleStack, middleOutput, middleValue, middleFrame⟩ :=
    add_register_execution program entry state 1 1 2 base count position running (by omega)
      baseFits countFits baseReg countReg (by simpa using atCode ⟨0, by simp [setupCode, saveHeapCountCode]⟩)
  let final := middle.advance.put 5 (word width (base + count))
  have lastStep : programStep program middle = some final := by
    rw [fetched program middle (entry + 1) _ middlePC (by omega)
      (by simpa using atCode ⟨1, by simp [setupCode, saveHeapCountCode]⟩)]
    simp [step, middle, final, State.put, State.advance, running]
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  have last : Execution program middle final 1 state.liveWords := by
    simpa only [middleLive, finalLive, Nat.max_self] using Execution.cons lastStep (Execution.refl final)
  refine ⟨final, by simpa only [Nat.max_self] using first.append last,
    ?_, middleRunning, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · change middle.advance.pc = word width (entry + 2)
    simpa only [Nat.add_assoc] using advance_position middle middlePC (by omega)
  · change middle.reg 1 = word width (base + count)
    exact middleValue
  · simp [final, State.put]
  · intro register one five
    exact (show final.reg register = middle.reg register by simp [final, State.put, State.advance, five]).trans
      (middleFrame register one)

private theorem finish_setup_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 2 < 2 ^ width)
    (atCode : RawTransferLoops.CodeAt program entry
      #[.constant 3 (word width (2 ^ width - 1)), .constant 7 (word width 0)]) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.pc = word width (entry + 2) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 3 = word width (2 ^ width - 1) ∧ final.reg 7 = word width 0 ∧
      (∀ register : Fin 8, register ≠ 3 → register ≠ 7 → final.reg register = state.reg register) := by
  let middle := state.advance.put 3 (word width (2 ^ width - 1))
  let final := middle.advance.put 7 (word width 0)
  have first : programStep program state = some middle := by
    rw [fetched program state entry _ position (by omega)
      (by simpa using atCode ⟨0, by simp [setupCode, saveHeapCountCode]⟩)]
    simp [step, running, middle]
  have middlePC : middle.pc = word width (entry + 1) := by
    simpa [middle, State.put] using advance_position state position (by omega)
  have last : programStep program middle = some final := by
    rw [fetched program middle (entry + 1) _ middlePC (by omega)
      (by simpa using atCode ⟨1, by simp [setupCode, saveHeapCountCode]⟩)]
    simp [step, running, middle, final, State.advance, State.put]
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, by simpa only [middleLive, finalLive, Nat.max_self] using
    (Execution.cons first (Execution.cons last (Execution.refl final))), ?_, running,
    rfl, rfl, rfl, ?_, ?_, ?_⟩
  · change middle.advance.pc = word width (entry + 2)
    simpa only [Nat.add_assoc] using advance_position middle middlePC (by omega)
  · simp [final, middle, State.put, State.advance]
  · simp [final, State.put]
  · intro register three seven
    simp [final, middle, State.put, State.advance, three, seven]

/-- The complete fixed setup derives the original occurrence count, source root
cursor, node-value base, decrement mask and zero from the actual source headers.
The second execution uses the original count retained by the first packet copy. -/
theorem setup_execution (program : Program width 8) (entry : Nat) (firstPass : Bool)
    (state : State width 8) (channels nodes children guards roots : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 24 < 2 ^ width)
    (capacity : 5 + 6 * nodes + children + guards + roots + channels + nodes < 2 ^ width)
    (shape : ShapeStored state.heap channels nodes children guards)
    (initialCount : firstPass = true → state.heap[4]? = some (word width roots))
    (retained : firstPass = false → state.reg 2 = word width roots)
    (present : RawTransferLoops.CodeAt program entry (setupCode width firstPass)) :
    ∃ final, Execution program state final 24 state.liveWords ∧
      final.pc = word width (entry + 24) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 1 = word width (5 + 6 * nodes + children + guards + roots) ∧
      final.reg 2 = word width roots ∧ final.reg 4 = word width roots ∧
      final.reg 3 = word width (2 ^ width - 1) ∧
      final.reg 5 = word width (5 + 6 * nodes + children + guards + roots + channels) ∧
      final.reg 7 = word width 0 := by
  have rootAt : RawTransferLoops.CodeAt program entry
      #[(if firstPass then .constant 0 (word width 4) else .copy 2 2),
        (if firstPass then .load 2 0 else .copy 2 2), .copy 4 2] := by
    intro index
    fin_cases index
    · simpa [setupCode] using present ⟨0, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode] using present ⟨1, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode] using present ⟨2, by simp [setupCode, saveHeapCountCode]⟩
  obtain ⟨a, rootTrace, aPC, aRunning, aHeap, aStack, aOutput, aCount, aSelected, aFrame⟩ :=
    root_count_execution program entry firstPass state roots position running (by omega)
      (by omega) (by have := shape.bound; omega) initialCount retained rootAt
  have nodeAt : RawTransferLoops.CodeAt program (entry + 3)
      #[.constant 0 (word width 1), .load 1 0, .add 1 1 1,
        .copy 5 1, .add 1 1 1, .add 1 1 5] := by
    intro index
    fin_cases index
    · simpa [setupCode, Nat.add_assoc] using present ⟨3, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨4, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨5, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨6, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨7, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨8, by simp [setupCode, saveHeapCountCode]⟩
  obtain ⟨b, nodeTrace, bPC, bRunning, bHeap, bStack, bOutput, bOne, bFive, bFrame⟩ :=
    node_extent_execution program (entry + 3) a nodes aPC aRunning (by omega)
      (by omega) (by omega) (by rw [aHeap]; have := shape.bound; omega)
      (by rw [aHeap]; exact shape.nodesCell) nodeAt
  have childAt : RawTransferLoops.CodeAt program (entry + 9)
      #[.constant 0 (word width 2), .load 5 0, .add 1 1 5] := by
    intro index
    fin_cases index
    · simpa [setupCode, Nat.add_assoc] using present ⟨9, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨10, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨11, by simp [setupCode, saveHeapCountCode]⟩
  obtain ⟨c, childTrace, cPC, cRunning, cHeap, cStack, cOutput, cOne, cFive, cFrame⟩ :=
    read_add_count_execution program (entry + 9) b 2 1 5 (6 * nodes) children bPC bRunning
      (by omega) (by omega) (by rw [bHeap, aHeap]; have := shape.bound; omega)
      (by rw [bHeap, aHeap]; exact shape.childrenCell) (by omega) (by omega) bOne
      (by decide) (by decide) childAt
  have guardAt : RawTransferLoops.CodeAt program (entry + 12)
      #[.constant 0 (word width 3), .load 5 0, .add 1 1 5] := by
    intro index
    fin_cases index
    · simpa [setupCode, Nat.add_assoc] using present ⟨12, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨13, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨14, by simp [setupCode, saveHeapCountCode]⟩
  obtain ⟨d, guardTrace, dPC, dRunning, dHeap, dStack, dOutput, dOne, dFive, dFrame⟩ :=
    read_add_count_execution program (entry + 12) c 3 1 5 (6 * nodes + children) guards cPC cRunning
      (by omega) (by omega) (by rw [cHeap, bHeap, aHeap]; have := shape.bound; omega)
      (by rw [cHeap, bHeap, aHeap]; exact shape.guardsCell) (by omega) (by omega) cOne
      (by decide) (by decide) guardAt
  have literalAt : RawTransferLoops.CodeAt program (entry + 15)
      #[.constant 0 (word width 5), .add 1 1 0] := by
    intro index
    fin_cases index
    · simpa [setupCode, Nat.add_assoc] using present ⟨15, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨16, by simp [setupCode, saveHeapCountCode]⟩
  obtain ⟨e, literalTrace, ePC, eRunning, eHeap, eStack, eOutput, eOneRaw, eFrame⟩ :=
    constant_add_execution program (entry + 15) d 1 0 (6 * nodes + children + guards) 5
      dPC dRunning (by omega) (by omega) (by omega) dOne (by decide) literalAt
  have baseEq : 6 * nodes + children + guards + 5 = 5 + 6 * nodes + children + guards := by omega
  have eOne : e.reg 1 = word width (5 + 6 * nodes + children + guards) := by
    simpa only [baseEq] using eOneRaw
  have eCount : e.reg 2 = word width roots :=
    (eFrame 2 (by decide) (by decide)).trans
      ((dFrame 2 (by decide) (by decide) (by decide)).trans
        ((cFrame 2 (by decide) (by decide) (by decide)).trans
          ((bFrame 2 (by decide) (by decide) (by decide)).trans aCount)))
  have endAt : RawTransferLoops.CodeAt program (entry + 17) #[.add 1 1 2, .copy 5 1] := by
    intro index
    fin_cases index
    · simpa [setupCode, Nat.add_assoc] using present ⟨17, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨18, by simp [setupCode, saveHeapCountCode]⟩
  obtain ⟨f, endTrace, fPC, fRunning, fHeap, fStack, fOutput, fOne, fFive, fFrame⟩ :=
    root_end_execution program (entry + 17) e (5 + 6 * nodes + children + guards) roots
      ePC eRunning (by omega) (by omega) (by omega) eOne eCount endAt
  have channelAt : RawTransferLoops.CodeAt program (entry + 19)
      #[.constant 0 (word width 0), .load 0 0, .add 5 5 0] := by
    intro index
    fin_cases index
    · simpa [setupCode, Nat.add_assoc] using present ⟨19, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨20, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨21, by simp [setupCode, saveHeapCountCode]⟩
  obtain ⟨g, channelTrace, gPC, gRunning, gHeap, gStack, gOutput, gFive, gZero, gFrame⟩ :=
    read_add_count_execution program (entry + 19) f 0 5 0
      (5 + 6 * nodes + children + guards + roots) channels fPC fRunning (by omega) (by omega)
      (by rw [fHeap, eHeap, dHeap, cHeap, bHeap, aHeap]; have := shape.bound; omega)
      (by rw [fHeap, eHeap, dHeap, cHeap, bHeap, aHeap]; exact shape.channelsCell)
      (by omega) (by omega) fFive (by decide) (by decide) channelAt
  have finishAt : RawTransferLoops.CodeAt program (entry + 22)
      #[.constant 3 (word width (2 ^ width - 1)), .constant 7 (word width 0)] := by
    intro index
    fin_cases index
    · simpa [setupCode, Nat.add_assoc] using present ⟨22, by simp [setupCode, saveHeapCountCode]⟩
    · simpa [setupCode, Nat.add_assoc] using present ⟨23, by simp [setupCode, saveHeapCountCode]⟩
  obtain ⟨final, finishTrace, finalPC, finalRunning, finalHeap, finalStack, finalOutput,
      finalMask, finalZero, finalFrame⟩ :=
    finish_setup_execution program (entry + 22) g gPC gRunning (by omega) finishAt
  have aLive : a.liveWords = state.liveWords := by simp only [State.liveWords, aHeap, aStack, aOutput]
  have bLive : b.liveWords = state.liveWords := by simp only [State.liveWords, bHeap, bStack, bOutput]; exact aLive
  have cLive : c.liveWords = state.liveWords := by simp only [State.liveWords, cHeap, cStack, cOutput]; exact bLive
  have dLive : d.liveWords = state.liveWords := by simp only [State.liveWords, dHeap, dStack, dOutput]; exact cLive
  have eLive : e.liveWords = state.liveWords := by simp only [State.liveWords, eHeap, eStack, eOutput]; exact dLive
  have fLive : f.liveWords = state.liveWords := by simp only [State.liveWords, fHeap, fStack, fOutput]; exact eLive
  have gLive : g.liveWords = state.liveWords := by simp only [State.liveWords, gHeap, gStack, gOutput]; exact fLive
  have joined := rootTrace.append (nodeTrace.append (childTrace.append (guardTrace.append
    (literalTrace.append (endTrace.append (channelTrace.append finishTrace))))))
  refine ⟨final, ?_, ?_, finalRunning,
    finalHeap.trans (gHeap.trans (fHeap.trans (eHeap.trans (dHeap.trans (cHeap.trans (bHeap.trans aHeap)))))),
    finalStack.trans (gStack.trans (fStack.trans (eStack.trans (dStack.trans (cStack.trans (bStack.trans aStack)))))),
    finalOutput.trans (gOutput.trans (fOutput.trans (eOutput.trans (dOutput.trans (cOutput.trans (bOutput.trans aOutput)))))),
    ?_, ?_, ?_, finalMask, (finalFrame 5 (by decide) (by decide)).trans gFive, finalZero⟩
  · simpa only [aLive, bLive, cLive, dLive, eLive, fLive, gLive, Nat.max_self] using joined
  · simpa only [Nat.add_assoc] using finalPC
  · exact (finalFrame 1 (by decide) (by decide)).trans
      ((gFrame 1 (by decide) (by decide) (by decide)).trans fOne)
  · exact (finalFrame 2 (by decide) (by decide)).trans
      ((gFrame 2 (by decide) (by decide) (by decide)).trans
        ((fFrame 2 (by decide) (by decide)).trans eCount))
  · exact (finalFrame 4 (by decide) (by decide)).trans
      ((gFrame 4 (by decide) (by decide) (by decide)).trans
        ((fFrame 4 (by decide) (by decide)).trans
          ((eFrame 4 (by decide) (by decide)).trans
            ((dFrame 4 (by decide) (by decide) (by decide)).trans
              ((cFrame 4 (by decide) (by decide) (by decide)).trans
                ((bFrame 4 (by decide) (by decide) (by decide)).trans aSelected))))))

/-- The first projected packet is formed by source-header setup, actual root
classification, and physical copying of the header and row prefix. -/
theorem first_packet_execution (program : Program width 8) (entry prepareEntry headerEntry : Nat)
    (state : State width 8) (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List (Word width)) (healthy : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (setupRoom : entry + 24 < 2 ^ width) (filterRoom : entry + 24 + 11 < 2 ^ width)
    (prepareRoom : prepareEntry + 7 < 2 ^ width)
    (saveRoom : prepareEntry + 7 + 6 < 2 ^ width)
    (headerRoom : headerEntry + 2 < 2 ^ width)
    (capacity : rootStart rows + roots.length + channels + rows.length < 2 ^ width)
    (heapFits : state.heap.size ≤ 2 ^ width)
    (prefixStored : PrefixStored state.heap channels rows roots.length)
    (rootStored : Stored state.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots)
    (setupAt : RawTransferLoops.CodeAt program entry (setupCode width true))
    (filterAt : CodeAt program (entry + 24) prepareEntry healthy)
    (prepareAt : RawTransferLoops.CodeAt program prepareEntry (prepareCode width true))
    (saveAt : RawTransferLoops.CodeAt program (prepareEntry + 7)
      (RawTransferLoops.reverseSaveCode width (prepareEntry + 7) headerEntry))
    (headerAt : RawTransferLoops.CodeAt program headerEntry (prependHeaderCode width)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 10 * roots.length +
        6 * (prefixWords width channels rows roots.length).length + 29 ∧
      peak ≤ state.liveWords + (prefixWords width channels rows roots.length).length +
        (selected state.heap (rootStart rows + roots.length + channels) healthy roots).length ∧
      final.heap = state.heap.setIfInBounds 4
        (word width (selected state.heap (rootStart rows + roots.length + channels) healthy roots).length) ∧
      final.stack = prefixWords width channels rows
        (selected state.heap (rootStart rows + roots.length + channels) healthy roots).length ++
        selected state.heap (rootStart rows + roots.length + channels) healthy roots ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (headerEntry + 2) ∧
      final.halted = false ∧ final.reg 2 = word width roots.length ∧
      final.reg 3 = word width (2 ^ width - 1) ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) := by
  have headerBound : 4 < (prefixWords width channels rows roots.length).length := by
    rw [prefixWords_length]
    omega
  have countCell : state.heap[4]? = some (word width roots.length) := by
    simpa [prefixWords] using prefixStored.cell ⟨4, headerBound⟩
  obtain ⟨ready, setupTrace, readyPC, readyRunning, readyHeap, readyStack, readyOutput,
      readyCursor, readyCount, readySelected, readyMask, readyValue, readyZero⟩ :=
    setup_execution program entry true state channels rows.length
      (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length
      roots.length position running setupRoom (by simpa only [rootStart] using capacity)
      (shape_of_prefix state.heap channels roots.length rows prefixStored)
      (by intro _; exact countCell) (by intro impossible; cases impossible) setupAt
  have readyStored : Stored ready.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots := by
    rw [readyHeap]
    exact rootStored
  obtain ⟨filtered, filterTicks, filterPeak, filterTrace, filterTime, filterSpace,
      filteredPC, filteredRunning, filteredHeap, filteredStack, filteredOutput,
      filteredCursor, filteredZero, filteredSelected, filteredFrame⟩ :=
    execution program (entry + 24) prepareEntry (rootStart rows)
      (rootStart rows + roots.length + channels) healthy roots ready readyPC readyRunning
      filterRoom (by rw [readyHeap]; exact heapFits) readyStored (by omega)
      (by simpa only [rootStart] using readyCursor) readyCount readySelected readyMask
      (by simpa only [rootStart] using readyValue) readyZero filterAt
  have filteredPrefix : PrefixStored filtered.heap channels rows roots.length := by
    rw [filteredHeap, readyHeap]
    exact prefixStored
  have selectedEq : selected ready.heap (rootStart rows + roots.length + channels) healthy roots =
      selected state.heap (rootStart rows + roots.length + channels) healthy roots := by
    rw [readyHeap]
  have filteredMask : filtered.reg 3 = word width (2 ^ width - 1) :=
    (filteredFrame 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans readyMask
  obtain ⟨final, copyPeak, copyTrace, copySpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalCount, finalMask, finalSelected, finalSix, finalSeven⟩ :=
    prepare_copy_execution program prepareEntry (prepareEntry + 7) headerEntry true filtered
      channels roots.length
      (selected state.heap (rootStart rows + roots.length + channels) healthy roots).length rows
      filteredPrefix filteredPC filteredRunning prepareRoom saveRoom headerRoom rfl
      (by rw [prefixWords_length]; change rootStart rows < 2 ^ width; omega)
      (by simpa only [rootStart, prefixWords_length] using filteredCursor) filteredMask
      (by simpa only [selectedEq] using filteredSelected) prepareAt saveAt headerAt
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have filteredLive : filtered.liveWords = state.liveWords +
      (selected state.heap (rootStart rows + roots.length + channels) healthy roots).length := by
    simp only [State.liveWords, filteredHeap, readyHeap, filteredStack, selectedEq,
      readyStack, filteredOutput, readyOutput, List.length_append]
    omega
  have prefixSame : (prefixWords width channels rows
      (selected state.heap (rootStart rows + roots.length + channels) healthy roots).length).length =
      (prefixWords width channels rows roots.length).length := by
    rw [prefixWords_length, prefixWords_length]
  let ticks := 24 + (filterTicks + 6 *
    (prefixWords width channels rows
      (selected state.heap (rootStart rows + roots.length + channels) healthy roots).length).length + 4)
  let peak := max state.liveWords (max filterPeak copyPeak)
  have joined := setupTrace.append (filterTrace.append copyTrace)
  refine ⟨final, ticks, peak, ?_, ?_, ?_, ?_, ?_, ?_, finalPC, finalRunning,
    ?_, ?_, finalSix, finalSeven⟩
  · simpa only [ticks, peak, Nat.add_assoc] using joined
  · dsimp only [ticks]
    rw [prefixSame]
    omega
  · rw [readyLive, selectedEq] at filterSpace
    rw [filteredLive, prefixSame] at copySpace
    exact Nat.max_le.mpr ⟨by omega, Nat.max_le.mpr ⟨by omega, by omega⟩⟩
  · rw [finalHeap, filteredHeap, readyHeap]
  · rw [finalStack, filteredStack, selectedEq, readyStack, List.append_assoc]
  · exact finalOutput.trans (filteredOutput.trans readyOutput)
  · simpa using finalCount
  · exact finalMask.trans filteredMask


/-- After the first packet has been saved, the second setup uses the retained
original occurrence count. The full source-heap size is loaded and retained
before the second prefix copy, then consumed by the fetched release loop. -/
theorem second_packet_release_execution (program : Program width 8)
    (entry saveCountEntry prepareEntry headerEntry releasePrepareEntry done : Nat)
    (state : State width 8) (channels oldCount : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (setupRoom : entry + 24 < 2 ^ width) (filterRoom : entry + 24 + 11 < 2 ^ width)
    (countRoom : saveCountEntry + 3 < 2 ^ width)
    (prepareRoom : prepareEntry + 7 < 2 ^ width)
    (saveRoom : prepareEntry + 7 + 6 < 2 ^ width)
    (headerRoom : headerEntry + 2 < 2 ^ width)
    (releaseRoom : releasePrepareEntry + 1 + 4 < 2 ^ width)
    (countNext : saveCountEntry + 3 = prepareEntry)
    (releaseNext : headerEntry + 2 = releasePrepareEntry)
    (heapFits : state.heap.size < 2 ^ width)
    (geometry : state.heap.size = rootStart rows + roots.length + channels + rows.length)
    (prefixStored : PrefixStored state.heap channels rows oldCount)
    (rootStored : Stored state.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots)
    (originalCount : state.reg 2 = word width roots.length)
    (setupAt : RawTransferLoops.CodeAt program entry (setupCode width false))
    (filterAt : CodeAt program (entry + 24) saveCountEntry false)
    (countAt : RawTransferLoops.CodeAt program saveCountEntry (saveHeapCountCode width))
    (prepareAt : RawTransferLoops.CodeAt program prepareEntry (prepareCode width false))
    (saveAt : RawTransferLoops.CodeAt program (prepareEntry + 7)
      (RawTransferLoops.reverseSaveCode width (prepareEntry + 7) headerEntry))
    (headerAt : RawTransferLoops.CodeAt program headerEntry (prependHeaderCode width))
    (copyAt : program[releasePrepareEntry]? = some (.copy 0 2))
    (releaseAt : RawTransferLoops.CodeAt program (releasePrepareEntry + 1)
      (RawTransferLoops.countedReleaseCode width (releasePrepareEntry + 1) done)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 10 * roots.length + 6 * (prefixWords width channels rows oldCount).length +
        4 * state.heap.size + 34 ∧
      peak ≤ state.liveWords + (prefixWords width channels rows oldCount).length +
        (selected state.heap (rootStart rows + roots.length + channels) false roots).length ∧
      final.heap = #[] ∧
      final.stack = prefixWords width channels rows
        (selected state.heap (rootStart rows + roots.length + channels) false roots).length ++
        selected state.heap (rootStart rows + roots.length + channels) false roots ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 := by
  have capacity : rootStart rows + roots.length + channels + rows.length < 2 ^ width := by
    rw [← geometry]
    exact heapFits
  obtain ⟨ready, setupTrace, readyPC, readyRunning, readyHeap, readyStack, readyOutput,
      readyCursor, readyCount, readySelected, readyMask, readyValue, readyZero⟩ :=
    setup_execution program entry false state channels rows.length
      (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length
      roots.length position running setupRoom (by simpa only [rootStart] using capacity)
      (shape_of_prefix state.heap channels oldCount rows prefixStored)
      (by intro impossible; cases impossible) (by intro _; exact originalCount) setupAt
  obtain ⟨filtered, filterTicks, filterPeak, filterTrace, filterTime, filterSpace,
      filteredPC, filteredRunning, filteredHeap, filteredStack, filteredOutput,
      filteredCursor, filteredZero, filteredSelected, filteredFrame⟩ :=
    execution program (entry + 24) saveCountEntry (rootStart rows)
      (rootStart rows + roots.length + channels) false roots ready readyPC readyRunning
      filterRoom (by rw [readyHeap]; exact le_of_lt heapFits)
      (by rw [readyHeap]; exact rootStored) (by omega)
      (by simpa only [rootStart] using readyCursor) readyCount readySelected readyMask
      (by simpa only [rootStart] using readyValue) readyZero filterAt
  have shape := shape_of_prefix state.heap channels oldCount rows prefixStored
  have filteredValue : filtered.reg 5 = word width (rootStart rows + roots.length + channels) :=
    (filteredFrame 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (by simpa only [rootStart] using readyValue)
  have selectedEq : selected ready.heap (rootStart rows + roots.length + channels) false roots =
      selected state.heap (rootStart rows + roots.length + channels) false roots := by
    rw [readyHeap]
  obtain ⟨counted, countTrace, countedPC, countedRunning, countedHeap, countedStack, countedOutput,
      countedCount, countedFrame⟩ :=
    save_heap_count_execution program saveCountEntry filtered
      (rootStart rows + roots.length + channels) rows.length filteredPC filteredRunning countRoom
      (by rw [filteredHeap, readyHeap]; have := shape.bound; omega)
      (by rw [filteredHeap, readyHeap]; exact shape.nodesCell)
      (by rw [filteredHeap, readyHeap]; exact geometry)
      (by rw [filteredHeap, readyHeap]; exact heapFits) filteredValue countAt
  have countedPrefix : PrefixStored counted.heap channels rows oldCount := by
    rw [countedHeap, filteredHeap, readyHeap]
    exact prefixStored
  have filteredMask : filtered.reg 3 = word width (2 ^ width - 1) :=
    (filteredFrame 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans readyMask
  obtain ⟨copied, copyPeak, copyTrace, copySpace, copiedHeap, copiedStack, copiedOutput,
      copiedPC, copiedRunning, copiedCount, copiedMask, copiedSelected, copiedSix, copiedSeven⟩ :=
    prepare_copy_execution program prepareEntry (prepareEntry + 7) headerEntry false counted
      channels oldCount
      (selected state.heap (rootStart rows + roots.length + channels) false roots).length rows
      countedPrefix (by simpa only [countNext] using countedPC) countedRunning
      prepareRoom saveRoom headerRoom rfl
      (by rw [prefixWords_length]; change rootStart rows < 2 ^ width; omega)
      (by rw [countedFrame 1 (by decide) (by decide)];
          simpa only [rootStart, prefixWords_length] using filteredCursor)
      ((countedFrame 3 (by decide) (by decide)).trans filteredMask)
      ((countedFrame 4 (by decide) (by decide)).trans
        (by simpa only [selectedEq] using filteredSelected)) prepareAt saveAt headerAt
  have copiedSize : copied.heap.size = state.heap.size := by
    simp only [copiedHeap, Array.size_setIfInBounds, countedHeap, filteredHeap, readyHeap]
  have actualCount : copied.reg 2 = word width copied.heap.size := by
    simp only [Bool.false_eq_true, ite_false] at copiedCount
    rw [copiedCount, countedCount, copiedSize, filteredHeap, readyHeap]
  obtain ⟨final, releasePeak, releaseTrace, releaseSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalZero⟩ :=
    release_saved_heap_execution program releasePrepareEntry (releasePrepareEntry + 1) done copied
      (by simpa only [releaseNext] using copiedPC) copiedRunning (by omega) releaseRoom rfl
      (by rw [copiedSize]; exact heapFits) actualCount copiedSeven copiedSix copyAt releaseAt
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have filteredLive : filtered.liveWords = state.liveWords +
      (selected state.heap (rootStart rows + roots.length + channels) false roots).length := by
    simp only [State.liveWords, filteredHeap, readyHeap, filteredStack, selectedEq,
      readyStack, filteredOutput, readyOutput, List.length_append]
    omega
  have countedLive : counted.liveWords = filtered.liveWords := by
    simp only [State.liveWords, countedHeap, countedStack, countedOutput]
  have copiedLive : copied.liveWords = counted.liveWords +
      (prefixWords width channels rows
        (selected state.heap (rootStart rows + roots.length + channels) false roots).length).length := by
    simp only [State.liveWords, copiedHeap, Array.size_setIfInBounds, copiedStack,
      copiedOutput, List.length_append]
    omega
  have prefixSame : (prefixWords width channels rows
      (selected state.heap (rootStart rows + roots.length + channels) false roots).length).length =
      (prefixWords width channels rows oldCount).length := by
    rw [prefixWords_length, prefixWords_length]
  have joined := setupTrace.append (filterTrace.append (countTrace.append (copyTrace.append releaseTrace)))
  refine ⟨final, _, _, joined, ?_, ?_, finalHeap, ?_, ?_, finalPC, finalRunning, finalZero⟩
  · simp only [copiedSize, prefixSame]
    omega
  · rw [readyLive, selectedEq] at filterSpace
    rw [countedLive, filteredLive, prefixSame] at copySpace
    rw [copiedLive, countedLive, filteredLive, prefixSame] at releaseSpace
    exact Nat.max_le.mpr ⟨by omega, Nat.max_le.mpr ⟨by omega,
      Nat.max_le.mpr ⟨by omega, Nat.max_le.mpr ⟨by omega, by omega⟩⟩⟩⟩
  · rw [finalStack, copiedStack, countedStack, filteredStack, selectedEq,
      readyStack, List.append_assoc]
  · exact finalOutput.trans (copiedOutput.trans (countedOutput.trans
      (filteredOutput.trans readyOutput)))

/-- Two passes retain the actual evaluated source until both occurrence-filtered
packets are saved. The final heap release is charged and leaves the positive
packet first, followed by the negative packet and the original caller stack. -/
theorem two_packets_execution (program : Program width 8)
    (firstEntry firstPrepare firstHeader secondEntry countEntry secondPrepare secondHeader
      releasePrepare done : Nat)
    (state : State width 8) (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List (Word width))
    (position : state.pc = word width firstEntry) (running : state.halted = false)
    (firstSetupRoom : firstEntry + 24 < 2 ^ width)
    (firstFilterRoom : firstEntry + 24 + 11 < 2 ^ width)
    (firstPrepareRoom : firstPrepare + 7 < 2 ^ width)
    (firstSaveRoom : firstPrepare + 7 + 6 < 2 ^ width)
    (firstHeaderRoom : firstHeader + 2 < 2 ^ width)
    (secondSetupRoom : secondEntry + 24 < 2 ^ width)
    (secondFilterRoom : secondEntry + 24 + 11 < 2 ^ width)
    (countRoom : countEntry + 3 < 2 ^ width)
    (secondPrepareRoom : secondPrepare + 7 < 2 ^ width)
    (secondSaveRoom : secondPrepare + 7 + 6 < 2 ^ width)
    (secondHeaderRoom : secondHeader + 2 < 2 ^ width)
    (releaseRoom : releasePrepare + 1 + 4 < 2 ^ width)
    (firstNext : firstHeader + 2 = secondEntry)
    (countNext : countEntry + 3 = secondPrepare)
    (releaseNext : secondHeader + 2 = releasePrepare)
    (heapFits : state.heap.size < 2 ^ width)
    (geometry : state.heap.size = rootStart rows + roots.length + channels + rows.length)
    (prefixStored : PrefixStored state.heap channels rows roots.length)
    (rootStored : Stored state.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots)
    (firstSetupAt : RawTransferLoops.CodeAt program firstEntry (setupCode width true))
    (firstFilterAt : CodeAt program (firstEntry + 24) firstPrepare true)
    (firstPrepareAt : RawTransferLoops.CodeAt program firstPrepare (prepareCode width true))
    (firstSaveAt : RawTransferLoops.CodeAt program (firstPrepare + 7)
      (RawTransferLoops.reverseSaveCode width (firstPrepare + 7) firstHeader))
    (firstHeaderAt : RawTransferLoops.CodeAt program firstHeader (prependHeaderCode width))
    (secondSetupAt : RawTransferLoops.CodeAt program secondEntry (setupCode width false))
    (secondFilterAt : CodeAt program (secondEntry + 24) countEntry false)
    (countAt : RawTransferLoops.CodeAt program countEntry (saveHeapCountCode width))
    (secondPrepareAt : RawTransferLoops.CodeAt program secondPrepare (prepareCode width false))
    (secondSaveAt : RawTransferLoops.CodeAt program (secondPrepare + 7)
      (RawTransferLoops.reverseSaveCode width (secondPrepare + 7) secondHeader))
    (secondHeaderAt : RawTransferLoops.CodeAt program secondHeader (prependHeaderCode width))
    (copyAt : program[releasePrepare]? = some (.copy 0 2))
    (releaseAt : RawTransferLoops.CodeAt program (releasePrepare + 1)
      (RawTransferLoops.countedReleaseCode width (releasePrepare + 1) done)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 20 * roots.length + 12 * (prefixWords width channels rows roots.length).length +
        4 * state.heap.size + 63 ∧
      peak ≤ state.liveWords + 2 * (prefixWords width channels rows roots.length).length + roots.length ∧
      final.heap = #[] ∧
      final.stack = prefixWords width channels rows
        (selected state.heap (rootStart rows + roots.length + channels) false roots).length ++
        selected state.heap (rootStart rows + roots.length + channels) false roots ++
        prefixWords width channels rows
          (selected state.heap (rootStart rows + roots.length + channels) true roots).length ++
        selected state.heap (rootStart rows + roots.length + channels) true roots ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 := by
  obtain ⟨middle, firstTicks, firstPeak, firstTrace, firstTime, firstSpace,
      middleHeap, middleStack, middleOutput, middlePC, middleRunning, middleCount,
      middleMask, middleSix, middleSeven⟩ :=
    first_packet_execution program firstEntry firstPrepare firstHeader state channels rows roots true
      position running firstSetupRoom firstFilterRoom firstPrepareRoom firstSaveRoom firstHeaderRoom
      (by rw [← geometry]; exact heapFits) (le_of_lt heapFits) prefixStored rootStored
      firstSetupAt firstFilterAt firstPrepareAt firstSaveAt firstHeaderAt
  let negative := selected state.heap (rootStart rows + roots.length + channels) true roots
  let positive := selected state.heap (rootStart rows + roots.length + channels) false roots
  have middleSize : middle.heap.size = state.heap.size := by
    simp only [middleHeap, Array.size_setIfInBounds]
  have middlePrefix : PrefixStored middle.heap channels rows negative.length := by
    rw [middleHeap]
    exact prefix_store_count state.heap channels roots.length negative.length rows prefixStored
  have middleRoots : Stored middle.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots := by
    rw [middleHeap]
    exact stored_count_header_frame state.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots rootStored
      (by unfold rootStart; omega) (by unfold rootStart; omega) (word width negative.length)
  obtain ⟨final, secondTicks, secondPeak, secondTrace, secondTime, secondSpace,
      finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalZero⟩ :=
    second_packet_release_execution program secondEntry countEntry secondPrepare secondHeader
      releasePrepare done middle channels negative.length rows roots
      (by simpa only [firstNext] using middlePC) middleRunning secondSetupRoom secondFilterRoom
      countRoom secondPrepareRoom secondSaveRoom secondHeaderRoom releaseRoom countNext releaseNext
      (by rw [middleSize]; exact heapFits) (middleSize.trans geometry) middlePrefix middleRoots
      middleCount secondSetupAt secondFilterAt countAt secondPrepareAt secondSaveAt secondHeaderAt
      copyAt releaseAt
  have positiveEq : selected middle.heap (rootStart rows + roots.length + channels) false roots =
      positive := by
    rw [middleHeap]
    exact selected_count_header_frame state.heap (rootStart rows + roots.length + channels)
      false roots (by unfold rootStart; omega) (word width negative.length)
  have prefixSame : (prefixWords width channels rows negative.length).length =
      (prefixWords width channels rows roots.length).length := by
    rw [prefixWords_length, prefixWords_length]
  have middleLive : middle.liveWords = state.liveWords +
      (prefixWords width channels rows roots.length).length + negative.length := by
    dsimp only [negative]
    simp only [State.liveWords, middleHeap, Array.size_setIfInBounds, middleStack, middleOutput,
      List.length_append, prefixWords_length]
    omega
  have partition : negative.length + positive.length = roots.length :=
    selected_partition_length state.heap (rootStart rows + roots.length + channels) roots
  refine ⟨final, firstTicks + secondTicks, max firstPeak secondPeak,
    firstTrace.append secondTrace, ?_, ?_, finalHeap, ?_, finalOutput.trans middleOutput,
    finalPC, finalRunning, finalZero⟩
  · rw [prefixSame, middleSize] at secondTime
    omega
  · rw [middleLive, prefixSame, positiveEq] at secondSpace
    exact Nat.max_le.mpr ⟨by dsimp only [negative, positive] at partition ⊢; omega,
      by omega⟩
  · rw [finalStack, positiveEq, middleStack]
    simp only [positive, List.append_assoc]

/-- A saved header/row prefix followed by the original-ID root column is the
literal cold-input word stream, including duplicate occurrences. -/
theorem prefix_root_packet_words (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) :
    prefixWords width channels rows roots.length ++ roots.map (word width) =
      (ForestIndexedOperands.inputPacket channels 0 rows roots).map (word width) := by
  rw [projected_input_packet]
  simp only [List.map_append, prefixWords, List.append_assoc]
  rfl

/-- The node-table base is the actual channel-heap end after the evaluator has
loaded both the original source packet and the original channel assignment. -/
theorem evaluation_value_start (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (assignment : Fin channels → Bool) :
    (ForestInputPrefixStored.channelHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment).size =
      sourceValueStart channels rows roots := by
  simp only [ForestInputPrefixStored.channelHeap_size, ForestIndexedOperands.cacheHeap_size,
    UniformDAGRun.packetHeaderHeap_size, ForestIndexedOperands.serializedRows_length,
    sourceValueStart, rootStart] <;> omega

/-- Every classification bit is read from the actual appended evaluation
array at the unchanged original node identifier. -/
theorem evaluation_node_cell (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (assignment : Fin channels → Bool) (nodes : Fin rows.length → Bool)
    (id : Fin rows.length) :
    ((ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)[sourceValueStart channels rows roots + id.val]?) = some (boolWord width (nodes id)) := by
  let channel := ForestInputPrefixStored.channelHeap
    (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment
  have baseEq : channel.size = sourceValueStart channels rows roots :=
    evaluation_value_start channels rows roots assignment
  change ((ForestInputStored.withValues channel nodes)[sourceValueStart channels rows roots + id.val]?) = _
  rw [← baseEq, Array.getElem?_eq_getElem (by
    simp only [ForestInputStored.withValues_size]
    exact Nat.add_lt_add_left id.isLt channel.size)]
  exact congrArg some (ForestInputStored.value_cell channel nodes id)

/-- Physical classification coincides with the occurrence-preserving filter of
actual evaluated nodes. Invalid IDs never enter this theorem's source domain. -/
theorem selected_evaluation_roots (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (assignment : Fin channels → Bool) (nodes : Fin rows.length → Bool)
    (healthy : Bool) (ids : ∀ root ∈ roots, root < rows.length)
    (heapFits : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes).size < 2 ^ width) :
    selected
      (ForestInputPrefixStored.evaluationHeap
        (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
      (sourceValueStart channels rows roots) healthy (roots.map (word width)) =
      (roots.filter (fun root => (if valid : root < rows.length then nodes ⟨root, valid⟩ else false)
        == healthy)).map (word width) := by
  let values : Nat → Bool := fun root => if valid : root < rows.length then nodes ⟨root, valid⟩ else false
  have fullSize := source_heap_end (width := width) channels rows roots assignment nodes
  have baseBound : 5 ≤ sourceValueStart channels rows roots := by
    unfold sourceValueStart rootStart
    omega
  apply selected_source_values _ _ healthy roots values
  · omega
  · intro root member
    have valid := ids root member
    omega
  · intro root member
    have valid := ids root member
    simpa only [values, dite_eq_left valid] using
      evaluation_node_cell channels rows roots assignment nodes ⟨root, valid⟩

/-- A successful positive branch discards the saved negative packet by reading
its physical count metadata, then executing this fixed stack-pop loop. -/
def discardCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done), .pop 5, .add 0 0 7, .branchZero 6 (word width entry)]

@[simp] theorem discardCode_size (width entry done : Nat) :
    (discardCode width entry done).size = 4 := rfl

private theorem discard_round (program : Program width 8) (entry done : Nat)
    (state : State width 8) (value : Word width) (rest : List (Word width)) (count : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 4 < 2 ^ width) (stack : state.stack = value :: rest)
    (countFits : count + 1 < 2 ^ width) (countReg : state.reg 0 = word width (count + 1))
    (maskReg : state.reg 7 = word width (2 ^ width - 1)) (zeroReg : state.reg 6 = word width 0)
    (present : RawTransferLoops.CodeAt program entry (discardCode width entry done)) :
    ∃ next, Execution program state next 4 state.liveWords ∧
      next.pc = word width entry ∧ next.halted = false ∧ next.heap = state.heap ∧
      next.stack = rest ∧ next.output = state.output ∧ next.reg 0 = word width count ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 5 → next.reg register = state.reg register) := by
  let one := state.advance
  let two := { (one.advance.put 5 value) with stack := rest }
  let three := two.advance.put 0 (word width count)
  let next := { three.advance with pc := word width entry }
  have onePC : one.pc = word width (entry + 1) := advance_position state position (by omega)
  have twoPC : two.pc = word width (entry + 2) := advance_position one onePC (by omega)
  have threePC : three.pc = word width (entry + 3) := advance_position two twoPC (by omega)
  have countValue : (state.reg 0).val = count + 1 := by
    rw [countReg]
    exact Nat.mod_eq_of_lt countFits
  have maskValue : (state.reg 7).val = 2 ^ width - 1 := by
    rw [maskReg]
    exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
  have first : programStep program state = some one := by
    rw [fetched program state entry _ position (by omega)
      (by simpa [discardCode] using present ⟨0, by simp [discardCode]⟩)]
    simp [step, running, countValue, one]
  have second : programStep program one = some two := by
    rw [fetched program one (entry + 1) _ onePC (by omega)
      (by simpa [discardCode] using present ⟨1, by simp [discardCode]⟩)]
    simp [step, one, two, State.advance, stack, running]
  have third : programStep program two = some three := by
    rw [fetched program two (entry + 2) _ twoPC (by omega)
      (by simpa [discardCode] using present ⟨2, by simp [discardCode]⟩)]
    have zeroValue : (two.reg 0).val = count + 1 := by
      simpa [two, one, State.advance, State.put] using countValue
    have sevenValue : (two.reg 7).val = 2 ^ width - 1 := by
      simpa [two, one, State.advance, State.put] using maskValue
    simp only [step, show two.halted = false from running, Bool.false_eq_true, ite_false,
      zeroValue, sevenValue]
    rw [RawTransferLoops.decrement_word]
  have fourth : programStep program three = some next := by
    rw [fetched program three (entry + 3) _ threePC (by omega)
      (by simpa [discardCode] using present ⟨3, by simp [discardCode]⟩)]
    simp [step, three, two, one, State.put, State.advance, running, zeroReg, word, next]
  have oneLive : one.liveWords = state.liveWords := rfl
  have twoLive : two.liveWords ≤ state.liveWords := by
    simp only [two, one, State.liveWords, State.put, State.advance, stack, List.length_cons]
    omega
  have threeLive : three.liveWords = two.liveWords := rfl
  have nextLive : next.liveWords = two.liveWords := rfl
  have trace := Execution.cons first (Execution.cons second
    (Execution.cons third (Execution.cons fourth (Execution.refl next))))
  have peakEq : max state.liveWords (max one.liveWords
      (max two.liveWords (max three.liveWords next.liveWords))) = state.liveWords := by omega
  refine ⟨next, by simpa only [Nat.zero_add, peakEq] using trace,
    rfl, running, rfl, rfl, rfl, ?_, ?_⟩
  · simp [next, three, State.put, State.advance]
  · intro register zero five
    simp [next, three, two, one, State.put, State.advance, zero, five]

/-- The number of popped words equals the length of the actual saved packet;
its cells may contain arbitrary source words and duplicate root identifiers. -/
theorem discard_execution (program : Program width 8) (entry done : Nat)
    (packet rest : List (Word width)) :
    ∀ state : State width 8, state.pc = word width entry → state.halted = false →
      entry + 4 < 2 ^ width → state.stack = packet ++ rest → packet.length < 2 ^ width →
      state.reg 0 = word width packet.length → state.reg 7 = word width (2 ^ width - 1) →
      state.reg 6 = word width 0 →
      RawTransferLoops.CodeAt program entry (discardCode width entry done) →
    ∃ final peak, Execution program state final (4 * packet.length + 1) peak ∧
      peak ≤ state.liveWords ∧ final.heap = state.heap ∧ final.stack = rest ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 5 → final.reg register = state.reg register) := by
  induction packet with
  | nil =>
    intro state position running room stack countFits countReg maskReg zeroReg present
    let final := { state.advance with pc := word width done }
    have transition : programStep program state = some final := by
      rw [fetched program state entry _ position (by omega)
        (by simpa [discardCode] using present ⟨0, by simp [discardCode]⟩)]
      simp [step, running, countReg, word, final]
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, state.liveWords, ?_, le_rfl, rfl, ?_, rfl, rfl, running, countReg, ?_⟩
    · simpa only [live, Nat.max_self, List.length_nil, Nat.mul_zero, Nat.zero_add] using
        Execution.cons transition (Execution.refl final)
    · change state.stack = rest
      simpa only [List.nil_append] using stack
    · intro register zero five; rfl
  | cons value packet ih =>
    intro state position running room stack countFits countReg maskReg zeroReg present
    obtain ⟨middle, first, middlePC, middleRunning, middleHeap, middleStack, middleOutput,
        middleCount, middleFrame⟩ :=
      discard_round program entry done state value (packet ++ rest) packet.length position running room
        (by simpa only [List.cons_append] using stack)
        (by simpa only [List.length_cons] using countFits)
        (by simpa only [List.length_cons] using countReg) maskReg zeroReg present
    obtain ⟨final, lastPeak, last, lastSpace, finalHeap, finalStack, finalOutput,
        finalPC, finalRunning, finalCount, finalFrame⟩ :=
      ih middle middlePC middleRunning room middleStack (by
        have bound : packet.length + 1 < 2 ^ width := by
          simpa only [List.length_cons] using countFits
        exact lt_trans (Nat.lt_succ_self packet.length) bound) middleCount
        ((middleFrame 7 (by decide) (by decide)).trans maskReg)
        ((middleFrame 6 (by decide) (by decide)).trans zeroReg) present
    have middleLive : middle.liveWords ≤ state.liveWords := Execution.final_storage_le first
    refine ⟨final, max state.liveWords lastPeak, ?_,
      Nat.max_le.mpr ⟨le_rfl, lastSpace.trans middleLive⟩, finalHeap.trans middleHeap,
      finalStack, finalOutput.trans middleOutput, finalPC, finalRunning, finalCount, ?_⟩
    · have scalar : 4 + (4 * packet.length + 1) = 4 * (value :: packet).length + 1 := by
        simp only [List.length_cons]
        omega
      simpa only [scalar] using first.append last
    · intro register zero five
      exact (finalFrame register zero five).trans (middleFrame register zero five)

/-- The first selected count is saved above its packet by reading the header
that the first physical copy just wrote. This metadata drives cleanup of the
unused negative packet after a positive witness is emitted. -/
def saveNegativeCountCode (width : Nat) : Program width 8 :=
  #[.constant 0 (word width 4), .load 4 0, .push 4]

@[simp] theorem saveNegativeCountCode_size (width : Nat) :
    (saveNegativeCountCode width).size = 3 := rfl

theorem save_negative_count_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (count : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (headerFits : 4 < 2 ^ width)
    (valid : 4 < state.heap.size) (cell : state.heap[4]? = some (word width count))
    (present : RawTransferLoops.CodeAt program entry (saveNegativeCountCode width)) :
    ∃ final, Execution program state final 3 (state.liveWords + 1) ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = word width count :: state.stack ∧
      final.output = state.output ∧ final.reg 4 = word width count ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 4 → final.reg register = state.reg register) := by
  let middle := (state.advance.put 0 (word width 4)).advance.put 4 (word width count)
  obtain ⟨readTrace, middlePC, middleRunning, middleHeap, middleStack, middleOutput,
      middleCount, middleFrame⟩ :=
    read_source_count_execution program entry state 4 4 (word width count) position running
      (by omega) headerFits valid cell
      (by simpa [saveNegativeCountCode] using present ⟨0, by simp [saveNegativeCountCode]⟩)
      (by simpa [saveNegativeCountCode] using present ⟨1, by simp [saveNegativeCountCode]⟩)
  let final := { middle.advance with stack := word width count :: state.stack }
  have last : programStep program middle = some final := by
    rw [fetched program middle (entry + 2) _ middlePC (by omega)
      (by simpa [saveNegativeCountCode, Nat.add_assoc] using present ⟨2, by simp [saveNegativeCountCode]⟩)]
    simp [step, middle, final, State.advance, State.put, running]
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords + 1 := by
    simp only [final, middle, State.advance, State.put, State.liveWords, List.length_cons]
    omega
  have tail : Execution program middle final 1 (state.liveWords + 1) := by
    have peakEq : max middle.liveWords final.liveWords = state.liveWords + 1 := by omega
    simpa only [peakEq] using Execution.cons last (Execution.refl final)
  refine ⟨final, ?_, ?_, running, rfl, rfl, rfl, ?_, ?_⟩
  · have peakEq : max state.liveWords (state.liveWords + 1) = state.liveWords + 1 := by omega
    simpa only [peakEq] using readTrace.append tail
  · change middle.advance.pc = word width (entry + 3)
    simpa only [Nat.add_assoc] using advance_position middle middlePC (by omega)
  · change middle.reg 4 = word width count
    exact middleCount
  · intro register zero four
    exact middleFrame register zero four


/-- Two passes retain the actual evaluated source until both occurrence-filtered
packets are saved. The final heap release is charged and leaves the positive
packet first, followed by the actual saved negative count, its packet, and the original caller stack. -/
theorem two_packets_with_count_execution (program : Program width 8)
    (firstEntry firstPrepare firstHeader metadataEntry secondEntry countEntry secondPrepare secondHeader
      releasePrepare done : Nat)
    (state : State width 8) (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List (Word width))
    (position : state.pc = word width firstEntry) (running : state.halted = false)
    (firstSetupRoom : firstEntry + 24 < 2 ^ width)
    (firstFilterRoom : firstEntry + 24 + 11 < 2 ^ width)
    (firstPrepareRoom : firstPrepare + 7 < 2 ^ width)
    (firstSaveRoom : firstPrepare + 7 + 6 < 2 ^ width)
    (firstHeaderRoom : firstHeader + 2 < 2 ^ width)
    (secondSetupRoom : secondEntry + 24 < 2 ^ width)
    (secondFilterRoom : secondEntry + 24 + 11 < 2 ^ width)
    (countRoom : countEntry + 3 < 2 ^ width)
    (secondPrepareRoom : secondPrepare + 7 < 2 ^ width)
    (secondSaveRoom : secondPrepare + 7 + 6 < 2 ^ width)
    (secondHeaderRoom : secondHeader + 2 < 2 ^ width)
    (releaseRoom : releasePrepare + 1 + 4 < 2 ^ width)
    (firstNext : firstHeader + 2 = metadataEntry)
    (metadataNext : metadataEntry + 3 = secondEntry)
    (metadataRoom : metadataEntry + 3 < 2 ^ width)
    (countNext : countEntry + 3 = secondPrepare)
    (releaseNext : secondHeader + 2 = releasePrepare)
    (heapFits : state.heap.size < 2 ^ width)
    (geometry : state.heap.size = rootStart rows + roots.length + channels + rows.length)
    (prefixStored : PrefixStored state.heap channels rows roots.length)
    (rootStored : Stored state.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots)
    (firstSetupAt : RawTransferLoops.CodeAt program firstEntry (setupCode width true))
    (firstFilterAt : CodeAt program (firstEntry + 24) firstPrepare true)
    (firstPrepareAt : RawTransferLoops.CodeAt program firstPrepare (prepareCode width true))
    (firstSaveAt : RawTransferLoops.CodeAt program (firstPrepare + 7)
      (RawTransferLoops.reverseSaveCode width (firstPrepare + 7) firstHeader))
    (firstHeaderAt : RawTransferLoops.CodeAt program firstHeader (prependHeaderCode width))
    (metadataAt : RawTransferLoops.CodeAt program metadataEntry (saveNegativeCountCode width))
    (secondSetupAt : RawTransferLoops.CodeAt program secondEntry (setupCode width false))
    (secondFilterAt : CodeAt program (secondEntry + 24) countEntry false)
    (countAt : RawTransferLoops.CodeAt program countEntry (saveHeapCountCode width))
    (secondPrepareAt : RawTransferLoops.CodeAt program secondPrepare (prepareCode width false))
    (secondSaveAt : RawTransferLoops.CodeAt program (secondPrepare + 7)
      (RawTransferLoops.reverseSaveCode width (secondPrepare + 7) secondHeader))
    (secondHeaderAt : RawTransferLoops.CodeAt program secondHeader (prependHeaderCode width))
    (copyAt : program[releasePrepare]? = some (.copy 0 2))
    (releaseAt : RawTransferLoops.CodeAt program (releasePrepare + 1)
      (RawTransferLoops.countedReleaseCode width (releasePrepare + 1) done)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 20 * roots.length + 12 * (prefixWords width channels rows roots.length).length +
        4 * state.heap.size + 66 ∧
      peak ≤ state.liveWords + 2 * (prefixWords width channels rows roots.length).length + roots.length + 1 ∧
      final.heap = #[] ∧
      final.stack = prefixWords width channels rows
        (selected state.heap (rootStart rows + roots.length + channels) false roots).length ++
        selected state.heap (rootStart rows + roots.length + channels) false roots ++
        [word width (selected state.heap (rootStart rows + roots.length + channels) true roots).length] ++
        prefixWords width channels rows
          (selected state.heap (rootStart rows + roots.length + channels) true roots).length ++
        selected state.heap (rootStart rows + roots.length + channels) true roots ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 := by
  obtain ⟨middle, firstTicks, firstPeak, firstTrace, firstTime, firstSpace,
      middleHeap, middleStack, middleOutput, middlePC, middleRunning, middleCount,
      middleMask, middleSix, middleSeven⟩ :=
    first_packet_execution program firstEntry firstPrepare firstHeader state channels rows roots true
      position running firstSetupRoom firstFilterRoom firstPrepareRoom firstSaveRoom firstHeaderRoom
      (by rw [← geometry]; exact heapFits) (le_of_lt heapFits) prefixStored rootStored
      firstSetupAt firstFilterAt firstPrepareAt firstSaveAt firstHeaderAt
  let negative := selected state.heap (rootStart rows + roots.length + channels) true roots
  let positive := selected state.heap (rootStart rows + roots.length + channels) false roots
  have middleSize : middle.heap.size = state.heap.size := by
    simp only [middleHeap, Array.size_setIfInBounds]
  have middlePrefix : PrefixStored middle.heap channels rows negative.length := by
    rw [middleHeap]
    exact prefix_store_count state.heap channels roots.length negative.length rows prefixStored
  have middleRoots : Stored middle.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots := by
    rw [middleHeap]
    exact stored_count_header_frame state.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots rootStored
      (by unfold rootStart; omega) (by unfold rootStart; omega) (word width negative.length)
  have sourceBound : 4 < state.heap.size := by
    have prefixBound := prefixStored.bound
    rw [prefixWords_length] at prefixBound
    omega
  have countCell : middle.heap[4]? = some (word width negative.length) := by
    simp only [middleHeap, Array.getElem?_setIfInBounds, ite_true, ite_eq_left sourceBound]
    rfl
  have selectedFits : negative.length < 2 ^ width := by
    have selectedLe := selected_length state.heap (rootStart rows + roots.length + channels) true roots
    have rootsBound := rootStored.rootBound
    dsimp only [negative]
    omega
  obtain ⟨marked, metadataTrace, markedPC, markedRunning, markedHeap, markedStack,
      markedOutput, markedCount, markedFrame⟩ :=
    save_negative_count_execution program metadataEntry middle negative.length
      (by simpa only [firstNext] using middlePC) middleRunning metadataRoom (by omega)
      (by rw [middleHeap, Array.size_setIfInBounds]; exact sourceBound) countCell metadataAt
  have markedSize : marked.heap.size = state.heap.size := by rw [markedHeap, middleSize]
  have markedPrefix : PrefixStored marked.heap channels rows negative.length := by
    rw [markedHeap]
    exact middlePrefix
  have markedRoots : Stored marked.heap (rootStart rows)
      (rootStart rows + roots.length + channels) roots := by
    rw [markedHeap]
    exact middleRoots
  have retainedCount : marked.reg 2 = word width roots.length :=
    (markedFrame 2 (by decide) (by decide)).trans middleCount
  obtain ⟨final, secondTicks, secondPeak, secondTrace, secondTime, secondSpace,
      finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalZero⟩ :=
    second_packet_release_execution program secondEntry countEntry secondPrepare secondHeader
      releasePrepare done marked channels negative.length rows roots
      (by simpa only [metadataNext] using markedPC) markedRunning secondSetupRoom secondFilterRoom
      countRoom secondPrepareRoom secondSaveRoom secondHeaderRoom releaseRoom countNext releaseNext
      (by rw [markedSize]; exact heapFits) (markedSize.trans geometry) markedPrefix markedRoots
      retainedCount secondSetupAt secondFilterAt countAt secondPrepareAt secondSaveAt secondHeaderAt
      copyAt releaseAt
  have positiveEq : selected marked.heap (rootStart rows + roots.length + channels) false roots =
      positive := by
    rw [markedHeap, middleHeap]
    exact selected_count_header_frame state.heap (rootStart rows + roots.length + channels)
      false roots (by unfold rootStart; omega) (word width negative.length)
  have prefixSame : (prefixWords width channels rows negative.length).length =
      (prefixWords width channels rows roots.length).length := by
    rw [prefixWords_length, prefixWords_length]
  have middleLive : middle.liveWords = state.liveWords +
      (prefixWords width channels rows roots.length).length + negative.length := by
    dsimp only [negative]
    simp only [State.liveWords, middleHeap, Array.size_setIfInBounds, middleStack, middleOutput,
      List.length_append, prefixWords_length]
    omega
  have markedLive : marked.liveWords = middle.liveWords + 1 := by
    simp only [State.liveWords, markedHeap, markedStack, markedOutput, List.length_cons]
    omega
  have partition : negative.length + positive.length = roots.length :=
    selected_partition_length state.heap (rootStart rows + roots.length + channels) roots
  refine ⟨final, firstTicks + (3 + secondTicks), max firstPeak (max (middle.liveWords + 1) secondPeak),
    firstTrace.append (metadataTrace.append secondTrace), ?_, ?_, finalHeap, ?_,
    finalOutput.trans (markedOutput.trans middleOutput),
    finalPC, finalRunning, finalZero⟩
  · rw [prefixSame, markedSize] at secondTime
    omega
  · rw [markedLive, middleLive, prefixSame, positiveEq] at secondSpace
    dsimp only [negative, positive] at partition middleLive secondSpace
    exact Nat.max_le.mpr ⟨by omega, Nat.max_le.mpr ⟨by rw [middleLive]; omega, by omega⟩⟩
  · rw [finalStack, positiveEq, markedStack, middleStack]
    simp only [positive, negative, List.append_assoc, List.cons_append, List.nil_append]


/-- Classification preserves the original occurrence order, and the saved
word packets are precisely the input packets for the two projected root lists. -/
theorem classified_packet_words (channels : Nat) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (assignment : Fin channels → Bool) (nodes : Fin rows.length → Bool)
    (healthy : Bool) (ids : ∀ root ∈ roots, root < rows.length)
    (heapFits : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes).size < 2 ^ width) :
    let heap := ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes
    let selectedIds := roots.filter (fun root =>
      (if valid : root < rows.length then nodes ⟨root, valid⟩ else false) == healthy)
    prefixWords width channels rows
      (selected heap (rootStart rows + (roots.map (word width)).length + channels)
        healthy (roots.map (word width))).length ++
      selected heap (rootStart rows + (roots.map (word width)).length + channels)
        healthy (roots.map (word width)) =
      (ForestIndexedOperands.inputPacket channels 0 rows selectedIds).map (word width) := by
  dsimp only
  have baseEq : rootStart rows + (roots.map (word width)).length + channels =
      sourceValueStart channels rows roots := by
    simp only [List.length_map, sourceValueStart]
  rw [baseEq, selected_evaluation_roots channels rows roots assignment nodes healthy ids heapFits,
    List.length_map]
  exact prefix_root_packet_words channels rows _

/-- The selected count is an actual representable word read from the stored
header. Its numeric value therefore equals the original occurrence count. -/
theorem selected_header_count_value (heap : Array (Word width)) (rootBase valueBase : Nat)
    (healthy : Bool) (roots : List (Word width)) (stored : Stored heap rootBase valueBase roots)
    (heapFits : heap.size < 2 ^ width) :
    (word width (selected heap valueBase healthy roots).length).val =
      (selected heap valueBase healthy roots).length := by
  have selectedLe := selected_length heap valueBase healthy roots
  have rootBound := stored.rootBound
  exact Nat.mod_eq_of_lt (by omega)


/-- The fixed packet loader executes in the actual eight-register caller.
Only its four low registers are used; the saved metadata registers are framed. -/
theorem cold_packet_eight_execution (program : Program width 8)
    (entry channels nodes children guards roots : Nat)
    (payload suffix : List (Word width)) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (empty : state.heap = #[]) (zero : state.reg 3 = word width 0)
    (stack : state.stack = ForestInputMetadata.headerWords width channels nodes children guards roots ++
      payload ++ suffix)
    (lengthEq : payload.length = 6 * nodes + children + guards + roots)
    (fits : entry + 33 < 2 ^ width) (room : 5 + payload.length ≤ 2 ^ width)
    (present : ForestZeroCallerWiden.WidenedBlockAt program entry
      (ForestInputMetadata.fullCode width entry)) :
    ∃ final, Execution program state final (27 + 7 * payload.length) state.liveWords ∧
      final.heap = (ForestInputMetadata.headerWords width channels nodes children guards roots).toArray ++
        payload.toArray ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 33) ∧ final.halted = false ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let low := (ForestCounter.counterState (#[] : Array (Word width)) entry
    (state.reg 0) (state.reg 1) (state.reg 2)).frame
      (ForestInputMetadata.headerWords width channels nodes children guards roots ++ payload ++ suffix)
      state.output
  have registers : (RegisterWiden.widenState low state.reg).reg = state.reg := by
    funext register
    fin_cases register
    all_goals simp only [RegisterWiden.widenState, low, State.frame,
      ForestCounter.counterState, Fin.reduceEq, Nat.reduceLT, ite_true, ite_false]
    all_goals first | rfl | exact zero.symm
  have initial : RegisterWiden.widenState low state.reg = state := by
    change State.mk _ #[] _ state.output (word width entry) false =
      State.mk state.reg state.heap state.stack state.output state.pc state.halted
    rw [State.mk.injEq]
    exact ⟨registers, empty.symm, stack.symm, rfl, position.symm, running.symm⟩
  obtain ⟨last, trace, heap, rest, output, pc, active⟩ :=
    ForestInputMetadata.cold_packet_execution (ForestZeroCallerWiden.lowerProgram program)
      entry channels nodes children guards roots payload suffix state.output
      (state.reg 0) (state.reg 1) (state.reg 2) lengthEq fits room
      (ForestZeroCallerWiden.lower_block program entry _ present)
  have lifted := ForestZeroCallerWiden.execution program low last _ _ trace active state.reg
  have live : 10 + payload.length + suffix.length + state.output.length + 4 = state.liveWords := by
    rw [State.liveWords, empty, stack]
    simp only [Array.size_empty, List.length_append, ForestInputMetadata.headerWords,
      List.length_cons, List.length_nil]
    omega
  refine ⟨RegisterWiden.widenState last state.reg, ?_, heap, rest, output, pc, active, ?_⟩
  · simpa only [initial, live] using lifted
  · intro register large
    exact RegisterWiden.widenState_high last state.reg register large

/-- A fetched constant clears the sole fixed-zero low register required by
cold loading; projection's decrement mask is never treated as an implicit zero. -/
theorem clear_loader_zero_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (present : program[entry]? = some (.constant 3 (word width 0))) :
    let final := state.advance.put 3 (word width 0)
    Execution program state final 1 state.liveWords ∧
      final.pc = word width (entry + 1) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 3 = word width 0 ∧
      (∀ register : Fin 8, register ≠ 3 → final.reg register = state.reg register) := by
  let final := state.advance.put 3 (word width 0)
  have transition : programStep program state = some final := by
    rw [fetched program state entry _ position (by omega) present]
    simp only [step, running, Bool.false_eq_true, ite_false]
    rfl
  have pcVal : state.pc.val = entry := by
    rw [position]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, running, rfl, rfl, rfl, ?_, ?_⟩
  · have live : final.liveWords = state.liveWords := rfl
    simpa only [live, Nat.max_self, Nat.zero_add] using
      Execution.cons transition (Execution.refl final)
  · change word width (state.pc.val + 1) = word width (entry + 1)
    rw [pcVal]
  · simp only [final, State.put, ite_true]
  · intro register other
    simp only [final, State.put, State.advance, ite_eq_right other]

/-- The positive packet consumes exactly its saved source words, retains the
negative-count trailer, and reconstructs its own cache in the released heap. -/
theorem projected_packet_load_execution (program : Program width 8)
    (entry channels nodes children guards roots : Nat)
    (payload suffix : List (Word width)) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (empty : state.heap = #[])
    (stack : state.stack = ForestInputMetadata.headerWords width channels nodes children guards roots ++
      payload ++ suffix)
    (lengthEq : payload.length = 6 * nodes + children + guards + roots)
    (fits : entry + 34 < 2 ^ width) (room : 5 + payload.length ≤ 2 ^ width)
    (clearAt : program[entry]? = some (.constant 3 (word width 0)))
    (loaderAt : ForestZeroCallerWiden.WidenedBlockAt program (entry + 1)
      (ForestInputMetadata.fullCode width (entry + 1))) :
    ∃ final, Execution program state final (28 + 7 * payload.length) state.liveWords ∧
      final.heap = (ForestInputMetadata.headerWords width channels nodes children guards roots).toArray ++
        payload.toArray ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 34) ∧ final.halted = false ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let ready := state.advance.put 3 (word width 0)
  obtain ⟨first, readyPC, readyRunning, readyHeap, readyStack, readyOutput, readyZero, readyFrame⟩ :=
    clear_loader_zero_execution program entry state position running (by omega) clearAt
  obtain ⟨final, last, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    cold_packet_eight_execution program (entry + 1) channels nodes children guards roots payload suffix ready
      readyPC readyRunning (readyHeap.trans empty) readyZero (readyStack.trans stack) lengthEq
      (by omega) room loaderAt
  have readyLive : ready.liveWords = state.liveWords := rfl
  have scalar : 1 + (27 + 7 * payload.length) = 28 + 7 * payload.length := by omega
  refine ⟨final, ?_, finalHeap, finalStack, finalOutput.trans readyOutput, ?_, finalRunning, ?_⟩
  · simpa only [readyLive, Nat.max_self, scalar] using first.append last
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · intro register large
    have other : register ≠ 3 := by
      intro same
      have equal := congrArg Fin.val same
      change register.val = 3 at equal
      omega
    exact (finalFrame register large).trans (readyFrame register other)

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RegisterWiden
variable {width : Nat}

/-- The resident weighted block is appended to the actual caller array. The
continuation uses the same array and may access all eight registers. -/
def weightedResident (prior : Program width 8)
    (items : List (Instruction width 4)) (continuation : Program width 8) : Program width 8 :=
  (items.map widenInstruction).toArrayAux prior ++ continuation

theorem lower_weighted_array (prior : Program width 8)
    (items : List (Instruction width 4)) :
    ForestZeroCallerWiden.lowerProgram ((items.map widenInstruction).toArrayAux prior) =
      ForestWeightedIndexed.materialize (ForestZeroCallerWiden.lowerProgram prior) items := by
  apply Array.toList_inj.mp
  simp only [ForestZeroCallerWiden.lowerProgram, ForestWeightedIndexed.materialize,
    Array.toList_map, Array.toArrayAux_eq, List.map_append, List.map_map, Function.comp_def]
  have identity : items.map (fun instruction =>
      ForestZeroCallerWiden.lowerInstruction (widenInstruction instruction)) = items := by
    simp only [ForestZeroCallerWiden.lower_widen, List.map_id_fun']
    rfl
  rw [identity]

theorem weighted_resident_fetch (prior : Program width 8)
    (items : List (Instruction width 4)) (continuation : Program width 8)
    (slot : Nat)
    (bound : slot < (ForestWeightedIndexed.materialize
      (ForestZeroCallerWiden.lowerProgram prior) items).size) :
    (ForestZeroCallerWiden.lowerProgram (weightedResident prior items continuation))[slot]? =
      (ForestWeightedIndexed.materialize (ForestZeroCallerWiden.lowerProgram prior) items)[slot]? := by
  have low := lower_weighted_array prior items
  have valid : slot < ((items.map widenInstruction).toArrayAux prior).size := by
    have sizes : ((items.map widenInstruction).toArrayAux prior).size =
        (ForestWeightedIndexed.materialize (ForestZeroCallerWiden.lowerProgram prior) items).size := by
      calc
        _ = (ForestZeroCallerWiden.lowerProgram
          ((items.map widenInstruction).toArrayAux prior)).size := by
            simp only [ForestZeroCallerWiden.lowerProgram, Array.size_map]
        _ = _ := congrArg Array.size low
    exact lt_of_lt_of_eq bound sizes.symm
  change (((items.map widenInstruction).toArrayAux prior ++ continuation).map
    ForestZeroCallerWiden.lowerInstruction)[slot]? = _
  rw [Array.getElem?_map, Array.getElem?_append_left valid]
  rw [← low]
  simp only [ForestZeroCallerWiden.lowerProgram, Array.getElem?_map]

/-- An actual successful low-register trace continues inside the resident
caller without copying the source heap or changing its continuation code. -/
theorem weighted_resident_execution (prior : Program width 8)
    (items : List (Instruction width 4)) (continuation : Program width 8)
    (before after : Controller.Cost.State width 4) (ticks peak : Nat)
    (trace : Execution (ForestWeightedIndexed.materialize
      (ForestZeroCallerWiden.lowerProgram prior) items) before after ticks peak)
    (running : after.halted = false) (saved : Fin 8 → Word width) :
    Execution (weightedResident prior items continuation)
      (widenState before saved) (widenState after saved) ticks (peak + 4) := by
  have sameProgram := ForestWeightedIndexed.execution_same_fetched_prefix
    (ForestWeightedIndexed.materialize (ForestZeroCallerWiden.lowerProgram prior) items)
    (ForestZeroCallerWiden.lowerProgram (weightedResident prior items continuation))
    before after ticks peak trace (weighted_resident_fetch prior items continuation)
  exact ForestZeroCallerWiden.execution _ before after ticks peak sameProgram running saved

theorem weighted_resident_formation (prior : Program width 8)
    (items : List (Instruction width 4)) (continuation : Program width 8) :
    CompilerArrayTrace.Trace (items.map widenInstruction) prior
      ((items.map widenInstruction).toArrayAux prior) items.length ∧
    (weightedResident prior items continuation).toList =
      prior.toList ++ items.map widenInstruction ++ continuation.toList ∧
    (weightedResident prior items continuation).size = prior.size + items.length + continuation.size := by
  have formation := CompilerArrayTrace.exists_trace (items.map widenInstruction) prior
  have count := CompilerArrayTrace.final_size formation
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.length_map] using formation
  · simp only [weightedResident, Array.toList_append, Array.toArrayAux_eq]
  · simpa only [weightedResident, Array.size_append, List.length_map] using
      congrArg (fun size => size + continuation.size) count

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWeightedPhysicalOptimal Controller.Cost.ForestWitnessMarshal
open Controller.Cost.ForestInputStored Controller.Cost.ForestCounter
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorMaterialize
open Controller.Cost.ForestCursorAllRoots
open Controller.Cost.RegisterWiden
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem selected_resident_eight_execution (prior : Program width 8)
    (continuation : Program width 8) (saved : Fin 8 → Word width)
    (heap : Array (Word width)) (graph : DAG n)
    (forest : graph.FormulaForest) (guarded : graph.Guarded)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : Nat) (target : Channel n)
    (candidate : Candidate W)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (countAddress : Nat) (address loaded temporary : Word width)
    (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : prior.size + (4 * (buildRoots graph).count + 2 * (n + 3)) + 94 < 2 ^ width) :
    let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2
    let items := selectedItems width heap graph rows roots computed candidate
      countFits positionFits prior.size countAddress
    computed.arithmetic ≤ n + 8 * (graph.roots.length + graph.childIncidences) +
      4 * graph.guardIncidences ∧
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution (weightedResident prior items continuation)
          (widenState ((counterState (cacheHeap width heap rows roots) prior.size
            address loaded temporary).frame stack output) saved) final ticks peak ∧
        ticks ≤ 18 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          12 * n + 24 ∧
        peak ≤ 9 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
        final.pc = word width (prior.size + 4 * (buildRoots graph).count + 2 * (n + 3) + 94) ∧
        final.halted = false ∧
        final.heap.size = (setupHeap width (cacheHeap width heap rows roots) graph).size ∧
        (∀ register : Fin 8, 4 ≤ register.val → final.reg register = saved register) := by
  obtain ⟨arithmetic, position, rootEq, blocked, lowFinal, ticks, peak,
      admissible, feasible, score, optimal, trace, time, space, stackEq, outputEq,
      pcEq, running, heapSize⟩ :=
    ForestWeightedIndexed.selected_prefixed_emission_endpoint
      (ForestZeroCallerWiden.lowerProgram prior) heap graph forest guarded rows roots matched
      rootMatches weights nonnegative b target candidate chosen countFits positionFits countAddress
      address loaded temporary stack output countValid countWord heapFits
      (by simpa only [ForestZeroCallerWiden.lowerProgram, Array.size_map] using programFits)
  let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2
  let items := selectedItems width heap graph rows roots computed candidate
    countFits positionFits prior.size countAddress
  have lowTrace : Execution (ForestWeightedIndexed.materialize
      (ForestZeroCallerWiden.lowerProgram prior) items)
      ((counterState (cacheHeap width heap rows roots) prior.size address loaded temporary).frame stack output)
      lowFinal ticks peak := by
    simpa only [ForestZeroCallerWiden.lowerProgram, Array.size_map, items, computed] using trace
  have lifted := weighted_resident_execution prior items continuation _ lowFinal ticks peak lowTrace running saved
  refine ⟨arithmetic, position, rootEq, blocked, widenState lowFinal saved, ticks, peak + 4,
    admissible, feasible, score, optimal, lifted, time, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stackEq
  · exact outputEq
  · simpa only [ForestZeroCallerWiden.lowerProgram, Array.size_map, widenState_pc] using pcEq
  · exact running
  · exact heapSize
  · intro register large
    exact widenState_high lowFinal saved register large

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

/-- The allocated endpoint is formed from the source headers and actual
computed descriptor count. Negative-packet length comes from its saved header. -/
def positiveCleanupCode (width entry allocated sourcePrefix : Nat) : Program width 8 :=
  #[.constant 0 (word width allocated)] ++
    countedReleaseCode width (entry + 1) (entry + 5) ++
    #[.pop 0, .constant 1 (word width sourcePrefix), .add 0 0 1] ++
    discardCode width (entry + 8) (entry + 12) ++ #[.halt]

@[simp] theorem positiveCleanupCode_size (width entry allocated sourcePrefix : Nat) :
    (positiveCleanupCode width entry allocated sourcePrefix).size = 13 := by
  simp [positiveCleanupCode]

theorem negative_discard_prepare (program : Program width 8) (entry basePrefix count : Nat)
    (state : State width 8) (packet rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (packetRoom : basePrefix + count < 2 ^ width)
    (stack : state.stack = word width count :: (packet ++ rest))
    (firstAt : program[entry]? = some (.pop 0))
    (secondAt : program[entry + 1]? = some (.constant 1 (word width basePrefix)))
    (thirdAt : program[entry + 2]? = some (.add 0 0 1)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.pc = word width (entry + 3) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = packet ++ rest ∧ final.output = state.output ∧
      final.reg 0 = word width (basePrefix + count) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  let first := { state.advance.put 0 (word width count) with stack := packet ++ rest }
  let second := first.advance.put 1 (word width basePrefix)
  let final := second.advance.put 0 (word width (basePrefix + count))
  have entryValue : state.pc.val = entry := by
    rw [position]
    exact Nat.mod_eq_of_lt (by omega)
  have firstPC : first.pc = word width (entry + 1) := by
    change word width (state.pc.val + 1) = _
    rw [entryValue]
  have firstValue : first.pc.val = entry + 1 := by
    rw [firstPC]
    exact Nat.mod_eq_of_lt (by omega)
  have secondPC : second.pc = word width (entry + 2) := by
    change word width (first.pc.val + 1) = _
    rw [firstValue]
  have secondValue : second.pc.val = entry + 2 := by
    rw [secondPC]
    exact Nat.mod_eq_of_lt (by omega)
  have t0 : programStep program state = some first := by
    rw [fetched program state entry _ position (by omega) firstAt]
    simp only [step, running, Bool.false_eq_true, ite_false, stack]
    rfl
  have t1 : programStep program first = some second := by
    rw [fetched program first (entry + 1) _ firstPC (by omega) secondAt]
    simp only [step, show first.halted = false from running, Bool.false_eq_true, ite_false]
    rfl
  have t2 : programStep program second = some final := by
    rw [fetched program second (entry + 2) _ secondPC (by omega) thirdAt]
    have zeroValue : (second.reg 0).val = count := by
      simp only [second, first, State.put, State.advance, Fin.reduceEq, ite_true, ite_false]
      exact Nat.mod_eq_of_lt (by omega)
    have oneValue : (second.reg 1).val = basePrefix := by
      change (word width basePrefix).val = basePrefix
      exact Nat.mod_eq_of_lt (by omega)
    simp only [step, show second.halted = false from running, Bool.false_eq_true, ite_false,
      zeroValue, oneValue, Nat.add_comm count basePrefix]
    rfl
  have firstLive : first.liveWords + 1 = state.liveWords := by
    simp only [first, State.liveWords, State.put, State.advance, stack, List.length_cons]
    omega
  have secondLive : second.liveWords = first.liveWords := rfl
  have finalLive : final.liveWords = first.liveWords := rfl
  refine ⟨final, ?_, ?_, running, rfl, rfl, rfl, ?_, ?_⟩
  · simpa only [secondLive, finalLive, Nat.max_self, Nat.zero_add,
      Nat.max_eq_left (by omega : first.liveWords ≤ state.liveWords)] using
      Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl final)))
  · change word width (second.pc.val + 1) = _
    rw [secondValue]
  · simp only [final, State.put, ite_true]
  · intro register zero one
    simp only [final, second, first, State.put, State.advance, ite_eq_right zero, ite_eq_right one]

/-- The positive witness is retained while actual heap releases and stack pops
remove the two now-unused storage regions. No output reads are used. -/
theorem positive_cleanup_execution (program : Program width 8)
    (entry allocated basePrefix count : Nat) (state : State width 8)
    (packet rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 13 < 2 ^ width)
    (allocatedRoom : allocated < 2 ^ width) (packetRoom : basePrefix + count < 2 ^ width)
    (heapSize : state.heap.size = allocated) (packetSize : packet.length = basePrefix + count)
    (stack : state.stack = word width count :: (packet ++ rest))
    (mask : state.reg 7 = word width (2 ^ width - 1)) (zero : state.reg 6 = word width 0)
    (present : RawTransferLoops.CodeAt program entry (positiveCleanupCode width entry allocated basePrefix)) :
    ∃ final peak, Execution program state final (4 * allocated + 4 * (basePrefix + count) + 7) peak ∧
      peak ≤ state.liveWords ∧ final.heap = #[] ∧ final.stack = rest ∧
      final.output = state.output ∧ final.pc = word width (entry + 13) ∧ final.halted = true ∧
      final.reg 4 = state.reg 4 := by
  let first := state.advance.put 0 (word width allocated)
  have firstAt : program[entry]? = some (.constant 0 (word width allocated)) := by
    simpa [positiveCleanupCode] using present ⟨0, by simp⟩
  have t0 : programStep program state = some first := by
    rw [fetched program state entry _ position (by omega) firstAt]
    simp only [step, running, Bool.false_eq_true, ite_false]
    rfl
  have firstTrace : Execution program state first 1 state.liveWords := by
    have live : first.liveWords = state.liveWords := rfl
    simpa only [live, Nat.max_self, Nat.zero_add] using
      Execution.cons t0 (Execution.refl first)
  have firstPC : first.pc = word width (entry + 1) := by
    change word width (state.pc.val + 1) = _
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have releaseAt : RawTransferLoops.CodeAt program (entry + 1) (countedReleaseCode width (entry + 1) (entry + 5)) := by
    intro slot
    have found := present ⟨1 + slot.val, by have := slot.isLt; simp at this; simp; omega⟩
    fin_cases slot <;>
      simpa [positiveCleanupCode, countedReleaseCode, discardCode, Nat.add_assoc] using found
  obtain ⟨released, releasePeak, releaseTrace, releaseSpace, releasedHeap, releasedStack,
      releasedOutput, releasedPC, releasedRunning, releasedZero, releasedFrame⟩ :=
    counted_release_execution program (entry + 1) (entry + 5) allocated first firstPC running
      (by omega) heapSize allocatedRoom (by simp [first, State.put]) mask zero releaseAt
  have prepAt0 : program[entry + 5]? = some (.pop 0) := by
    simpa [positiveCleanupCode, countedReleaseCode, discardCode] using present ⟨5, by simp⟩
  have prepAt1 : program[entry + 6]? = some (.constant 1 (word width basePrefix)) := by
    simpa [positiveCleanupCode, countedReleaseCode, discardCode] using present ⟨6, by simp⟩
  have prepAt2 : program[entry + 7]? = some (.add 0 0 1) := by
    simpa [positiveCleanupCode, countedReleaseCode, discardCode] using present ⟨7, by simp⟩
  obtain ⟨ready, prepTrace, readyPC, readyRunning, readyHeap, readyStack, readyOutput,
      readyCount, readyFrame⟩ := negative_discard_prepare program (entry + 5) basePrefix count released
        packet rest releasedPC releasedRunning (by omega) packetRoom
        (releasedStack.trans stack) prepAt0 (by simpa only [Nat.add_assoc] using prepAt1)
        (by simpa only [Nat.add_assoc] using prepAt2)
  have discardAt : RawTransferLoops.CodeAt program (entry + 8) (discardCode width (entry + 8) (entry + 12)) := by
    intro slot
    have found := present ⟨8 + slot.val, by have := slot.isLt; simp at this; simp; omega⟩
    fin_cases slot <;>
      simpa [positiveCleanupCode, countedReleaseCode, discardCode, Nat.add_assoc] using found
  have readyMask : ready.reg 7 = word width (2 ^ width - 1) :=
    (readyFrame 7 (by decide) (by decide)).trans
      ((releasedFrame 7 (by decide)).trans mask)
  have readyZero : ready.reg 6 = word width 0 :=
    (readyFrame 6 (by decide) (by decide)).trans
      ((releasedFrame 6 (by decide)).trans zero)
  obtain ⟨discarded, discardPeak, discardTrace, discardSpace, discardedHeap, discardedStack,
      discardedOutput, discardedPC, discardedRunning, discardedCount, discardedFrame⟩ :=
    discard_execution program (entry + 8) (entry + 12) packet rest ready
      (by simpa only [Nat.add_assoc] using readyPC) readyRunning (by omega) readyStack
      (by simpa only [packetSize] using packetRoom)
      (by simpa only [packetSize] using readyCount) readyMask readyZero discardAt
  let final := { discarded.advance with halted := true }
  have haltAt : program[entry + 12]? = some .halt := by
    simpa [positiveCleanupCode, countedReleaseCode, discardCode] using present ⟨12, by simp⟩
  have haltStep : programStep program discarded = some final := by
    rw [fetched program discarded (entry + 12) _ discardedPC (by omega) haltAt]
    simp only [step, discardedRunning, Bool.false_eq_true, ite_false]
    rfl
  have haltTrace : Execution program discarded final 1 discarded.liveWords := by
    have live : final.liveWords = discarded.liveWords := rfl
    simpa only [live, Nat.max_self, Nat.zero_add] using
      Execution.cons haltStep (Execution.refl final)
  have firstLive : first.liveWords = state.liveWords := rfl
  have releasedLive : released.liveWords ≤ state.liveWords :=
    (Execution.final_storage_le releaseTrace).trans (by simpa only [firstLive] using releaseSpace)
  have readyLive : ready.liveWords ≤ released.liveWords := Execution.final_storage_le prepTrace
  have discardedLive : discarded.liveWords ≤ ready.liveWords :=
    (Execution.final_storage_le discardTrace).trans discardSpace
  have joined := ((firstTrace.append releaseTrace).append prepTrace).append
    (discardTrace.append haltTrace)
  have totalTicks : 1 + (4 * allocated + 1) + 3 + (4 * packet.length + 1 + 1) =
      4 * allocated + 4 * (basePrefix + count) + 7 := by
    rw [packetSize]
    omega
  refine ⟨final, max (max (max state.liveWords releasePeak) released.liveWords)
    (max discardPeak discarded.liveWords), ?_, ?_, ?_, discardedStack, ?_, ?_, rfl, ?_⟩
  · simpa only [totalTicks] using joined
  · apply max_le
    · apply max_le
      · apply max_le
        · exact le_rfl
        · simpa only [firstLive] using releaseSpace
      · exact releasedLive
    · apply max_le
      · exact discardSpace.trans (readyLive.trans releasedLive)
      · exact discardedLive.trans (readyLive.trans releasedLive)
  · exact discardedHeap.trans (readyHeap.trans releasedHeap)
  · exact discardedOutput.trans (readyOutput.trans (releasedOutput.trans rfl))
  · change word width (discarded.pc.val + 1) = _
    rw [discardedPC, show (word width (entry + 12)).val = entry + 12 from Nat.mod_eq_of_lt (by omega)]
  · exact (discardedFrame 4 (by decide) (by decide)).trans
      ((readyFrame 4 (by decide) (by decide)).trans
        ((releasedFrame 4 (by decide)).trans rfl))

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorDescriptors
variable {width n : Nat}

def sourcePrefixCells (rows : List Row) : Nat :=
  5 + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length

def sourceAllocatedCells (graph : DAG n) (rows : List Row) (positiveRoots : List Nat) : Nat :=
  sourcePrefixCells rows + positiveRoots.length + 2 * (buildRoots graph).count + (n + 3)

theorem source_allocated_heap_size (graph : DAG n) (rows : List Row) (positiveRoots : List Nat) :
    (setupHeap width (cacheHeap width
      (UniformDAGRun.packetHeaderHeap width n rows positiveRoots) rows positiveRoots) graph).size =
      sourceAllocatedCells graph rows positiveRoots := by
  simp only [setupHeap_size, cacheHeap_size, UniformDAGRun.packetHeaderHeap_size,
    sourceAllocatedCells, sourcePrefixCells]

theorem source_negative_packet_size (rows : List Row) (negativeRoots : List Nat) :
    ((inputPacket n 0 rows negativeRoots).map (word width)).length =
      sourcePrefixCells rows + negativeRoots.length := by
  simp only [List.length_map, inputPacket, List.length_append, globalHeader_length,
    serializedRows_length, sourcePrefixCells]
  omega

theorem weighted_continuation_present (prior : Program width 8)
    (items : List (Instruction width 4)) (continuation : Program width 8) :
    RawTransferLoops.CodeAt (weightedResident prior items continuation)
      (prior.size + items.length) continuation := by
  have sizes := CompilerArrayTrace.final_size
    (CompilerArrayTrace.exists_trace (items.map RegisterWiden.widenInstruction) prior)
  simp only [List.length_map] at sizes
  intro offset
  change (((items.map RegisterWiden.widenInstruction).toArrayAux prior) ++ continuation)[prior.size + items.length + offset.val]? = continuation[offset.val]?
  rw [← sizes, Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

/-- The cleanup count is derived from the actual selected heap endpoint and
original packet fields. The continuation is fetched from its appended array. -/
theorem selected_source_cleanup_execution (prior : Program width 8)
    (items : List (Instruction width 4)) (graph : DAG n) (rows : List Row)
    (positiveRoots negativeRoots : List Nat) (state : State width 8)
    (rest : List (Word width))
    (position : state.pc = word width (prior.size + items.length))
    (running : state.halted = false)
    (room : prior.size + items.length + 13 < 2 ^ width)
    (allocatedRoom : sourceAllocatedCells graph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (heapSize : state.heap.size =
      (setupHeap width (cacheHeap width
        (UniformDAGRun.packetHeaderHeap width n rows positiveRoots) rows positiveRoots) graph).size)
    (stack : state.stack = word width negativeRoots.length ::
      ((inputPacket n 0 rows negativeRoots).map (word width) ++ rest))
    (mask : state.reg 7 = word width (2 ^ width - 1)) (zero : state.reg 6 = word width 0) :
    let continuation := positiveCleanupCode width (prior.size + items.length)
      (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
    ∃ final peak, Execution (weightedResident prior items continuation) state final
      (4 * sourceAllocatedCells graph rows positiveRoots +
        4 * (sourcePrefixCells rows + negativeRoots.length) + 7) peak ∧
      peak ≤ state.liveWords ∧ final.heap = #[] ∧ final.stack = rest ∧
      final.output = state.output ∧
      final.pc = word width (prior.size + items.length + 13) ∧ final.halted = true ∧
      final.reg 4 = state.reg 4 := by
  let continuation := positiveCleanupCode width (prior.size + items.length)
    (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
  exact positive_cleanup_execution (weightedResident prior items continuation)
    (prior.size + items.length) (sourceAllocatedCells graph rows positiveRoots)
    (sourcePrefixCells rows) negativeRoots.length state
    ((inputPacket n 0 rows negativeRoots).map (word width)) rest position running room
    allocatedRoom packetRoom
    (heapSize.trans (source_allocated_heap_size graph rows positiveRoots))
    (source_negative_packet_size rows negativeRoots) stack mask zero
    (weighted_continuation_present prior items continuation)

end Controller.Cost.ForestRootProjection


namespace Controller.Cost.ForestRootProjection
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestWitnessMarshal Controller.Cost.ForestCounter
open Controller.Cost.RegisterWiden
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem selected_original_positive_execution (prior : Program width 8)
    (saved : Fin 8 → Word width) (graph : DAG n)
    (forest : graph.FormulaForest) (guarded : graph.Guarded)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph positiveRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (target : Channel n) (candidate : Candidate W)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (address loaded temporary : Word width) (rest output : List (Word width))
    (sourceRoom : sourceAllocatedCells graph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (programRoom : prior.size + (4 * (buildRoots graph).count + 2 * n + 100) + 13 < 2 ^ width)
    (mask : saved 7 = word width (2 ^ width - 1)) (zero : saved 6 = word width 0)
    (success : saved 4 = word width 1) :
    let header := UniformDAGRun.packetHeaderHeap width n rows positiveRoots
    let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
    let items := selectedItems width header graph rows positiveRoots computed candidate
      countFits positionFits prior.size 0
    let stack := word width negativeRoots.length ::
      ((inputPacket n 0 rows negativeRoots).map (word width) ++ rest)
    let continuation := positiveCleanupCode width (prior.size + items.length)
      (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution (weightedResident prior items continuation)
          (widenState ((counterState (cacheHeap width header rows positiveRoots) prior.size
            address loaded temporary).frame stack output) saved) final ticks peak ∧
        ticks ≤ 18 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          12 * n + 4 * sourceAllocatedCells graph rows positiveRoots +
          4 * (sourcePrefixCells rows + negativeRoots.length) + 31 ∧
        peak ≤ 9 + sourceAllocatedCells graph rows positiveRoots +
          (buildRoots graph).count + sourcePrefixCells rows + negativeRoots.length +
          rest.length + output.length + n + 2 ∧
        final.heap = #[] ∧ final.stack = rest ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
        final.halted = true ∧ final.reg 4 = word width 1 := by
  let header := UniformDAGRun.packetHeaderHeap width n rows positiveRoots
  let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
  let items := selectedItems width header graph rows positiveRoots computed candidate
    countFits positionFits prior.size 0
  let stack := word width negativeRoots.length ::
    ((inputPacket n 0 rows negativeRoots).map (word width) ++ rest)
  let continuation := positiveCleanupCode width (prior.size + items.length)
    (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
  have itemLength : items.length = 4 * (buildRoots graph).count + 2 * n + 100 :=
    selectedItems_length header graph rows positiveRoots matched rootMatches weights b target
      candidate countFits positionFits prior.size 0
  have countValid : 0 < header.size := by
    simp only [header, UniformDAGRun.packetHeaderHeap_size]
    omega
  have countWord : header[0] = word width n := by
    simp [header, UniformDAGRun.packetHeaderHeap, globalHeader]
  have heapRoom : (setupHeap width (cacheHeap width header rows positiveRoots) graph).size ≤ 2 ^ width := by
    rw [source_allocated_heap_size]
    exact sourceRoom.le
  obtain ⟨arithmetic, position, rootEq, blocked, selectedFinal, firstTicks, firstPeak,
      admissible, feasible, score, optimal, firstTrace, firstTime, firstSpace, selectedStack,
      selectedOutput, selectedPC, selectedRunning, selectedHeap, selectedFrame⟩ :=
    selected_resident_eight_execution prior continuation saved header graph forest guarded rows
      positiveRoots matched rootMatches weights nonnegative b target candidate chosen countFits positionFits
      0 address loaded temporary stack output countValid countWord heapRoom (by omega)
  have selectedEntry : selectedFinal.pc = word width (prior.size + items.length) := by
    rw [itemLength]
    have scalar : prior.size + 4 * (buildRoots graph).count + 2 * (n + 3) + 94 =
        prior.size + (4 * (buildRoots graph).count + 2 * n + 100) := by omega
    exact selectedPC.trans (congrArg (word width) scalar)
  obtain ⟨final, lastPeak, lastTrace, lastSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalHalted, finalFrame⟩ := selected_source_cleanup_execution prior items graph rows
        positiveRoots negativeRoots selectedFinal rest selectedEntry selectedRunning
        (by rw [itemLength]; exact programRoom) sourceRoom packetRoom selectedHeap
        selectedStack ((selectedFrame 7 (by decide)).trans mask)
        ((selectedFrame 6 (by decide)).trans zero)
  have finalLive : selectedFinal.liveWords ≤ firstPeak := Execution.final_storage_le firstTrace
  have joined := firstTrace.append lastTrace
  refine ⟨position, rootEq, blocked, final, firstTicks +
    (4 * sourceAllocatedCells graph rows positiveRoots +
      4 * (sourcePrefixCells rows + negativeRoots.length) + 7),
    max firstPeak lastPeak, admissible, feasible, score, optimal, joined, by omega,
    ?_, finalHeap, finalStack, finalOutput.trans selectedOutput, finalHalted,
    finalFrame.trans ((selectedFrame 4 (by decide)).trans success)⟩
  have stackSize : stack.length = sourcePrefixCells rows + negativeRoots.length + rest.length + 1 := by
    simp only [stack, List.length_cons, List.length_append, source_negative_packet_size]
  have sourceSize := source_allocated_heap_size (width := width) graph rows positiveRoots
  have firstBound : firstPeak ≤ 9 + sourceAllocatedCells graph rows positiveRoots +
      (buildRoots graph).count + sourcePrefixCells rows + negativeRoots.length +
      rest.length + output.length + n + 2 := by
    rw [sourceSize] at firstSpace
    rw [stackSize] at firstSpace
    omega
  exact max_le firstBound (lastSpace.trans (finalLive.trans firstBound))

end Controller.Cost.ForestRootProjection


namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The Boolean operand is formed from the actual indexed selected-result
field. The fetched branch tests that stored operand in register four. -/
def mixedSelectorCode (width failure : Nat) (rows : List Row)
    (roots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n) : Program width 8 :=
  #[.constant 4 (boolWord width
      (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected.isSome),
    .branchZero 4 (word width failure)]

@[simp] theorem mixedSelectorCode_size (width failure : Nat) (rows : List Row)
    (roots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n) :
    (mixedSelectorCode width failure rows roots weights b target).size = 2 := rfl

theorem mixed_selector_execution (program : Program width 8) (entry failure : Nat)
    (rows : List Row) (roots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (state : Controller.Cost.State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 2 < 2 ^ width)
    (present : RawTransferLoops.CodeAt program entry
      (mixedSelectorCode width failure rows roots weights b target)) :
    let chosen := (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected.isSome
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.pc = word width (if chosen then entry + 2 else failure) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = boolWord width chosen ∧
      (∀ register : Fin 8, register ≠ 4 → final.reg register = state.reg register) := by
  let chosen := (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected.isSome
  let first := state.advance.put 4 (boolWord width chosen)
  let final := { first.advance with pc := word width (if chosen then entry + 2 else failure) }
  have constAt : program[entry]? = some (.constant 4 (boolWord width chosen)) := by
    simpa [mixedSelectorCode] using present ⟨0, by simp⟩
  have branchAt : program[entry + 1]? = some (.branchZero 4 (word width failure)) := by
    simpa [mixedSelectorCode] using present ⟨1, by simp⟩
  have firstPC : first.pc = word width (entry + 1) := by
    change word width (state.pc.val + 1) = _
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have firstValue : first.pc.val = entry + 1 := by
    rw [firstPC]
    exact Nat.mod_eq_of_lt (by omega)
  have t0 : programStep program state = some first := by
    rw [RawTransferLoops.fetched program state entry _ position (by omega) constAt]
    simp only [step, running, Bool.false_eq_true, ite_false]
    rfl
  have t1 : programStep program first = some final := by
    rw [RawTransferLoops.fetched program first (entry + 1) _ firstPC (by omega) branchAt]
    have selector : first.reg 4 = boolWord width chosen := by simp only [first, State.put, ite_true]
    have firstRunning : first.halted = false := running
    have selectorValue : (first.reg 4).val = if chosen then 1 else 0 := by
      rw [selector]
      cases selected : chosen <;>
        simp only [selected, boolWord, word, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ width),
          Nat.zero_mod, Bool.false_eq_true, ite_false, ite_true]
    cases selected : chosen <;>
      simp only [step, firstRunning, Bool.false_eq_true, ite_false, selectorValue,
        selected, ite_true, Nat.one_ne_zero, final, State.advance, firstValue,
        show entry + 1 + 1 = entry + 2 from by omega]
  have firstLive : first.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, rfl, running, rfl, rfl, rfl, ?_, ?_⟩
  · simpa only [firstLive, finalLive, Nat.max_self, Nat.zero_add] using
      Execution.cons t0 (Execution.cons t1 (Execution.refl final))
  · simp only [final, first, State.advance, State.put, ite_true]
    rfl
  · intro register other
    simp only [final, first, State.advance, State.put, ite_eq_right other]

end Controller.Cost.ForestRootProjection


namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

def negativeHandoffCode (width entry allocated : Nat) : Program width 8 :=
  #[.constant 0 (word width allocated)] ++
    countedReleaseCode width (entry + 1) (entry + 5) ++
    #[.pop 4, .constant 3 (word width 0)]

@[simp] theorem negativeHandoffCode_size (width entry allocated : Nat) :
    (negativeHandoffCode width entry allocated).size = 7 := by
  simp [negativeHandoffCode]

theorem negative_handoff_execution (program : Program width 8)
    (entry allocated : Nat) (state : State width 8) (countWord : Word width)
    (packet rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 7 < 2 ^ width) (allocatedRoom : allocated < 2 ^ width)
    (heapSize : state.heap.size = allocated)
    (stack : state.stack = countWord :: (packet ++ rest))
    (mask : state.reg 7 = word width (2 ^ width - 1)) (zero : state.reg 6 = word width 0)
    (present : RawTransferLoops.CodeAt program entry (negativeHandoffCode width entry allocated)) :
    ∃ final peak, Execution program state final (4 * allocated + 4) peak ∧
      peak ≤ state.liveWords ∧ final.heap = #[] ∧ final.stack = packet ++ rest ∧
      final.output = state.output ∧ final.pc = word width (entry + 7) ∧ final.halted = false ∧
      final.reg 3 = word width 0 ∧ final.reg 4 = countWord ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → register ≠ 4 → final.reg register = state.reg register) := by
  let first := state.advance.put 0 (word width allocated)
  have constAt : program[entry]? = some (.constant 0 (word width allocated)) := by
    simpa [negativeHandoffCode] using present ⟨0, by simp⟩
  have t0 : programStep program state = some first := by
    rw [fetched program state entry _ position (by omega) constAt]
    simp only [step, running, Bool.false_eq_true, ite_false]
    rfl
  have firstLive : first.liveWords = state.liveWords := rfl
  have firstStack : first.stack = state.stack := rfl
  have firstTrace : Execution program state first 1 state.liveWords := by
    simpa only [firstLive, Nat.max_self, Nat.zero_add] using
      Execution.cons t0 (Execution.refl first)
  have firstPC : first.pc = word width (entry + 1) := by
    change word width (state.pc.val + 1) = _
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have releaseAt : RawTransferLoops.CodeAt program (entry + 1) (countedReleaseCode width (entry + 1) (entry + 5)) := by
    intro slot
    have found := present ⟨1 + slot.val, by have := slot.isLt; simp at this; simp; omega⟩
    fin_cases slot <;> simpa [negativeHandoffCode, countedReleaseCode, Nat.add_assoc] using found
  obtain ⟨released, releasePeak, releaseTrace, releaseSpace, releasedHeap, releasedStack,
      releasedOutput, releasedPC, releasedRunning, releasedZero, releasedFrame⟩ :=
    counted_release_execution program (entry + 1) (entry + 5) allocated first firstPC running
      (by omega) heapSize allocatedRoom (by simp [first, State.put]) mask zero releaseAt
  let middle := { released.advance.put 4 countWord with stack := packet ++ rest }
  let final := middle.advance.put 3 (word width 0)
  have popAt : program[entry + 5]? = some (.pop 4) := by
    simpa [negativeHandoffCode, countedReleaseCode] using present ⟨5, by simp⟩
  have clearAt : program[entry + 6]? = some (.constant 3 (word width 0)) := by
    simpa [negativeHandoffCode, countedReleaseCode] using present ⟨6, by simp⟩
  have popStep : programStep program released = some middle := by
    rw [fetched program released (entry + 5) _ releasedPC (by omega) popAt]
    simp only [step, releasedRunning, Bool.false_eq_true, ite_false, releasedStack, firstStack, stack]
    rfl
  have middlePC : middle.pc = word width (entry + 6) := by
    change word width (released.pc.val + 1) = _
    rw [releasedPC, show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (by omega)] <;> rfl
  have clearStep : programStep program middle = some final := by
    rw [fetched program middle (entry + 6) _ middlePC (by omega) clearAt]
    simp only [step, show middle.halted = false from releasedRunning, Bool.false_eq_true, ite_false]
    rfl
  have middleLive : middle.liveWords + 1 = released.liveWords := by
    simp only [middle, State.liveWords, State.put, State.advance, releasedStack, firstStack, stack, List.length_cons]
    omega
  have finalLive : final.liveWords = middle.liveWords := rfl
  have lastTrace : Execution program released final 2 released.liveWords := by
    simpa only [finalLive, Nat.max_self, Nat.zero_add,
      Nat.max_eq_left (by omega : middle.liveWords ≤ released.liveWords)] using
      Execution.cons popStep (Execution.cons clearStep (Execution.refl final))
  have releasedLive : released.liveWords ≤ state.liveWords :=
    (Execution.final_storage_le releaseTrace).trans (by simpa only [firstLive] using releaseSpace)
  have ticksEq : 1 + (4 * allocated + 1) + 2 = 4 * allocated + 4 := by omega
  refine ⟨final, max (max state.liveWords releasePeak) released.liveWords, ?_,
    max_le (max_le le_rfl (by simpa only [firstLive] using releaseSpace)) releasedLive,
    releasedHeap, rfl, releasedOutput, ?_, releasedRunning, ?_, ?_, ?_⟩
  · simpa only [ticksEq] using (firstTrace.append releaseTrace).append lastTrace
  · change word width (middle.pc.val + 1) = _
    rw [middlePC, show (word width (entry + 6)).val = entry + 6 from Nat.mod_eq_of_lt (by omega)] <;> rfl
  · simp only [final, State.put, ite_true]
  · simp only [final, middle, State.put, State.advance, Fin.reduceEq, ite_true, ite_false]
  · intro register other0 other3 other4
    exact (by simp only [final, middle, State.put, State.advance, ite_eq_right other3, ite_eq_right other4] :
      final.reg register = released.reg register).trans
      ((releasedFrame register other0).trans (by simp only [first, State.put, State.advance, ite_eq_right other0]))

/-- Every physical ready state with its cleared low register has the exact
counter entry shape needed by the cold negative source loader. -/
theorem cleared_counter_state (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 3 = word width 0) :
    RegisterWiden.widenState
      ((ForestCounter.counterState state.heap entry (state.reg 0) (state.reg 1) (state.reg 2)).frame
        state.stack state.output) state.reg = state := by
  have registers : (RegisterWiden.widenState
      ((ForestCounter.counterState state.heap entry (state.reg 0) (state.reg 1) (state.reg 2)).frame
        state.stack state.output) state.reg).reg = state.reg := by
    funext register
    fin_cases register
    all_goals simp only [RegisterWiden.widenState, State.frame, ForestCounter.counterState,
      Fin.reduceEq, Nat.reduceLT, ite_true, ite_false]
    all_goals first | rfl | exact zero.symm
  change State.mk _ state.heap state.stack state.output (word width entry) false =
    State.mk state.reg state.heap state.stack state.output state.pc state.halted
  rw [State.mk.injEq]
  exact ⟨registers, rfl, rfl, rfl, position.symm, running.symm⟩

end Controller.Cost.ForestRootProjection


namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestIndexedOperands
variable {width n : Nat}

/-- The failure continuation and the zero-query loader belong to a single
resident array; the loader begins immediately after the physical handoff. -/
def negativePrior (prior : Program width 8) (allocated : Nat) : Program width 8 :=
  prior ++ negativeHandoffCode width prior.size allocated

def negativeResident (prior : Program width 8) (allocated : Nat)
    (graph : DAG n) (rows : List Row) (negativeRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n) : Program width 8 :=
  residentProgram (coldPrefix (negativePrior prior allocated))
    (controlledHeap (width := width) graph rows negativeRoots target)
    (controlledLayout (width := width) graph rows negativeRoots target)
    n (Nat.le_add_right _ _)
    (zeroQueries width graph rows negativeRoots rowsMatch b target)

@[simp] theorem negativePrior_size (prior : Program width 8) (allocated : Nat) :
    (negativePrior prior allocated).size = prior.size + 7 := by
  simp only [negativePrior, Array.size_append, negativeHandoffCode_size]

/-- Both layers of the resident assembler preserve every actual instruction
of the preceding array, including the release/pop/clear handoff. -/
theorem negative_resident_prior_fetch (prior : Program width 8) (allocated : Nat)
    (graph : DAG n) (rows : List Row) (negativeRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n)
    (position : Nat) (before : position < (negativePrior prior allocated).size) :
    (negativeResident prior allocated graph rows negativeRoots rowsMatch b target)[position]? =
      (negativePrior prior allocated)[position]? := by
  unfold negativeResident
  rw [resident_prior_fetch _ _ _ _ _ _ _ (by rw [coldPrefix_size]; omega)]
  have contents := materialize_contents (negativePrior prior allocated)
    ((ForestZeroControlLoad.code width (negativePrior prior allocated).size ++
      [Instruction.pop 2]).map RegisterWiden.widenInstruction)
  have getter := congrArg (fun items : List (Instruction width 8) => items[position]?) contents
  simp only [Array.getElem?_toList] at getter
  unfold coldPrefix
  rw [getter, List.getElem?_append_left (by simpa only [Array.length_toList] using before)]
  simp only [Array.getElem?_toList]

theorem negative_resident_handoff_at (prior : Program width 8) (allocated : Nat)
    (graph : DAG n) (rows : List Row) (negativeRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n) :
    RawTransferLoops.CodeAt
      (negativeResident prior allocated graph rows negativeRoots rowsMatch b target)
      prior.size (negativeHandoffCode width prior.size allocated) := by
  intro slot
  rw [negative_resident_prior_fetch prior allocated graph rows negativeRoots rowsMatch b target
    (prior.size + slot.val)
    (by rw [negativePrior_size]; have := slot.isLt; simp only [negativeHandoffCode_size] at this; omega)]
  unfold negativePrior
  rw [Array.getElem?_append_right (show prior.size ≤ prior.size + slot.val from by omega)]
  simp only [Nat.add_sub_cancel_left]

/-- The actual cleared endpoint, its empty heap and its retained target word
identify the zero-query loader entry without a supplied initial-state record. -/
theorem negative_cold_initial (state : Controller.Cost.State width 8)
    (prior : Program width 8) (allocated : Nat) (graph : DAG n)
    (rows : List Row) (negativeRoots : List Nat) (target : Fin n)
    (rest output : List (Word width))
    (position : state.pc = word width ((negativePrior prior allocated).size))
    (running : state.halted = false) (empty : state.heap = #[])
    (stack : state.stack = (inputPacket n 0 rows negativeRoots).map (word width) ++
      (word width target.val :: rest))
    (outputs : state.output = output) (zero : state.reg 3 = word width 0) :
    coldInitial graph rows negativeRoots target (negativePrior prior allocated).size rest output
      (state.reg 0) (state.reg 1) (state.reg 2) state.reg = state := by
  have shape := cleared_counter_state state (negativePrior prior allocated).size position running zero
  rw [empty, stack, outputs] at shape
  exact shape

end Controller.Cost.ForestRootProjection


namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestIndexedOperands
variable {width n : Nat}

/-- The selected-result failure path physically releases the positive packet
and enters the negative source caller in the same resident program. -/
theorem negative_original_cold_execution (prior : Program width 8)
    (graph : DAG n) (forest : graph.FormulaForest) (guarded : graph.Guarded)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (rootsMatch : RootsMatch graph negativeRoots)
    (b : Nat) (target : Fin n) (state : Controller.Cost.State width 8)
    (rest : List (Word width))
    (position : state.pc = word width prior.size) (running : state.halted = false)
    (heap : state.heap = cacheHeap width
      (UniformDAGRun.packetHeaderHeap width n rows positiveRoots) rows positiveRoots)
    (stack : state.stack = word width negativeRoots.length ::
      ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest)))
    (mask : state.reg 7 = word width (2 ^ width - 1)) (zero : state.reg 6 = word width 0)
    (allocatedRoom : sourcePrefixCells rows + positiveRoots.length < 2 ^ width)
    (programRoom :
      (negativeResident prior (sourcePrefixCells rows + positiveRoots.length)
        graph rows negativeRoots rowsMatch b target).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) graph rows negativeRoots target).size +
      2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (negativeResident prior (sourcePrefixCells rows + positiveRoots.length)
        graph rows negativeRoots rowsMatch b target) state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 4 * (sourcePrefixCells rows + positiveRoots.length) + 4 +
        63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        14 * (n + graph.nodeCount) + 4288 * graph.roots.length +
        2772 * graph.childIncidences + 387 * graph.guardIncidences + 13 * n + 2 ∧
      peak ≤ state.liveWords + 2 * (n + graph.nodeCount) + 146 * graph.roots.length +
        105 * graph.childIncidences + 15 * graph.guardIncidences + 2 * n + 21 ∧
      (answer = true ↔ ∃ position : Fin (zeroQueries width graph rows negativeRoots rowsMatch b target).length,
        Controller.CNF.Satisfiable (constructorFormula (controlledHeap (width := width) graph rows negativeRoots target)
          (controlledLayout (width := width) graph rows negativeRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (zeroQueries width graph rows negativeRoots rowsMatch b target)[position] n (Nat.le_add_right _ _))) ∧
      (answer = true → ∃ position : Fin (zeroQueries width graph rows negativeRoots rowsMatch b target).length,
        Controller.CNF.Satisfiable (constructorFormula (controlledHeap (width := width) graph rows negativeRoots target)
          (controlledLayout (width := width) graph rows negativeRoots target)
          (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (zeroQueries width graph rows negativeRoots rowsMatch b target)[position] n (Nat.le_add_right _ _)) ∧
        QueryChannelWitness (controlledHeap (width := width) graph rows negativeRoots target)
          (controlledLayout (width := width) graph rows negativeRoots target)
          (zeroQueries width graph rows negativeRoots rowsMatch b target)[position] n (Nat.le_add_right _ _) final.output) := by
  let allocated := sourcePrefixCells rows + positiveRoots.length
  let priorNext := negativePrior prior allocated
  let program := negativeResident prior allocated graph rows negativeRoots rowsMatch b target
  have priorRoom : prior.size + 7 < 2 ^ width := by
    have nextSize : priorNext.size ≤ program.size := by
      change (negativePrior prior allocated).size ≤
        (residentProgram (coldPrefix (negativePrior prior allocated)) _ _ _ _ _).size
      unfold residentProgram
      rw [materialize_size, coldPrefix_size]
      omega
    have priorSize : priorNext.size = prior.size + 7 := negativePrior_size prior allocated
    have fullRoom : program.size < 2 ^ width := programRoom
    omega
  have heapSize : state.heap.size = allocated := by
    rw [heap, cacheHeap_size, UniformDAGRun.packetHeaderHeap_size]
    unfold allocated sourcePrefixCells
    omega
  obtain ⟨ready, firstPeak, firstTrace, firstSpace, readyHeap, readyStack, readyOutput,
      readyPC, readyRunning, readyZero, readyCount, readyFrame⟩ :=
    negative_handoff_execution program prior.size allocated state (word width negativeRoots.length)
      ((inputPacket n 0 rows negativeRoots).map (word width)) (word width target.val :: rest)
      position running priorRoom allocatedRoom heapSize stack mask zero
      (negative_resident_handoff_at prior allocated graph rows negativeRoots rowsMatch b target)
  have coldState : coldInitial graph rows negativeRoots target priorNext.size rest state.output
      (ready.reg 0) (ready.reg 1) (ready.reg 2) ready.reg = ready :=
    negative_cold_initial ready prior allocated graph rows negativeRoots target rest state.output
      (by simpa only [priorNext, negativePrior_size] using readyPC) readyRunning readyHeap
      readyStack readyOutput readyZero
  obtain ⟨answer, final, lastTicks, lastPeak, lastTrace, halted, tag, lastTime, lastSpace,
      meaning, model⟩ := cold_zero_resident_execution graph guarded rows negativeRoots rowsMatch rootsMatch
        b target forest priorNext rest state.output (ready.reg 0) (ready.reg 1) (ready.reg 2)
        ready.reg programRoom wordRoom
  rw [coldState] at lastTrace lastSpace
  have readyLive : ready.liveWords ≤ state.liveWords :=
    (Execution.final_storage_le firstTrace).trans firstSpace
  refine ⟨answer, final, (4 * allocated + 4) + lastTicks, max firstPeak lastPeak,
    firstTrace.append lastTrace, halted, tag, ?_, ?_, meaning, model⟩
  · dsimp only [allocated]
    omega
  · exact max_le (by omega) (lastSpace.trans (by omega))

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

def targetTailCode (width : Nat) : Program width 8 := #[Instruction.pop 3, .halt]

/-- The target control word is consumed by a fetched pop before the successful
branch halts; the detecting bits and decision register are preserved. -/
theorem target_tail_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (targetWord : Word width) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (stack : state.stack = targetWord :: rest)
    (present : RawTransferLoops.CodeAt program entry (targetTailCode width)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = true ∧ final.reg 4 = state.reg 4 := by
  let popped := { state.advance.put 3 targetWord with stack := rest }
  let final := { popped.advance with halted := true }
  have popAt : program[entry]? = some (.pop 3) := by
    simpa [targetTailCode] using present ⟨0, by simp [targetTailCode]⟩
  have haltAt : program[entry + 1]? = some .halt := by
    simpa [targetTailCode] using present ⟨1, by simp [targetTailCode]⟩
  have popStep : programStep program state = some popped := by
    rw [fetched program state entry _ position (by omega) popAt]
    simp only [step, running, Bool.false_eq_true, ite_false, stack]
    rfl
  have poppedPC : popped.pc = word width (entry + 1) := by
    change word width (state.pc.val + 1) = _
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have haltStep : programStep program popped = some final := by
    rw [fetched program popped (entry + 1) _ poppedPC (by omega) haltAt]
    simp only [step, show popped.halted = false from running, Bool.false_eq_true, ite_false]
    rfl
  have poppedLive : popped.liveWords + 1 = state.liveWords := by
    simp only [popped, State.liveWords, State.put, State.advance, stack, List.length_cons]
    omega
  have finalLive : final.liveWords = popped.liveWords := rfl
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, rfl, ?_⟩
  · simpa only [finalLive, Nat.max_self, Nat.zero_add,
      Nat.max_eq_left (by omega : popped.liveWords ≤ state.liveWords)] using
      Execution.cons popStep (Execution.cons haltStep (Execution.refl final))
  · change word width (popped.pc.val + 1) = _
    rw [poppedPC, show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  · simp only [final, popped, State.advance, State.put, Fin.reduceEq, ite_false]

def positiveTargetCleanupCode (width entry allocated sourcePrefix : Nat) : Program width 8 :=
  #[.constant 0 (word width allocated)] ++
    countedReleaseCode width (entry + 1) (entry + 5) ++
    #[.pop 0, .constant 1 (word width sourcePrefix), .add 0 0 1] ++
    discardCode width (entry + 8) (entry + 12) ++ targetTailCode width

@[simp] theorem positiveTargetCleanupCode_size (width entry allocated sourcePrefix : Nat) :
    (positiveTargetCleanupCode width entry allocated sourcePrefix).size = 14 := by
  simp [positiveTargetCleanupCode, targetTailCode]

theorem positive_target_cleanup_execution (program : Program width 8)
    (entry allocated basePrefix count : Nat) (state : State width 8)
    (packet rest : List (Word width)) (targetWord : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 14 < 2 ^ width)
    (allocatedRoom : allocated < 2 ^ width) (packetRoom : basePrefix + count < 2 ^ width)
    (heapSize : state.heap.size = allocated) (packetSize : packet.length = basePrefix + count)
    (stack : state.stack = word width count :: (packet ++ (targetWord :: rest)))
    (mask : state.reg 7 = word width (2 ^ width - 1)) (zero : state.reg 6 = word width 0)
    (present : RawTransferLoops.CodeAt program entry (positiveTargetCleanupCode width entry allocated basePrefix)) :
    ∃ final peak, Execution program state final (4 * allocated + 4 * (basePrefix + count) + 8) peak ∧
      peak ≤ state.liveWords ∧ final.heap = #[] ∧ final.stack = rest ∧
      final.output = state.output ∧ final.pc = word width (entry + 14) ∧ final.halted = true ∧
      final.reg 4 = state.reg 4 := by
  let first := state.advance.put 0 (word width allocated)
  have firstAt : program[entry]? = some (.constant 0 (word width allocated)) := by
    simpa [positiveTargetCleanupCode] using present ⟨0, by simp⟩
  have t0 : programStep program state = some first := by
    rw [fetched program state entry _ position (by omega) firstAt]
    simp only [step, running, Bool.false_eq_true, ite_false]
    rfl
  have firstTrace : Execution program state first 1 state.liveWords := by
    have live : first.liveWords = state.liveWords := rfl
    simpa only [live, Nat.max_self, Nat.zero_add] using
      Execution.cons t0 (Execution.refl first)
  have firstPC : first.pc = word width (entry + 1) := by
    change word width (state.pc.val + 1) = _
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have releaseAt : RawTransferLoops.CodeAt program (entry + 1) (countedReleaseCode width (entry + 1) (entry + 5)) := by
    intro slot
    have found := present ⟨1 + slot.val, by have := slot.isLt; simp at this; simp; omega⟩
    fin_cases slot <;>
      simpa [positiveTargetCleanupCode, targetTailCode, countedReleaseCode, discardCode, Nat.add_assoc] using found
  obtain ⟨released, releasePeak, releaseTrace, releaseSpace, releasedHeap, releasedStack,
      releasedOutput, releasedPC, releasedRunning, releasedZero, releasedFrame⟩ :=
    counted_release_execution program (entry + 1) (entry + 5) allocated first firstPC running
      (by omega) heapSize allocatedRoom (by simp [first, State.put]) mask zero releaseAt
  have prepAt0 : program[entry + 5]? = some (.pop 0) := by
    simpa [positiveTargetCleanupCode, targetTailCode, countedReleaseCode, discardCode] using present ⟨5, by simp⟩
  have prepAt1 : program[entry + 6]? = some (.constant 1 (word width basePrefix)) := by
    simpa [positiveTargetCleanupCode, targetTailCode, countedReleaseCode, discardCode] using present ⟨6, by simp⟩
  have prepAt2 : program[entry + 7]? = some (.add 0 0 1) := by
    simpa [positiveTargetCleanupCode, targetTailCode, countedReleaseCode, discardCode] using present ⟨7, by simp⟩
  obtain ⟨ready, prepTrace, readyPC, readyRunning, readyHeap, readyStack, readyOutput,
      readyCount, readyFrame⟩ := negative_discard_prepare program (entry + 5) basePrefix count released
        packet (targetWord :: rest) releasedPC releasedRunning (by omega) packetRoom
        (releasedStack.trans stack) prepAt0 (by simpa only [Nat.add_assoc] using prepAt1)
        (by simpa only [Nat.add_assoc] using prepAt2)
  have discardAt : RawTransferLoops.CodeAt program (entry + 8) (discardCode width (entry + 8) (entry + 12)) := by
    intro slot
    have found := present ⟨8 + slot.val, by have := slot.isLt; simp at this; simp; omega⟩
    fin_cases slot <;>
      simpa [positiveTargetCleanupCode, targetTailCode, countedReleaseCode, discardCode, Nat.add_assoc] using found
  have readyMask : ready.reg 7 = word width (2 ^ width - 1) :=
    (readyFrame 7 (by decide) (by decide)).trans
      ((releasedFrame 7 (by decide)).trans mask)
  have readyZero : ready.reg 6 = word width 0 :=
    (readyFrame 6 (by decide) (by decide)).trans
      ((releasedFrame 6 (by decide)).trans zero)
  obtain ⟨discarded, discardPeak, discardTrace, discardSpace, discardedHeap, discardedStack,
      discardedOutput, discardedPC, discardedRunning, discardedCount, discardedFrame⟩ :=
    discard_execution program (entry + 8) (entry + 12) packet (targetWord :: rest) ready
      (by simpa only [Nat.add_assoc] using readyPC) readyRunning (by omega) readyStack
      (by simpa only [packetSize] using packetRoom)
      (by simpa only [packetSize] using readyCount) readyMask readyZero discardAt
  have tailAt : RawTransferLoops.CodeAt program (entry + 12) (targetTailCode width) := by
    intro phase
    have found := present ⟨12 + phase.val, by have := phase.isLt; simp [targetTailCode] at this; simp; omega⟩
    fin_cases phase <;>
      simpa [positiveTargetCleanupCode, targetTailCode, countedReleaseCode, discardCode, Nat.add_assoc] using found
  obtain ⟨final, tailTrace, tailHeap, tailStack, tailOutput, tailPC, tailHalted, tailFrame⟩ :=
    target_tail_execution program (entry + 12) discarded targetWord rest discardedPC discardedRunning
      (by omega) discardedStack tailAt
  have firstLive : first.liveWords = state.liveWords := rfl
  have releasedLive : released.liveWords ≤ state.liveWords :=
    (Execution.final_storage_le releaseTrace).trans (by simpa only [firstLive] using releaseSpace)
  have readyLive : ready.liveWords ≤ released.liveWords := Execution.final_storage_le prepTrace
  have discardedLive : discarded.liveWords ≤ ready.liveWords :=
    (Execution.final_storage_le discardTrace).trans discardSpace
  have joined := ((firstTrace.append releaseTrace).append prepTrace).append
    (discardTrace.append tailTrace)
  have totalTicks : 1 + (4 * allocated + 1) + 3 + (4 * packet.length + 1 + 2) =
      4 * allocated + 4 * (basePrefix + count) + 8 := by
    rw [packetSize]
    omega
  refine ⟨final, max (max (max state.liveWords releasePeak) released.liveWords)
    (max discardPeak discarded.liveWords), ?_, ?_, ?_, tailStack, ?_, ?_, tailHalted, ?_⟩
  · simpa only [totalTicks] using joined
  · apply max_le
    · apply max_le
      · apply max_le
        · exact le_rfl
        · simpa only [firstLive] using releaseSpace
      · exact releasedLive
    · apply max_le
      · exact discardSpace.trans (readyLive.trans releasedLive)
      · exact discardedLive.trans (readyLive.trans releasedLive)
  · exact tailHeap.trans (discardedHeap.trans (readyHeap.trans releasedHeap))
  · exact tailOutput.trans (discardedOutput.trans (readyOutput.trans (releasedOutput.trans rfl)))
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using tailPC
  · exact tailFrame.trans ((discardedFrame 4 (by decide) (by decide)).trans
      ((readyFrame 4 (by decide) (by decide)).trans
        ((releasedFrame 4 (by decide)).trans rfl)))

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorDescriptors
variable {width n : Nat}

theorem selected_source_target_cleanup_execution (prior : Program width 8)
    (items : List (Instruction width 4)) (graph : DAG n) (rows : List Row)
    (positiveRoots negativeRoots : List Nat) (state : State width 8)
    (rest : List (Word width)) (targetWord : Word width)
    (position : state.pc = word width (prior.size + items.length))
    (running : state.halted = false)
    (room : prior.size + items.length + 14 < 2 ^ width)
    (allocatedRoom : sourceAllocatedCells graph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (heapSize : state.heap.size =
      (setupHeap width (cacheHeap width
        (UniformDAGRun.packetHeaderHeap width n rows positiveRoots) rows positiveRoots) graph).size)
    (stack : state.stack = word width negativeRoots.length ::
      ((inputPacket n 0 rows negativeRoots).map (word width) ++ (targetWord :: rest)))
    (mask : state.reg 7 = word width (2 ^ width - 1)) (zero : state.reg 6 = word width 0) :
    let continuation := positiveTargetCleanupCode width (prior.size + items.length)
      (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
    ∃ final peak, Execution (weightedResident prior items continuation) state final
      (4 * sourceAllocatedCells graph rows positiveRoots +
        4 * (sourcePrefixCells rows + negativeRoots.length) + 8) peak ∧
      peak ≤ state.liveWords ∧ final.heap = #[] ∧ final.stack = rest ∧
      final.output = state.output ∧
      final.pc = word width (prior.size + items.length + 14) ∧ final.halted = true ∧
      final.reg 4 = state.reg 4 := by
  let continuation := positiveTargetCleanupCode width (prior.size + items.length)
    (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
  exact positive_target_cleanup_execution (weightedResident prior items continuation)
    (prior.size + items.length) (sourceAllocatedCells graph rows positiveRoots)
    (sourcePrefixCells rows) negativeRoots.length state
    ((inputPacket n 0 rows negativeRoots).map (word width)) rest targetWord position running room
    allocatedRoom packetRoom
    (heapSize.trans (source_allocated_heap_size graph rows positiveRoots))
    (source_negative_packet_size rows negativeRoots) stack mask zero
    (weighted_continuation_present prior items continuation)


end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestWitnessMarshal Controller.Cost.ForestCounter
open Controller.Cost.RegisterWiden
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem selected_original_positive_target_execution (prior : Program width 8)
    (saved : Fin 8 → Word width) (graph : DAG n)
    (forest : graph.FormulaForest) (guarded : graph.Guarded)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph positiveRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (target : Channel n) (candidate : Candidate W)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (address loaded temporary : Word width) (rest output : List (Word width))
    (sourceRoom : sourceAllocatedCells graph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (programRoom : prior.size + (4 * (buildRoots graph).count + 2 * n + 100) + 14 < 2 ^ width)
    (mask : saved 7 = word width (2 ^ width - 1)) (zero : saved 6 = word width 0)
    (success : saved 4 = word width 1) :
    let header := UniformDAGRun.packetHeaderHeap width n rows positiveRoots
    let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
    let items := selectedItems width header graph rows positiveRoots computed candidate
      countFits positionFits prior.size 0
    let stack := word width negativeRoots.length ::
      ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest))
    let continuation := positiveTargetCleanupCode width (prior.size + items.length)
      (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution (weightedResident prior items continuation)
          (widenState ((counterState (cacheHeap width header rows positiveRoots) prior.size
            address loaded temporary).frame stack output) saved) final ticks peak ∧
        ticks ≤ 18 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          12 * n + 4 * sourceAllocatedCells graph rows positiveRoots +
          4 * (sourcePrefixCells rows + negativeRoots.length) + 32 ∧
        peak ≤ 9 + sourceAllocatedCells graph rows positiveRoots +
          (buildRoots graph).count + sourcePrefixCells rows + negativeRoots.length +
          rest.length + output.length + n + 3 ∧
        final.heap = #[] ∧ final.stack = rest ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
        final.halted = true ∧ final.reg 4 = word width 1 := by
  let header := UniformDAGRun.packetHeaderHeap width n rows positiveRoots
  let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
  let items := selectedItems width header graph rows positiveRoots computed candidate
    countFits positionFits prior.size 0
  let stack := word width negativeRoots.length ::
    ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest))
  let continuation := positiveTargetCleanupCode width (prior.size + items.length)
    (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
  have itemLength : items.length = 4 * (buildRoots graph).count + 2 * n + 100 :=
    selectedItems_length header graph rows positiveRoots matched rootMatches weights b target
      candidate countFits positionFits prior.size 0
  have countValid : 0 < header.size := by
    simp only [header, UniformDAGRun.packetHeaderHeap_size]
    omega
  have countWord : header[0] = word width n := by
    simp [header, UniformDAGRun.packetHeaderHeap, globalHeader]
  have heapRoom : (setupHeap width (cacheHeap width header rows positiveRoots) graph).size ≤ 2 ^ width := by
    rw [source_allocated_heap_size]
    exact sourceRoom.le
  obtain ⟨arithmetic, position, rootEq, blocked, selectedFinal, firstTicks, firstPeak,
      admissible, feasible, score, optimal, firstTrace, firstTime, firstSpace, selectedStack,
      selectedOutput, selectedPC, selectedRunning, selectedHeap, selectedFrame⟩ :=
    selected_resident_eight_execution prior continuation saved header graph forest guarded rows
      positiveRoots matched rootMatches weights nonnegative b target candidate chosen countFits positionFits
      0 address loaded temporary stack output countValid countWord heapRoom (by omega)
  have selectedEntry : selectedFinal.pc = word width (prior.size + items.length) := by
    rw [itemLength]
    have scalar : prior.size + 4 * (buildRoots graph).count + 2 * (n + 3) + 94 =
        prior.size + (4 * (buildRoots graph).count + 2 * n + 100) := by omega
    exact selectedPC.trans (congrArg (word width) scalar)
  obtain ⟨final, lastPeak, lastTrace, lastSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalHalted, finalFrame⟩ := selected_source_target_cleanup_execution prior items graph rows
        positiveRoots negativeRoots selectedFinal rest (word width target.val) selectedEntry selectedRunning
        (by rw [itemLength]; exact programRoom) sourceRoom packetRoom selectedHeap
        selectedStack ((selectedFrame 7 (by decide)).trans mask)
        ((selectedFrame 6 (by decide)).trans zero)
  have finalLive : selectedFinal.liveWords ≤ firstPeak := Execution.final_storage_le firstTrace
  have joined := firstTrace.append lastTrace
  refine ⟨position, rootEq, blocked, final, firstTicks +
    (4 * sourceAllocatedCells graph rows positiveRoots +
      4 * (sourcePrefixCells rows + negativeRoots.length) + 8),
    max firstPeak lastPeak, admissible, feasible, score, optimal, joined, by omega,
    ?_, finalHeap, finalStack, finalOutput.trans selectedOutput, finalHalted,
    finalFrame.trans ((selectedFrame 4 (by decide)).trans success)⟩
  have stackSize : stack.length = sourcePrefixCells rows + negativeRoots.length + rest.length + 2 := by
    simp only [stack, List.length_cons, List.length_append, source_negative_packet_size] <;> omega
  have sourceSize := source_allocated_heap_size (width := width) graph rows positiveRoots
  have firstBound : firstPeak ≤ 9 + sourceAllocatedCells graph rows positiveRoots +
      (buildRoots graph).count + sourcePrefixCells rows + negativeRoots.length +
      rest.length + output.length + n + 3 := by
    rw [sourceSize] at firstSpace
    rw [stackSize] at firstSpace
    omega
  exact max_le firstBound (lastSpace.trans (finalLive.trans firstBound))

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

def mixedMaskCode (width : Nat) : Program width 8 :=
  #[Instruction.constant 6 (word width 0), .constant 7 (word width (2 ^ width - 1))]

@[simp] theorem mixedMaskCode_size (width : Nat) : (mixedMaskCode width).size = 2 := rfl

theorem mixed_mask_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 2 < 2 ^ width)
    (present : RawTransferLoops.CodeAt program entry (mixedMaskCode width)) :
    ∃ ready, Execution program state ready 2 state.liveWords ∧
      ready.pc = word width (entry + 2) ∧ ready.halted = false ∧
      ready.heap = state.heap ∧ ready.stack = state.stack ∧ ready.output = state.output ∧
      ready.reg 6 = word width 0 ∧ ready.reg 7 = word width (2 ^ width - 1) ∧
      (∀ register : Fin 8, register ≠ 6 → register ≠ 7 → ready.reg register = state.reg register) := by
  let middle := state.advance.put 6 (word width 0)
  let ready := middle.advance.put 7 (word width (2 ^ width - 1))
  have firstAt : program[entry]? = some (.constant 6 (word width 0)) := by
    simpa [mixedMaskCode] using present ⟨0, by simp⟩
  have secondAt : program[entry + 1]? = some (.constant 7 (word width (2 ^ width - 1))) := by
    simpa [mixedMaskCode] using present ⟨1, by simp⟩
  have firstStep : programStep program state = some middle := by
    rw [fetched program state entry _ position (by omega) firstAt]
    simp only [step, running, Bool.false_eq_true, ite_false]
    rfl
  have middlePC : middle.pc = word width (entry + 1) := by
    change word width (state.pc.val + 1) = _
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have secondStep : programStep program middle = some ready := by
    rw [fetched program middle (entry + 1) _ middlePC (by omega) secondAt]
    simp only [step, show middle.halted = false from running, Bool.false_eq_true, ite_false]
    rfl
  have middleLive : middle.liveWords = state.liveWords := rfl
  have readyLive : ready.liveWords = state.liveWords := rfl
  refine ⟨ready, ?_, ?_, running, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa only [middleLive, readyLive, Nat.max_self, Nat.zero_add] using
      Execution.cons firstStep (Execution.cons secondStep (Execution.refl ready))
  · change word width (middle.pc.val + 1) = _
    rw [middlePC, show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  · simp only [ready, middle, State.put, State.advance, Fin.reduceEq, ite_false, ite_true]
  · simp only [ready, State.put, ite_true]
  · intro register other6 other7
    simp only [ready, middle, State.put, State.advance, ite_eq_right other7, ite_eq_right other6]

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The actual clear and weighted-result branch establish both the counter
entry ABI and the physical decision register from the same source run. -/
theorem mixed_clear_selector_execution (program : Program width 8) (entry failure : Nat)
    (rows : List Row) (roots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (state : Controller.Cost.State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 3 < 2 ^ width)
    (present : RawTransferLoops.CodeAt program entry
      (#[Instruction.constant 3 (word width 0)] ++
        mixedSelectorCode width failure rows roots weights b target)) :
    let chosen := (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected.isSome
    ∃ ready, Execution program state ready 3 state.liveWords ∧
      ready.pc = word width (if chosen then entry + 3 else failure) ∧ ready.halted = false ∧
      ready.heap = state.heap ∧ ready.stack = state.stack ∧ ready.output = state.output ∧
      ready.reg 3 = word width 0 ∧ ready.reg 4 = boolWord width chosen ∧
      (∀ register : Fin 8, register ≠ 3 → register ≠ 4 → ready.reg register = state.reg register) := by
  let first := state.advance.put 3 (word width 0)
  have clearAt : program[entry]? = some (.constant 3 (word width 0)) := by
    simpa [mixedSelectorCode] using present ⟨0, by simp⟩
  obtain ⟨firstTrace, firstPC, firstRunning, firstHeap, firstStack, firstOutput, firstZero, firstFrame⟩ :=
    clear_loader_zero_execution program entry state position running (by omega) clearAt
  have selectorAt : RawTransferLoops.CodeAt program (entry + 1)
      (mixedSelectorCode width failure rows roots weights b target) := by
    intro phase
    have found := present ⟨1 + phase.val, by have := phase.isLt; simp at this; simp; omega⟩
    fin_cases phase <;> simpa [mixedSelectorCode, Nat.add_assoc] using found
  obtain ⟨ready, lastTrace, readyPC, readyRunning, readyHeap, readyStack, readyOutput, readyTag, readyFrame⟩ :=
    mixed_selector_execution program (entry + 1) failure rows roots weights b target first
      firstPC firstRunning (by omega) selectorAt
  have firstLive : first.liveWords = state.liveWords := rfl
  refine ⟨ready, ?_, ?_, readyRunning, readyHeap.trans firstHeap, readyStack.trans firstStack,
    readyOutput.trans firstOutput, (readyFrame 3 (by decide)).trans firstZero, readyTag, ?_⟩
  · simpa only [firstLive, Nat.max_self] using firstTrace.append lastTrace
  · have scalar : entry + 1 + 2 = entry + 3 := by omega
    simpa only [scalar] using readyPC
  · intro register other3 other4
    exact (readyFrame register other4).trans (firstFrame register other3)

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem mixed_prefix_execution (program : Program width 8) (entry failure : Nat)
    (rows : List Row) (roots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (state : Controller.Cost.State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 5 < 2 ^ width)
    (present : RawTransferLoops.CodeAt program entry
      (mixedMaskCode width ++ #[Instruction.constant 3 (word width 0)] ++
        mixedSelectorCode width failure rows roots weights b target)) :
    let chosen := (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected.isSome
    ∃ ready, Execution program state ready 5 state.liveWords ∧
      ready.pc = word width (if chosen then entry + 5 else failure) ∧ ready.halted = false ∧
      ready.heap = state.heap ∧ ready.stack = state.stack ∧ ready.output = state.output ∧
      ready.reg 3 = word width 0 ∧ ready.reg 4 = boolWord width chosen ∧
      ready.reg 6 = word width 0 ∧ ready.reg 7 = word width (2 ^ width - 1) ∧
      (∀ register : Fin 8, register ≠ 3 → register ≠ 4 → register ≠ 6 → register ≠ 7 →
        ready.reg register = state.reg register) := by
  have maskAt : RawTransferLoops.CodeAt program entry (mixedMaskCode width) := by
    intro phase
    have actual := present ⟨phase.val, by have := phase.isLt; simp at this; simp; omega⟩
    fin_cases phase <;> simpa [mixedMaskCode, mixedSelectorCode] using actual
  obtain ⟨middle, maskTrace, middlePC, middleRunning, middleHeap, middleStack, middleOutput,
      middleZero, middleMask, middleFrame⟩ :=
    mixed_mask_execution program entry state position running (by omega) maskAt
  have remainderAt : RawTransferLoops.CodeAt program (entry + 2)
      (#[Instruction.constant 3 (word width 0)] ++ mixedSelectorCode width failure rows roots weights b target) := by
    intro phase
    have actual := present ⟨2 + phase.val, by have := phase.isLt; simp [mixedSelectorCode] at this; simp; omega⟩
    fin_cases phase <;> simpa [mixedMaskCode, mixedSelectorCode, Nat.add_assoc] using actual
  obtain ⟨ready, remainderTrace, readyPC, readyRunning, readyHeap, readyStack, readyOutput,
      readyZero, readyTag, readyFrame⟩ := mixed_clear_selector_execution program (entry + 2) failure
        rows roots weights b target middle middlePC middleRunning (by omega) remainderAt
  have middleLive : middle.liveWords = state.liveWords := by
    simp only [State.liveWords, middleHeap, middleStack, middleOutput]
  refine ⟨ready, ?_, ?_, readyRunning, readyHeap.trans middleHeap, readyStack.trans middleStack,
    readyOutput.trans middleOutput, readyZero, readyTag,
    (readyFrame 6 (by decide) (by decide)).trans middleZero,
    (readyFrame 7 (by decide) (by decide)).trans middleMask, ?_⟩
  · simpa only [middleLive, Nat.max_self] using maskTrace.append remainderTrace
  · have scalar : entry + 2 + 3 = entry + 5 := by omega
    simpa only [scalar] using readyPC
  · intro register other3 other4 other6 other7
    exact (readyFrame register other3 other4).trans (middleFrame register other6 other7)

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedPhysicalOptimal
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Every source operand in the selector is determined by the indexed weighted
run over the positive root occurrences. The low loader register is cleared
before either weighted reconstruction or the negative source handoff. -/
def mixedBranchPrefix (prior : Program width 8) (failure : Nat)
    (rows : List Row) (positiveRoots : List Nat) (weights : Channel n → W)
    (b : Nat) (target : Channel n) : Program width 8 :=
  prior ++ mixedMaskCode width ++ #[Instruction.constant 3 (word width 0)] ++
    mixedSelectorCode width failure rows positiveRoots weights b target

@[simp] theorem mixedBranchPrefix_size (prior : Program width 8) (failure : Nat)
    (rows : List Row) (positiveRoots : List Nat) (weights : Channel n → W)
    (b : Nat) (target : Channel n) :
    (mixedBranchPrefix prior failure rows positiveRoots weights b target).size = prior.size + 5 := by
  simp only [mixedBranchPrefix, Array.size_append, mixedMaskCode_size, mixedSelectorCode_size]
  change prior.size + 2 + 1 + 2 = prior.size + 5
  omega

/-- The selected incumbent determines the actual weighted suffix. With no
incumbent, the same selector falls directly into the negative handoff. -/
def mixedPositiveProgram (prior : Program width 8) (graph : DAG n) (rows : List Row)
    (positiveRoots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width) : Program width 8 :=
  let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
  match computed.selected with
  | none => mixedBranchPrefix prior (prior.size + 5) rows positiveRoots weights b target
  | some candidate =>
    let header := UniformDAGRun.packetHeaderHeap width n rows positiveRoots
    let items := selectedItems width header graph rows positiveRoots computed candidate
      countFits positionFits (prior.size + 5) 0
    let endAt := prior.size + 5 + items.length
    let cleanup := positiveTargetCleanupCode width endAt
      (sourceAllocatedCells graph rows positiveRoots) (sourcePrefixCells rows)
    weightedResident
      (mixedBranchPrefix prior (endAt + 14) rows positiveRoots weights b target) items cleanup

/-- Both root families share the resident prefix and the physical branch.
The negative continuation receives the source packet retained by the filter. -/
def mixedResident (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (negativeMatched : RowsMatch negativeGraph rows)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width) : Program width 8 :=
  negativeResident
    (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target countFits positionFits)
    (sourcePrefixCells rows + positiveRoots.length)
    negativeGraph rows negativeRoots negativeMatched b target

/-- Appending the weighted suffix and cleanup preserves the actual preceding
instructions independently of the selected witness length. -/
theorem weighted_resident_prior_fetch (prior : Program width 8)
    (items : List (Instruction width 4)) (continuation : Program width 8)
    (position : Nat) (before : position < prior.size) :
    (weightedResident prior items continuation)[position]? = prior[position]? := by
  have contents : (weightedResident prior items continuation).toList =
      prior.toList ++ (items.map RegisterWiden.widenInstruction) ++ continuation.toList := by
    simp only [weightedResident, Array.toList_append, Array.toArrayAux_eq, List.append_assoc]
  have getter := congrArg (fun entries : List (Instruction width 8) => entries[position]?) contents
  simp only [Array.getElem?_toList, List.append_assoc] at getter
  rw [getter, List.getElem?_append_left (by simpa only [Array.length_toList] using before)]
  simp only [Array.getElem?_toList]

/-- The failure handoff is appended after the complete positive branch;
therefore the selected witness trace uses this exact final resident array. -/
theorem mixed_positive_fetch (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (negativeMatched : RowsMatch negativeGraph rows)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (position : Nat)
    (before : position < (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target
      countFits positionFits).size) :
    (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots negativeMatched
      weights b target countFits positionFits)[position]? =
    (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target
      countFits positionFits)[position]? := by
  unfold mixedResident
  rw [negative_resident_prior_fetch
    (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target countFits positionFits)
    (sourcePrefixCells rows + positiveRoots.length) negativeGraph rows negativeRoots negativeMatched
    b target position (by rw [negativePrior_size]; omega)]
  simp only [negativePrior, Array.getElem?_append_left before]


/-- The selected operand is exactly the successful decision word read by the
physical branch and retained through witness cleanup. -/
theorem selected_selector_word (rows : List Row) (roots : List Nat)
    (weights : Channel n → W) (b : Nat) (target : Channel n) (candidate : Candidate W)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected = some candidate) :
    boolWord width (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected.isSome =
      word width 1 := by
  rw [chosen]
  rfl

theorem none_selector_word (rows : List Row) (roots : List Nat)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected = none) :
    boolWord width (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected.isSome =
      word width 0 := by
  rw [chosen]
  rfl

/-- The entire negative source occurrence stream has linear resident size;
the original optional positive clause is handled by shared fixed loops. -/
theorem negative_resident_size_bound (prior : Program width 8) (allocated : Nat)
    (graph : DAG n) (rows : List Row) (negativeRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n)
    (forest : graph.FormulaForest) :
    (negativeResident prior allocated graph rows negativeRoots rowsMatch b target).size ≤
      prior.size + 833 * graph.roots.length + 183 * graph.childIncidences +
        28 * graph.guardIncidences + 84 := by
  let queries := ForestZeroSourcePlan.zeroQueries width graph rows negativeRoots rowsMatch b target
  have bounds := ForestZeroSourcePlan.zero_queries_forest_bounds
    (width := width) graph rows negativeRoots rowsMatch b target forest
  have counts := ForestZeroSourcePlan.residentInstructions_length
    (ForestZeroSourcePlan.controlledHeap (width := width) graph rows negativeRoots target)
    (ForestZeroSourcePlan.controlledLayout (width := width) graph rows negativeRoots target)
    n (Nat.le_add_right _ _ ) queries
    (ForestZeroSourcePlan.coldPrefix (negativePrior prior allocated)).size
  have querySize : queries.length = graph.roots.length :=
    ForestZeroSourcePlan.zeroQueries_length graph rows negativeRoots rowsMatch b target
  unfold negativeResident ForestZeroSourcePlan.residentProgram
  rw [ForestZeroResident.materialize_size, ForestZeroSourcePlan.coldPrefix_size, negativePrior_size]
  dsimp only [queries] at counts querySize
  rw [querySize, ForestZeroSourcePlan.coldPrefix_size, negativePrior_size] at counts
  omega

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The same indexed selected-result field controls the physical selector,
the candidate constants, and the resident weighted suffix. -/
theorem mixed_selected_program (prior : Program width 8) (graph : DAG n) (rows : List Row)
    (positiveRoots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected = some candidate) :
    let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
    let items := selectedItems width (UniformDAGRun.packetHeaderHeap width n rows positiveRoots)
      graph rows positiveRoots computed candidate countFits positionFits (prior.size + 5) 0
    let cleanupAt := prior.size + 5 + items.length
    mixedPositiveProgram prior graph rows positiveRoots weights b target countFits positionFits =
      weightedResident
        (mixedBranchPrefix prior (cleanupAt + 14) rows positiveRoots weights b target) items
        (positiveTargetCleanupCode width cleanupAt (sourceAllocatedCells graph rows positiveRoots)
          (sourcePrefixCells rows)) := by
  unfold mixedPositiveProgram
  dsimp only
  rw [chosen]

/-- With no selected candidate, the physically fetched failure target is
exactly the beginning of the appended negative handoff. -/
theorem mixed_none_program (prior : Program width 8) (graph : DAG n) (rows : List Row)
    (positiveRoots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected = none) :
    mixedPositiveProgram prior graph rows positiveRoots weights b target countFits positionFits =
      mixedBranchPrefix prior (prior.size + 5) rows positiveRoots weights b target := by
  unfold mixedPositiveProgram
  dsimp only
  rw [chosen]

/-- Fetched prefix instructions remain available after either resident branch
has been appended, without a new program premise at the execution boundary. -/
theorem mixed_none_prefix_at (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (negativeMatched : RowsMatch negativeGraph rows)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected = none) :
    RawTransferLoops.CodeAt
      (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots negativeMatched
        weights b target countFits positionFits) prior.size
      (mixedMaskCode width ++ #[Instruction.constant 3 (word width 0)] ++
        mixedSelectorCode width (prior.size + 5) rows positiveRoots weights b target) := by
  intro phase
  have phaseBound : phase.val < 5 := by simpa [mixedMaskCode, mixedSelectorCode] using phase.isLt
  have fetched := mixed_positive_fetch prior positiveGraph negativeGraph rows positiveRoots negativeRoots
    negativeMatched weights b target countFits positionFits (prior.size + phase.val)
    (by rw [mixed_none_program prior positiveGraph rows positiveRoots weights b target countFits positionFits chosen,
      mixedBranchPrefix_size]; omega)
  rw [fetched, mixed_none_program prior positiveGraph rows positiveRoots weights b target countFits positionFits chosen]
  unfold mixedBranchPrefix
  simp only [Array.append_assoc]
  rw [Array.getElem?_append_right
    (show prior.size ≤ prior.size + phase.val from by omega)]
  simp only [Nat.add_sub_cancel_left]

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

@[simp] theorem weightedResident_size (prior : Program width 8)
    (items : List (Instruction width 4)) (continuation : Program width 8) :
    (weightedResident prior items continuation).size = prior.size + items.length + continuation.size := by
  have actual := CompilerArrayTrace.final_size
    (CompilerArrayTrace.exists_trace (items.map RegisterWiden.widenInstruction) prior)
  simp only [List.length_map] at actual
  unfold weightedResident
  rw [Array.size_append, actual]

theorem mixed_selected_prefix_at (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (negativeMatched : RowsMatch negativeGraph rows)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected = some candidate) :
    let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
    let items := selectedItems width (UniformDAGRun.packetHeaderHeap width n rows positiveRoots)
      positiveGraph rows positiveRoots computed candidate countFits positionFits (prior.size + 5) 0
    let failure := prior.size + 5 + items.length + 14
    RawTransferLoops.CodeAt
      (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots negativeMatched
        weights b target countFits positionFits) prior.size
      (mixedMaskCode width ++ #[Instruction.constant 3 (word width 0)] ++
        mixedSelectorCode width failure rows positiveRoots weights b target) := by
  let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
  let items := selectedItems width (UniformDAGRun.packetHeaderHeap width n rows positiveRoots)
    positiveGraph rows positiveRoots computed candidate countFits positionFits (prior.size + 5) 0
  let failure := prior.size + 5 + items.length + 14
  let tagged := mixedBranchPrefix prior failure rows positiveRoots weights b target
  let cleanup := positiveTargetCleanupCode width (prior.size + 5 + items.length)
    (sourceAllocatedCells positiveGraph rows positiveRoots) (sourcePrefixCells rows)
  have shape : mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target
      countFits positionFits = weightedResident tagged items cleanup :=
    mixed_selected_program prior positiveGraph rows positiveRoots weights b target countFits positionFits candidate chosen
  have taggedSize : tagged.size = prior.size + 5 := mixedBranchPrefix_size prior failure rows positiveRoots weights b target
  have positiveSize : (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target
      countFits positionFits).size = tagged.size + items.length + 14 := by
    rw [shape, weightedResident_size]
    simp only [cleanup, positiveTargetCleanupCode_size]
  change RawTransferLoops.CodeAt
    (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots negativeMatched
      weights b target countFits positionFits) prior.size
    (mixedMaskCode width ++ #[Instruction.constant 3 (word width 0)] ++
      mixedSelectorCode width failure rows positiveRoots weights b target)
  intro phase
  have phaseBound : phase.val < 5 := by simpa [mixedMaskCode, mixedSelectorCode] using phase.isLt
  rw [mixed_positive_fetch prior positiveGraph negativeGraph rows positiveRoots negativeRoots
    negativeMatched weights b target countFits positionFits (prior.size + phase.val)
    (by rw [positiveSize, taggedSize]; omega), shape,
    weighted_resident_prior_fetch tagged items cleanup (prior.size + phase.val)
      (by rw [taggedSize]; omega)]
  unfold tagged mixedBranchPrefix
  simp only [Array.append_assoc]
  rw [Array.getElem?_append_right
    (show prior.size ≤ prior.size + phase.val from by omega)]
  simp only [Nat.add_sub_cancel_left]

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Failure of the actual weighted selected-result field takes the fetched
branch into the negative source execution, preserving the original packet. -/
theorem mixed_none_execution (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (negativeForest : negativeGraph.FormulaForest) (negativeGuarded : negativeGraph.Guarded)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (negativeMatched : RowsMatch negativeGraph rows) (negativeRootsMatch : RootsMatch negativeGraph negativeRoots)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected = none)
    (state : Controller.Cost.State width 8) (rest : List (Word width))
    (position : state.pc = word width prior.size) (running : state.halted = false)
    (heap : state.heap = cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows positiveRoots) rows positiveRoots)
    (stack : state.stack = word width negativeRoots.length ::
      ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest)))
    (allocatedRoom : sourcePrefixCells rows + positiveRoots.length < 2 ^ width)
    (programRoom : (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
      negativeMatched weights b target countFits positionFits).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) negativeGraph rows negativeRoots target).size +
      2 * (n + negativeGraph.nodeCount) + 14 +
      5 * (5 * negativeGraph.roots.length + 3 * negativeGraph.childIncidences) +
      15 * (8 * negativeGraph.roots.length + 6 * negativeGraph.childIncidences + negativeGraph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
        negativeMatched weights b target countFits positionFits) state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 4 * (sourcePrefixCells rows + positiveRoots.length) + 9 +
        63 + 7 * (6 * negativeGraph.nodeCount + negativeGraph.childIncidences + negativeGraph.guardIncidences + negativeGraph.roots.length) +
        14 * (n + negativeGraph.nodeCount) + 4288 * negativeGraph.roots.length +
        2772 * negativeGraph.childIncidences + 387 * negativeGraph.guardIncidences + 13 * n + 2 ∧
      peak ≤ state.liveWords + 2 * (n + negativeGraph.nodeCount) + 146 * negativeGraph.roots.length +
        105 * negativeGraph.childIncidences + 15 * negativeGraph.guardIncidences + 2 * n + 21 ∧
      (answer = true ↔ ∃ position : Fin (zeroQueries width negativeGraph rows negativeRoots negativeMatched b target).length,
        Controller.CNF.Satisfiable (constructorFormula (controlledHeap (width := width) negativeGraph rows negativeRoots target)
          (controlledLayout (width := width) negativeGraph rows negativeRoots target)
          (ForestZeroCompile.empty (n + negativeGraph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (zeroQueries width negativeGraph rows negativeRoots negativeMatched b target)[position] n (Nat.le_add_right _ _))) ∧
      (answer = true → ∃ position : Fin (zeroQueries width negativeGraph rows negativeRoots negativeMatched b target).length,
        Controller.CNF.Satisfiable (constructorFormula (controlledHeap (width := width) negativeGraph rows negativeRoots target)
          (controlledLayout (width := width) negativeGraph rows negativeRoots target)
          (ForestZeroCompile.empty (n + negativeGraph.nodeCount)) (ForestZeroCompile.empty_coherent _)
          (zeroQueries width negativeGraph rows negativeRoots negativeMatched b target)[position] n (Nat.le_add_right _ _)) ∧
        QueryChannelWitness (controlledHeap (width := width) negativeGraph rows negativeRoots target)
          (controlledLayout (width := width) negativeGraph rows negativeRoots target)
          (zeroQueries width negativeGraph rows negativeRoots negativeMatched b target)[position] n (Nat.le_add_right _ _) final.output) := by
  let tagged := mixedBranchPrefix prior (prior.size + 5) rows positiveRoots weights b target
  let program := mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
    negativeMatched weights b target countFits positionFits
  have programEq : program = negativeResident tagged (sourcePrefixCells rows + positiveRoots.length)
      negativeGraph rows negativeRoots negativeMatched b target := by
    unfold program mixedResident
    rw [mixed_none_program prior positiveGraph rows positiveRoots weights b target countFits positionFits chosen]
  have taggedSize : tagged.size = prior.size + 5 := mixedBranchPrefix_size prior _ rows positiveRoots weights b target
  have priorRoom : prior.size + 5 < 2 ^ width := by
    have priorLe : tagged.size ≤ program.size := by
      rw [programEq]
      unfold negativeResident residentProgram
      rw [ForestZeroResident.materialize_size, coldPrefix_size, negativePrior_size]
      omega
    have fullRoom : program.size < 2 ^ width := programRoom
    omega
  obtain ⟨ready, prefixTrace, readyPC, readyRunning, readyHeap, readyStack, readyOutput,
      readyZero, readyTag, readyZero6, readyMask, readyFrame⟩ := mixed_prefix_execution program prior.size (prior.size + 5)
        rows positiveRoots weights b target state position running priorRoom
        (mixed_none_prefix_at prior positiveGraph negativeGraph rows positiveRoots negativeRoots
          negativeMatched weights b target countFits positionFits chosen)
  have readyPosition : ready.pc = word width tagged.size := by
    rw [chosen] at readyPC
    simpa only [Option.isSome_none, Bool.false_eq_true, ite_false, taggedSize] using readyPC
  obtain ⟨answer, final, lastTicks, lastPeak, lastTrace, halted, tag, lastTime, lastSpace,
      meaning, model⟩ := negative_original_cold_execution tagged negativeGraph negativeForest negativeGuarded
        rows positiveRoots negativeRoots negativeMatched negativeRootsMatch b target ready rest readyPosition
        readyRunning (readyHeap.trans heap) (readyStack.trans stack)
        readyMask
        readyZero6 allocatedRoom
        (by
          have fullRoom : program.size < 2 ^ width := programRoom
          rw [programEq] at fullRoom
          exact fullRoom) wordRoom
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have fullTrace : Execution program ready final lastTicks lastPeak := by
    simpa only [programEq] using lastTrace
  refine ⟨answer, final, 5 + lastTicks, max state.liveWords lastPeak,
    prefixTrace.append fullTrace, halted, tag, by omega, ?_, meaning, model⟩
  rw [readyLive] at lastSpace
  exact max_le (by omega) lastSpace

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestWitnessMarshal
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- A selected source incumbent takes the actual branch, emits its optimal
original-channel witness once, then removes both packets and the target word. -/
theorem mixed_selected_execution (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (positiveForest : positiveGraph.FormulaForest) (positiveGuarded : positiveGraph.Guarded)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (positiveMatched : RowsMatch positiveGraph rows) (positiveRootsMatch : RootsMatch positiveGraph positiveRoots)
    (negativeMatched : RowsMatch negativeGraph rows)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (candidate : Candidate W)
    (chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected = some candidate)
    (state : Controller.Cost.State width 8) (rest : List (Word width))
    (position : state.pc = word width prior.size) (running : state.halted = false)
    (heap : state.heap = cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows positiveRoots) rows positiveRoots)
    (stack : state.stack = word width negativeRoots.length ::
      ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest)))
    (sourceRoom : sourceAllocatedCells positiveGraph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (programRoom : (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
      negativeMatched weights b target countFits positionFits).size < 2 ^ width) :
    ∃ selected : Fin positiveGraph.roots.length, candidate.root = selected.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        positiveGraph.eval (assignmentOfSet (fullUnblocked blocked)) (positiveGraph.roots.get selected) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          positiveGraph.eval (assignmentOfSet K) (positiveGraph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
          negativeMatched weights b target countFits positionFits) state final ticks peak ∧
        ticks ≤ 18 * (buildRoots positiveGraph).count +
          ForestWitnessAccept.sourceBudget positiveGraph positiveGraph.nodeCount + 12 * n +
          4 * sourceAllocatedCells positiveGraph rows positiveRoots +
          4 * (sourcePrefixCells rows + negativeRoots.length) + 37 ∧
        peak ≤ state.liveWords + 3 * (buildRoots positiveGraph).count + 2 * n + 6 ∧
        final.heap = #[] ∧ final.stack = rest ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ state.output ∧
        final.halted = true ∧ final.reg 4 = word width 1 := by
  let computed := (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2
  let header := UniformDAGRun.packetHeaderHeap width n rows positiveRoots
  let items := selectedItems width header positiveGraph rows positiveRoots computed candidate
    countFits positionFits (prior.size + 5) 0
  let failure := prior.size + 5 + items.length + 14
  let tagged := mixedBranchPrefix prior failure rows positiveRoots weights b target
  let cleanup := positiveTargetCleanupCode width (prior.size + 5 + items.length)
    (sourceAllocatedCells positiveGraph rows positiveRoots) (sourcePrefixCells rows)
  let program := mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
    negativeMatched weights b target countFits positionFits
  have shape : mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target
      countFits positionFits = weightedResident tagged items cleanup :=
    mixed_selected_program prior positiveGraph rows positiveRoots weights b target countFits positionFits candidate chosen
  have taggedSize : tagged.size = prior.size + 5 := mixedBranchPrefix_size prior failure rows positiveRoots weights b target
  have positiveSize : (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target
      countFits positionFits).size = tagged.size + items.length + 14 := by
    rw [shape, weightedResident_size]
    simp only [cleanup, positiveTargetCleanupCode_size]
  have positiveLe : (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target
      countFits positionFits).size ≤ program.size := by
    unfold program mixedResident negativeResident ForestZeroSourcePlan.residentProgram
    rw [ForestZeroResident.materialize_size, ForestZeroSourcePlan.coldPrefix_size, negativePrior_size]
    omega
  have fullRoom : program.size < 2 ^ width := programRoom
  have priorRoom : prior.size + 5 < 2 ^ width := by rw [positiveSize, taggedSize] at positiveLe; omega
  obtain ⟨ready, prefixTrace, readyPC, readyRunning, readyHeap, readyStack, readyOutput,
      readyZero, readyTag, readyZero6, readyMask, readyFrame⟩ := mixed_prefix_execution program prior.size failure
        rows positiveRoots weights b target state position running priorRoom
        (mixed_selected_prefix_at prior positiveGraph negativeGraph rows positiveRoots negativeRoots
          negativeMatched weights b target countFits positionFits candidate chosen)
  have readyPosition : ready.pc = word width tagged.size := by
    rw [chosen] at readyPC
    simpa only [Option.isSome_some, ite_true, taggedSize] using readyPC
  have success : ready.reg 4 = word width 1 := readyTag.trans
    (selected_selector_word rows positiveRoots weights b target candidate chosen)
  have counterEntry := cleared_counter_state ready tagged.size readyPosition readyRunning readyZero
  have entryShape : RegisterWiden.widenState
      ((ForestCounter.counterState (cacheHeap width header rows positiveRoots) tagged.size
        (ready.reg 0) (ready.reg 1) (ready.reg 2)).frame
        (word width negativeRoots.length ::
          ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest))) state.output)
      ready.reg = ready := by
    rw [readyHeap, heap, readyStack, stack, readyOutput] at counterEntry
    exact counterEntry
  have itemLength : items.length = 4 * (buildRoots positiveGraph).count + 2 * n + 100 :=
    selectedItems_length header positiveGraph rows positiveRoots positiveMatched positiveRootsMatch weights b target
      candidate countFits positionFits (prior.size + 5) 0
  have helperRoom : tagged.size + (4 * (buildRoots positiveGraph).count + 2 * n + 100) + 14 < 2 ^ width := by
    rw [positiveSize, itemLength] at positiveLe
    omega
  obtain ⟨selected, rootEq, blocked, final, lastTicks, lastPeak, admissible, feasible, score,
      optimal, lastTrace, lastTime, lastSpace, finalHeap, finalStack, finalOutput, finalHalted, finalTag⟩ :=
    selected_original_positive_target_execution tagged ready.reg positiveGraph positiveForest positiveGuarded
      rows positiveRoots negativeRoots positiveMatched positiveRootsMatch weights nonnegative b target candidate
      chosen countFits positionFits (ready.reg 0) (ready.reg 1) (ready.reg 2) rest state.output
      sourceRoom packetRoom helperRoom
      readyMask
      readyZero6 success
  rw [entryShape] at lastTrace
  have helperProgram :
      weightedResident tagged
        (selectedItems width header positiveGraph rows positiveRoots computed candidate countFits positionFits tagged.size 0)
        (positiveTargetCleanupCode width (tagged.size +
          (selectedItems width header positiveGraph rows positiveRoots computed candidate countFits positionFits tagged.size 0).length)
          (sourceAllocatedCells positiveGraph rows positiveRoots) (sourcePrefixCells rows)) =
      mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target countFits positionFits := by
    rw [taggedSize]
    exact shape.symm
  rw [helperProgram] at lastTrace
  have lifted : Execution program ready final lastTicks lastPeak :=
    execution_same_fetched_prefix _ program ready final lastTicks lastPeak lastTrace
      (fun slot valid => mixed_positive_fetch prior positiveGraph negativeGraph rows positiveRoots negativeRoots
        negativeMatched weights b target countFits positionFits slot valid)
  have initialLive : state.liveWords = 9 + sourcePrefixCells rows + positiveRoots.length +
      sourcePrefixCells rows + negativeRoots.length + rest.length + state.output.length + 2 := by
    simp only [State.liveWords, heap, stack, cacheHeap_size, UniformDAGRun.packetHeaderHeap_size,
      List.length_cons, List.length_append, source_negative_packet_size]
    unfold sourcePrefixCells
    omega
  have setupSize : sourceAllocatedCells positiveGraph rows positiveRoots =
      sourcePrefixCells rows + positiveRoots.length + 2 * (buildRoots positiveGraph).count + n + 3 := by
    unfold sourceAllocatedCells
    omega
  have peakBound : lastPeak ≤ state.liveWords + 3 * (buildRoots positiveGraph).count + 2 * n + 6 := by
    rw [setupSize] at lastSpace
    rw [initialLive]
    omega
  refine ⟨selected, rootEq, blocked, final, 5 + lastTicks, max state.liveWords lastPeak,
    admissible, feasible, score, optimal, prefixTrace.append lifted, by omega,
    max_le (by omega) peakBound, finalHeap, finalStack, finalOutput, finalHalted, finalTag⟩

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def positiveModel (graph : DAG n) (b : Nat) (target : Channel n) : Prop :=
  ∃ position : Fin graph.roots.length, ∃ K : Finset (Channel n),
    Admissible b target K ∧ graph.eval (assignmentOfSet K) (graph.roots.get position) = true

def negativeModel (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (b : Nat) (target : Channel n) : Prop :=
  ∃ position : Fin (zeroQueries width graph rows roots matched b target).length,
    Controller.CNF.Satisfiable (constructorFormula (controlledHeap (width := width) graph rows roots target)
      (controlledLayout (width := width) graph rows roots target)
      (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
      (zeroQueries width graph rows roots matched b target)[position] n (Nat.le_add_right _ _))

def positiveOutput (width : Nat) (graph : DAG n) (b : Nat) (target : Channel n)
    (before after : List (Word width)) : Prop :=
  ∃ position : Fin graph.roots.length, ∃ K : Finset (Channel n),
    Admissible b target K ∧ graph.eval (assignmentOfSet K) (graph.roots.get position) = true ∧
      after = List.ofFn (fun channel : Channel n => boolWord width (decide (channel ∈ K))) ++ before

def negativeOutput (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (b : Nat) (target : Channel n) (output : List (Word width)) : Prop :=
  ∃ position : Fin (zeroQueries width graph rows roots matched b target).length,
    Controller.CNF.Satisfiable (constructorFormula (controlledHeap (width := width) graph rows roots target)
      (controlledLayout (width := width) graph rows roots target)
      (ForestZeroCompile.empty (n + graph.nodeCount)) (ForestZeroCompile.empty_coherent _)
      (zeroQueries width graph rows roots matched b target)[position] n (Nat.le_add_right _ _)) ∧
    QueryChannelWitness (controlledHeap (width := width) graph rows roots target)
      (controlledLayout (width := width) graph rows roots target)
      (zeroQueries width graph rows roots matched b target)[position] n (Nat.le_add_right _ _) output

/-- A single source-derived resident program executes the selected-result
branch and its complete continuation. Its decision is the actual register
four, and every successful branch returns the same detecting output bits. -/
theorem mixed_execution (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (positiveForest : positiveGraph.FormulaForest) (positiveGuarded : positiveGraph.Guarded)
    (negativeForest : negativeGraph.FormulaForest) (negativeGuarded : negativeGraph.Guarded)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (positiveMatched : RowsMatch positiveGraph rows) (positiveRootsMatch : RootsMatch positiveGraph positiveRoots)
    (negativeMatched : RowsMatch negativeGraph rows) (negativeRootsMatch : RootsMatch negativeGraph negativeRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (state : Controller.Cost.State width 8) (rest : List (Word width))
    (position : state.pc = word width prior.size) (running : state.halted = false)
    (heap : state.heap = cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows positiveRoots) rows positiveRoots)
    (stack : state.stack = word width negativeRoots.length ::
      ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest)))
    (sourceRoom : sourceAllocatedCells positiveGraph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (programRoom : (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
      negativeMatched weights b target countFits positionFits).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) negativeGraph rows negativeRoots target).size +
      2 * (n + negativeGraph.nodeCount) + 14 +
      5 * (5 * negativeGraph.roots.length + 3 * negativeGraph.childIncidences) +
      15 * (8 * negativeGraph.roots.length + 6 * negativeGraph.childIncidences + negativeGraph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
        negativeMatched weights b target countFits positionFits) state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤
        (18 * (buildRoots positiveGraph).count +
          ForestWitnessAccept.sourceBudget positiveGraph positiveGraph.nodeCount + 12 * n +
          4 * sourceAllocatedCells positiveGraph rows positiveRoots +
          4 * (sourcePrefixCells rows + negativeRoots.length) + 37) +
        (4 * (sourcePrefixCells rows + positiveRoots.length) + 9 +
          63 + 7 * (6 * negativeGraph.nodeCount + negativeGraph.childIncidences + negativeGraph.guardIncidences + negativeGraph.roots.length) +
          14 * (n + negativeGraph.nodeCount) + 4288 * negativeGraph.roots.length +
          2772 * negativeGraph.childIncidences + 387 * negativeGraph.guardIncidences + 13 * n + 2) ∧
      peak ≤ state.liveWords + 3 * (buildRoots positiveGraph).count + 2 * n + 6 +
        (2 * (n + negativeGraph.nodeCount) + 146 * negativeGraph.roots.length +
          105 * negativeGraph.childIncidences + 15 * negativeGraph.guardIncidences + 2 * n + 21) ∧
      (answer = true ↔ positiveModel positiveGraph b target ∨
        negativeModel width negativeGraph rows negativeRoots negativeMatched b target) ∧
      (answer = true → positiveOutput width positiveGraph b target state.output final.output ∨
        negativeOutput width negativeGraph rows negativeRoots negativeMatched b target final.output) := by
  cases chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected with
  | none =>
    have allocatedRoom : sourcePrefixCells rows + positiveRoots.length < 2 ^ width := by
      unfold sourceAllocatedCells at sourceRoom
      omega
    obtain ⟨answer, final, ticks, peak, trace, halted, tag, time, space, meaning, model⟩ :=
      mixed_none_execution prior positiveGraph negativeGraph negativeForest negativeGuarded
        rows positiveRoots negativeRoots negativeMatched negativeRootsMatch weights b target countFits positionFits
        chosen state rest position running heap stack allocatedRoom programRoom wordRoom
    have noPositive : ¬ positiveModel positiveGraph b target :=
      (indexed_none_iff positiveGraph positiveGuarded rows positiveRoots positiveMatched positiveRootsMatch
        weights nonnegative b target).mp chosen
    refine ⟨answer, final, ticks, peak, trace, halted, tag, by omega, by omega, ?_, ?_⟩
    · constructor
      · intro yes
        exact Or.inr (meaning.mp yes)
      · intro feasible
        rcases feasible with impossible | negative
        · exact False.elim (noPositive impossible)
        · exact meaning.mpr negative
    · intro yes
      exact Or.inr (model yes)
  | some candidate =>
    obtain ⟨selected, rootEq, blocked, final, ticks, peak, admissible, feasible, score, optimal,
        trace, time, space, finalHeap, finalStack, finalOutput, halted, tag⟩ :=
      mixed_selected_execution prior positiveGraph negativeGraph positiveForest positiveGuarded
        rows positiveRoots negativeRoots positiveMatched positiveRootsMatch negativeMatched weights nonnegative
        b target countFits positionFits candidate chosen state rest position running heap stack
        sourceRoom packetRoom programRoom
    have model : positiveModel positiveGraph b target := ⟨selected, fullUnblocked blocked, admissible, feasible⟩
    refine ⟨true, final, ticks, peak, trace, halted, tag, by omega, by omega, ?_, ?_⟩
    · exact ⟨fun _ => Or.inl model, fun _ => rfl⟩
    · intro _
      exact Or.inl ⟨selected, fullUnblocked blocked, admissible, feasible, finalOutput⟩

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

/-- All root filtering, packet transfer, release, and loading blocks have fixed
resident size. Source occurrences and packet words are handled by their loops. -/
def packetPreludeChunks (width entry : Nat) : List (Program width 8) :=
  [setupCode width true,
   code width (entry + 24) (entry + 35) true,
   prepareCode width true,
   reverseSaveCode width (entry + 42) (entry + 48),
   prependHeaderCode width,
   saveNegativeCountCode width,
   setupCode width false,
   code width (entry + 77) (entry + 88) false,
   saveHeapCountCode width,
   prepareCode width false,
   reverseSaveCode width (entry + 98) (entry + 104),
   prependHeaderCode width,
   releasePreparationCode,
   countedReleaseCode width (entry + 107) (entry + 111),
   #[Instruction.constant 3 (word width 0)],
   ((ForestInputMetadata.fullCode width (entry + 112)).map RegisterWiden.widenInstruction).toArray]

@[simp] theorem packetPreludeChunks_sizes (width entry : Nat) :
    (packetPreludeChunks width entry).map Array.size =
      [24,11,7,6,2,3,24,11,3,7,6,2,1,4,1,33] := by
  simp only [packetPreludeChunks, List.map_cons, List.map_nil, setupCode_size,
    code_size, prepareCode_size, reverseSaveCode_size, prependHeaderCode,
    saveNegativeCountCode_size, saveHeapCountCode_size, releasePreparationCode_size,
    countedReleaseCode_size, List.size_toArray, List.length_map, ForestInputMetadata.fullCode_length]
  rfl

def packetPrelude (prior : Program width 8) : Program width 8 :=
  ForestZeroResident.materialize prior ((packetPreludeChunks width prior.size).flatMap Array.toList)

@[simp] theorem packetPrelude_size (prior : Program width 8) :
    (packetPrelude prior).size = prior.size + 145 := by
  rw [packetPrelude, ForestZeroResident.materialize_size]
  simp only [List.length_flatMap, Array.length_toList, packetPreludeChunks_sizes]
  rfl

/-- Each chunk is fetched at the sum of the actual preceding chunk lengths,
from the resident array produced by its instruction pushes. -/
theorem materialize_chunk (prior : Program width 8) (chunks : List (Program width 8))
    (index : Fin chunks.length) :
    RawTransferLoops.CodeAt
      (ForestZeroResident.materialize prior (chunks.flatMap Array.toList))
      (prior.size + ((chunks.take index.val).map Array.size).sum) chunks[index.val] := by
  let before := (chunks.take index.val).flatMap Array.toList
  let after := (chunks.drop (index.val + 1)).flatMap Array.toList
  have split : chunks = chunks.take index.val ++ chunks[index.val] :: chunks.drop (index.val + 1) := by
    rw [← List.drop_eq_getElem_cons index.isLt]
    exact (List.take_append_drop index.val chunks).symm
  have parts : chunks.flatMap Array.toList = before ++ (chunks[index.val]).toList ++ after := by
    conv_lhs => rw [split]
    simp only [List.flatMap_append, List.flatMap_cons, before, after, List.append_assoc]
  have beforeSize : before.length = ((chunks.take index.val).map Array.size).sum := by
    simp only [before, List.length_flatMap, Array.length_toList]
  intro phase
  rw [parts, ← beforeSize]
  simpa only [Array.getElem?_toList] using
    ForestZeroResident.materialize_block prior before (chunks[index.val]).toList after
      phase.val (by simpa only [Array.length_toList] using phase.isLt)

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

theorem materialize_chunk_bound (prior : Program width 8) (chunks : List (Program width 8))
    (index : Fin chunks.length) (phase : Fin (chunks[index.val]).size) :
    prior.size + ((chunks.take index.val).map Array.size).sum + phase.val <
      (ForestZeroResident.materialize prior (chunks.flatMap Array.toList)).size := by
  have split : chunks = chunks.take index.val ++ chunks[index.val] :: chunks.drop (index.val + 1) := by
    rw [← List.drop_eq_getElem_cons index.isLt]
    exact (List.take_append_drop index.val chunks).symm
  have counts := congrArg (fun entries : List (Program width 8) => (entries.map Array.size).sum) split
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at counts
  rw [ForestZeroResident.materialize_size]
  simp only [List.length_flatMap, Array.length_toList]
  change prior.size + ((chunks.take index.val).map Array.size).sum + phase.val <
    prior.size + (chunks.map Array.size).sum
  have inside := phase.isLt
  omega

theorem packetPrelude_at (prior program : Program width 8)
    (preserved : ∀ address, address < (packetPrelude prior).size →
      program[address]? = (packetPrelude prior)[address]?)
    (index : Fin (packetPreludeChunks width prior.size).length) :
    RawTransferLoops.CodeAt program
      (prior.size + (((packetPreludeChunks width prior.size).take index.val).map Array.size).sum)
      (packetPreludeChunks width prior.size)[index.val] := by
  intro phase
  rw [preserved _ (materialize_chunk_bound prior (packetPreludeChunks width prior.size) index phase)]
  exact materialize_chunk prior (packetPreludeChunks width prior.size) index phase

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

theorem packetPrelude_blocks (prior program : Program width 8)
    (preserved : ∀ address, address < (packetPrelude prior).size →
      program[address]? = (packetPrelude prior)[address]?) :
    RawTransferLoops.CodeAt program prior.size (setupCode width true) ∧
    CodeAt program (prior.size + 24) (prior.size + 35) true ∧
    RawTransferLoops.CodeAt program (prior.size + 35) (prepareCode width true) ∧
    RawTransferLoops.CodeAt program (prior.size + 42) (reverseSaveCode width (prior.size + 42) (prior.size + 48)) ∧
    RawTransferLoops.CodeAt program (prior.size + 48) (prependHeaderCode width) ∧
    RawTransferLoops.CodeAt program (prior.size + 50) (saveNegativeCountCode width) ∧
    RawTransferLoops.CodeAt program (prior.size + 53) (setupCode width false) ∧
    CodeAt program (prior.size + 77) (prior.size + 88) false ∧
    RawTransferLoops.CodeAt program (prior.size + 88) (saveHeapCountCode width) ∧
    RawTransferLoops.CodeAt program (prior.size + 91) (prepareCode width false) ∧
    RawTransferLoops.CodeAt program (prior.size + 98) (reverseSaveCode width (prior.size + 98) (prior.size + 104)) ∧
    RawTransferLoops.CodeAt program (prior.size + 104) (prependHeaderCode width) ∧
    RawTransferLoops.CodeAt program (prior.size + 106) releasePreparationCode ∧
    RawTransferLoops.CodeAt program (prior.size + 107) (countedReleaseCode width (prior.size + 107) (prior.size + 111)) := by
  have firstSetup := packetPrelude_at prior program preserved ⟨0, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at firstSetup
  change RawTransferLoops.CodeAt program prior.size (setupCode width true) at firstSetup
  have firstFilter := packetPrelude_at prior program preserved ⟨1, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at firstFilter
  change CodeAt program (prior.size + 24) (prior.size + 35) true at firstFilter
  have firstPrepare := packetPrelude_at prior program preserved ⟨2, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at firstPrepare
  change RawTransferLoops.CodeAt program (prior.size + 35) (prepareCode width true) at firstPrepare
  have firstSave := packetPrelude_at prior program preserved ⟨3, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at firstSave
  change RawTransferLoops.CodeAt program (prior.size + 42) (reverseSaveCode width (prior.size + 42) (prior.size + 48)) at firstSave
  have firstHeader := packetPrelude_at prior program preserved ⟨4, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at firstHeader
  change RawTransferLoops.CodeAt program (prior.size + 48) (prependHeaderCode width) at firstHeader
  have metadata := packetPrelude_at prior program preserved ⟨5, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at metadata
  change RawTransferLoops.CodeAt program (prior.size + 50) (saveNegativeCountCode width) at metadata
  have secondSetup := packetPrelude_at prior program preserved ⟨6, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at secondSetup
  change RawTransferLoops.CodeAt program (prior.size + 53) (setupCode width false) at secondSetup
  have secondFilter := packetPrelude_at prior program preserved ⟨7, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at secondFilter
  change CodeAt program (prior.size + 77) (prior.size + 88) false at secondFilter
  have count := packetPrelude_at prior program preserved ⟨8, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at count
  change RawTransferLoops.CodeAt program (prior.size + 88) (saveHeapCountCode width) at count
  have secondPrepare := packetPrelude_at prior program preserved ⟨9, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at secondPrepare
  change RawTransferLoops.CodeAt program (prior.size + 91) (prepareCode width false) at secondPrepare
  have secondSave := packetPrelude_at prior program preserved ⟨10, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at secondSave
  change RawTransferLoops.CodeAt program (prior.size + 98) (reverseSaveCode width (prior.size + 98) (prior.size + 104)) at secondSave
  have secondHeader := packetPrelude_at prior program preserved ⟨11, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at secondHeader
  change RawTransferLoops.CodeAt program (prior.size + 104) (prependHeaderCode width) at secondHeader
  have releaseSetup := packetPrelude_at prior program preserved ⟨12, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at releaseSetup
  change RawTransferLoops.CodeAt program (prior.size + 106) releasePreparationCode at releaseSetup
  have release := packetPrelude_at prior program preserved ⟨13, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at release
  change RawTransferLoops.CodeAt program (prior.size + 107) (countedReleaseCode width (prior.size + 107) (prior.size + 111)) at release
  exact ⟨firstSetup, firstFilter, firstPrepare, firstSave, firstHeader, metadata, secondSetup, secondFilter, count, secondPrepare, secondSave, secondHeader, releaseSetup, release⟩

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RawTransferLoops
variable {width : Nat}

theorem packetPrelude_loader_at (prior program : Program width 8)
    (preserved : ∀ address, address < (packetPrelude prior).size →
      program[address]? = (packetPrelude prior)[address]?) :
    program[prior.size + 111]? = some (.constant 3 (word width 0)) ∧
    ForestZeroCallerWiden.WidenedBlockAt program (prior.size + 112)
      (ForestInputMetadata.fullCode width (prior.size + 112)) := by
  have clearChunk := materialize_chunk prior (packetPreludeChunks width prior.size)
    ⟨14, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at clearChunk
  change RawTransferLoops.CodeAt (packetPrelude prior) (prior.size + 111)
    #[Instruction.constant 3 (word width 0)] at clearChunk
  have loaderChunk := materialize_chunk prior (packetPreludeChunks width prior.size)
    ⟨15, by simp [packetPreludeChunks]⟩
  rw [List.map_take, packetPreludeChunks_sizes] at loaderChunk
  change RawTransferLoops.CodeAt (packetPrelude prior) (prior.size + 112)
    (((ForestInputMetadata.fullCode width (prior.size + 112)).map RegisterWiden.widenInstruction).toArray)
    at loaderChunk
  constructor
  · rw [preserved (prior.size + 111) (by rw [packetPrelude_size]; omega)]
    have actual := clearChunk ⟨0, by change 0 < 1; decide⟩
    change (packetPrelude prior)[prior.size + 111 + 0]? = some (.constant 3 (word width 0)) at actual
    simpa only [Nat.add_zero] using actual
  · intro offset within
    rw [preserved (prior.size + 112 + offset) (by
      rw [packetPrelude_size]
      rw [ForestInputMetadata.fullCode_length] at within
      omega)]
    simpa only [List.getElem?_toArray, List.getElem?_map] using
      loaderChunk ⟨offset, by simpa only [List.size_toArray, List.length_map] using within⟩

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands
variable {width n : Nat}

/-- The packet saved by classification is loaded at its own cold origin. The
resulting source cache is derived from the executed packet loader. -/
theorem projected_source_load_execution (program : Program width 8) (entry : Nat)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (state : State width 8) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (empty : state.heap = #[])
    (stack : state.stack = (inputPacket n 0 rows roots).map (word width) ++ suffix)
    (fits : entry + 34 < 2 ^ width)
    (room : (inputPacket n 0 rows roots).length ≤ 2 ^ width)
    (clearAt : program[entry]? = some (.constant 3 (word width 0)))
    (loaderAt : ForestZeroCallerWiden.WidenedBlockAt program (entry + 1)
      (ForestInputMetadata.fullCode width (entry + 1))) :
    ∃ final, Execution program state final
      (28 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length))
      state.liveWords ∧
      final.heap = cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (entry + 34) ∧ final.halted = false ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let payload := (serializedRows 5 rows roots).map (word width)
  have payloadLength : payload.length =
      6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length := by
    simpa only [payload, List.length_map] using matched_packet_length 5 graph rows roots matched rootMatches
  have words := matched_cold_input_words (width := width) graph rows roots matched rootMatches
  have packetLength := matched_input_packet_length 0 graph rows roots matched rootMatches
  obtain ⟨final, trace, heap, finalStack, output, pc, active, frame⟩ :=
    projected_packet_load_execution program entry n graph.nodeCount graph.childIncidences
      graph.guardIncidences graph.roots.length payload suffix state position running empty
      (by rw [stack, words]; rfl) payloadLength fits (by rw [payloadLength]; omega) clearAt loaderAt
  rw [payloadLength] at trace
  refine ⟨final, trace, ?_, finalStack, output, pc, active, frame⟩
  rw [← UniformDAGRun.input_packet_cache, words]
  simpa only [ForestInputMetadata.headerWords, payload, List.append_toArray] using heap

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem mixed_positive_prior_fetch (prior : Program width 8) (graph : DAG n) (rows : List Row)
    (roots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (address : Nat) (before : address < prior.size) :
    (mixedPositiveProgram prior graph rows roots weights b target countFits positionFits)[address]? = prior[address]? := by
  cases chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected with
  | none =>
    rw [mixed_none_program prior graph rows roots weights b target countFits positionFits chosen]
    unfold mixedBranchPrefix
    simp only [Array.append_assoc]
    rw [Array.getElem?_append_left before]
  | some candidate =>
    rw [mixed_selected_program prior graph rows roots weights b target countFits positionFits candidate chosen]
    rw [weighted_resident_prior_fetch _ _ _ address (by rw [mixedBranchPrefix_size]; omega)]
    unfold mixedBranchPrefix
    simp only [Array.append_assoc]
    rw [Array.getElem?_append_left before]

theorem mixed_resident_prior_fetch (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (negativeMatched : RowsMatch negativeGraph rows) (weights : Channel n → W)
    (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (address : Nat) (before : address < prior.size) :
    (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots negativeMatched
      weights b target countFits positionFits)[address]? = prior[address]? := by
  have positiveBound : prior.size ≤
      (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target countFits positionFits).size := by
    cases chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected with
    | none =>
      rw [mixed_none_program prior positiveGraph rows positiveRoots weights b target countFits positionFits chosen,
        mixedBranchPrefix_size]
      omega
    | some candidate =>
      rw [mixed_selected_program prior positiveGraph rows positiveRoots weights b target countFits positionFits candidate chosen,
        weightedResident_size, mixedBranchPrefix_size]
      omega
  rw [mixed_positive_fetch prior positiveGraph negativeGraph rows positiveRoots negativeRoots negativeMatched
    weights b target countFits positionFits address (by omega)]
  exact mixed_positive_prior_fetch prior positiveGraph rows positiveRoots weights b target
    countFits positionFits address before

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Cost.RawTransferLoops
open Controller.Cost.ForestIndexedOperands
variable {width : Nat}

def classifiedIds (rows : List Row) (roots : List Nat) (nodes : Fin rows.length → Bool)
    (healthy : Bool) : List Nat :=
  roots.filter (fun root => (if valid : root < rows.length then nodes ⟨root, valid⟩ else false) == healthy)

/-- The complete two-pass filter executes over the original evaluated packet.
Both output packets and the saved negative count are its actual classification,
with original order and duplicates retained. -/
theorem packet_prelude_execution (prior program : Program width 8)
    (preserved : ∀ address, address < (packetPrelude prior).size →
      program[address]? = (packetPrelude prior)[address]?)
    (channels : Nat) (rows : List Row) (roots : List Nat)
    (assignment : Fin channels → Bool) (nodes : Fin rows.length → Bool)
    (ids : ∀ root ∈ roots, root < rows.length)
    (state : State width 8) (position : state.pc = word width prior.size)
    (running : state.halted = false)
    (heap : state.heap = ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
    (heapFits : state.heap.size < 2 ^ width) (codeFits : prior.size + 145 < 2 ^ width) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 20 * roots.length + 12 * sourcePrefixCells rows + 4 * state.heap.size + 66 ∧
      peak ≤ state.liveWords + 2 * sourcePrefixCells rows + roots.length + 1 ∧
      final.heap = #[] ∧
      final.stack = (inputPacket channels 0 rows (classifiedIds rows roots nodes false)).map (word width) ++
        [word width (classifiedIds rows roots nodes true).length] ++
        (inputPacket channels 0 rows (classifiedIds rows roots nodes true)).map (word width) ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (prior.size + 111) ∧
      final.halted = false ∧ final.reg 0 = word width 0 := by
  obtain ⟨firstSetup, firstFilter, firstPrepare, firstSave, firstHeader, metadata,
      secondSetup, secondFilter, count, secondPrepare, secondSave, secondHeader,
      releaseSetup, release⟩ := packetPrelude_blocks prior program preserved
  have storedPrefix : PrefixStored state.heap channels rows (roots.map (word width)).length := by
    rw [heap, List.length_map]
    exact evaluation_prefix_stored channels rows roots assignment nodes
  have geometry : state.heap.size = rootStart rows + (roots.map (word width)).length + channels + rows.length := by
    rw [heap, ForestInputPrefixStored.evaluationHeap_size]
    simp only [ForestInputPrefixStored.channelHeap_size, cacheHeap_size,
      UniformDAGRun.packetHeaderHeap_size, List.length_map]
    unfold rootStart
    omega
  have rootBase : (prefixWords width channels rows roots.length).length = rootStart rows :=
    (rootStart_eq_prefix channels roots.length rows).symm
  have valueBase : (ForestInputPrefixStored.channelHeap
      (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment).size =
      rootStart rows + (roots.map (word width)).length + channels := by
    simp only [ForestInputPrefixStored.channelHeap_size, cacheHeap_size,
      UniformDAGRun.packetHeaderHeap_size, List.length_map]
    unfold rootStart
    omega
  have storedRoots : Stored state.heap (rootStart rows)
      (rootStart rows + (roots.map (word width)).length + channels) (roots.map (word width)) := by
    rw [heap]
    have actual := evaluation_roots_stored channels rows roots assignment nodes ids (by rw [← heap]; exact heapFits)
    rw [rootBase, valueBase] at actual
    exact actual
  have releaseCopy := releaseSetup ⟨0, by change 0 < 1; decide⟩
  change program[prior.size + 106 + 0]? = some (.copy 0 2) at releaseCopy
  obtain ⟨final, ticks, peak, trace, time, space, finalHeap, finalStack, finalOutput, finalPC,
      finalRunning, finalZero⟩ := two_packets_with_count_execution program
        prior.size (prior.size + 35) (prior.size + 48) (prior.size + 50)
        (prior.size + 53) (prior.size + 88) (prior.size + 91) (prior.size + 104)
        (prior.size + 106) (prior.size + 111) state channels rows (roots.map (word width))
        position running (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        heapFits geometry storedPrefix storedRoots firstSetup firstFilter firstPrepare
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using firstSave) firstHeader metadata secondSetup
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using secondFilter) count secondPrepare
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using secondSave) secondHeader
        (by simpa only [Nat.add_zero] using releaseCopy)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using release)
  have baseEq : rootStart rows + (roots.map (word width)).length + channels = sourceValueStart channels rows roots := by
    simp only [List.length_map, sourceValueStart]
  have negativeIds := selected_evaluation_roots channels rows roots assignment nodes true ids (by rw [← heap]; exact heapFits)
  have negativeWords := classified_packet_words channels rows roots assignment nodes true ids (by rw [← heap]; exact heapFits)
  have positiveWords := classified_packet_words channels rows roots assignment nodes false ids (by rw [← heap]; exact heapFits)
  have packetStack : final.stack =
      (inputPacket channels 0 rows (classifiedIds rows roots nodes false)).map (word width) ++
        [word width (classifiedIds rows roots nodes true).length] ++
        (inputPacket channels 0 rows (classifiedIds rows roots nodes true)).map (word width) ++ state.stack := by
    rw [heap] at finalStack
    dsimp only at negativeWords positiveWords
    rw [baseEq] at finalStack negativeWords positiveWords
    have countEq := congrArg List.length negativeIds
    simp only [List.length_map] at countEq
    have grouped : final.stack =
        (prefixWords width channels rows
          (selected (ForestInputPrefixStored.evaluationHeap
            (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
            (sourceValueStart channels rows roots) false (roots.map (word width))).length ++
          selected (ForestInputPrefixStored.evaluationHeap
            (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
            (sourceValueStart channels rows roots) false (roots.map (word width))) ++
        [word width (selected (ForestInputPrefixStored.evaluationHeap
          (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
          (sourceValueStart channels rows roots) true (roots.map (word width))).length] ++
        (prefixWords width channels rows
          (selected (ForestInputPrefixStored.evaluationHeap
            (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
            (sourceValueStart channels rows roots) true (roots.map (word width))).length ++
          selected (ForestInputPrefixStored.evaluationHeap
            (UniformDAGRun.packetHeaderHeap width channels rows roots) rows roots assignment nodes)
            (sourceValueStart channels rows roots) true (roots.map (word width))) ++ state.stack := by
      simpa only [List.append_assoc] using finalStack
    rw [positiveWords, negativeWords, countEq] at grouped
    simpa only [classifiedIds, List.append_assoc] using grouped
  have prefixSize : (prefixWords width channels rows roots.length).length = sourcePrefixCells rows := by
    rw [prefixWords_length]
    rfl
  rw [List.length_map, prefixSize] at time space
  exact ⟨final, ticks, peak, trace, time, space, finalHeap, packetStack, finalOutput, finalPC, finalRunning, finalZero⟩

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem mixed_positive_size_bound (prior : Program width 8) (graph : DAG n) (rows : List Row)
    (roots : List Nat) (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width) :
    (mixedPositiveProgram prior graph rows roots weights b target countFits positionFits).size ≤
      prior.size + 4 * (buildRoots graph).count + 2 * n + 119 := by
  cases chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target roots).2.selected with
  | none =>
    rw [mixed_none_program prior graph rows roots weights b target countFits positionFits chosen,
      mixedBranchPrefix_size]
    omega
  | some candidate =>
    rw [mixed_selected_program prior graph rows roots weights b target countFits positionFits candidate chosen,
      weightedResident_size, mixedBranchPrefix_size, positiveTargetCleanupCode_size,
      selectedItems_length (UniformDAGRun.packetHeaderHeap width n rows roots) graph rows roots
        matched rootMatches weights b target candidate countFits positionFits (prior.size + 5) 0]
    omega

theorem mixed_resident_size_bound (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (positiveMatched : RowsMatch positiveGraph rows) (positiveRootsMatch : RootsMatch positiveGraph positiveRoots)
    (negativeMatched : RowsMatch negativeGraph rows) (negativeForest : negativeGraph.FormulaForest)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width) :
    (mixedResident (packetPrelude prior) positiveGraph negativeGraph rows positiveRoots negativeRoots
      negativeMatched weights b target countFits positionFits).size ≤
      prior.size + 4 * (buildRoots positiveGraph).count + 2 * n +
        833 * negativeGraph.roots.length + 183 * negativeGraph.childIncidences +
        28 * negativeGraph.guardIncidences + 348 := by
  have positive := mixed_positive_size_bound (packetPrelude prior) positiveGraph rows positiveRoots
    positiveMatched positiveRootsMatch weights b target countFits positionFits
  have negative := negative_resident_size_bound
    (mixedPositiveProgram (packetPrelude prior) positiveGraph rows positiveRoots weights b target countFits positionFits)
    (sourcePrefixCells rows + positiveRoots.length) negativeGraph rows negativeRoots negativeMatched b target negativeForest
  rw [packetPrelude_size] at positive
  change (negativeResident
    (mixedPositiveProgram (packetPrelude prior) positiveGraph rows positiveRoots weights b target countFits positionFits)
    (sourcePrefixCells rows + positiveRoots.length) negativeGraph rows negativeRoots negativeMatched b target).size ≤ _
  omega

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem loaded_mixed_execution (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (positiveForest : positiveGraph.FormulaForest) (positiveGuarded : positiveGraph.Guarded)
    (negativeForest : negativeGraph.FormulaForest) (negativeGuarded : negativeGraph.Guarded)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (positiveMatched : RowsMatch positiveGraph rows) (positiveRootsMatch : RootsMatch positiveGraph positiveRoots)
    (negativeMatched : RowsMatch negativeGraph rows) (negativeRootsMatch : RootsMatch negativeGraph negativeRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (state : Controller.Cost.State width 8) (rest : List (Word width))
    (position : state.pc = word width (prior.size + 111)) (running : state.halted = false)
    (empty : state.heap = #[])
    (stack : state.stack = (inputPacket n 0 rows positiveRoots).map (word width) ++
      (word width negativeRoots.length ::
        ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest))))
    (sourceRoom : sourceAllocatedCells positiveGraph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (programRoom : (mixedResident (packetPrelude prior) positiveGraph negativeGraph rows positiveRoots negativeRoots
      negativeMatched weights b target countFits positionFits).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) negativeGraph rows negativeRoots target).size +
      2 * (n + negativeGraph.nodeCount) + 14 +
      5 * (5 * negativeGraph.roots.length + 3 * negativeGraph.childIncidences) +
      15 * (8 * negativeGraph.roots.length + 6 * negativeGraph.childIncidences + negativeGraph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (mixedResident (packetPrelude prior) positiveGraph negativeGraph rows positiveRoots negativeRoots
        negativeMatched weights b target countFits positionFits) state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 28 + 7 * (6 * positiveGraph.nodeCount + positiveGraph.childIncidences +
        positiveGraph.guardIncidences + positiveGraph.roots.length) +
        (18 * (buildRoots positiveGraph).count +
          ForestWitnessAccept.sourceBudget positiveGraph positiveGraph.nodeCount + 12 * n +
          4 * sourceAllocatedCells positiveGraph rows positiveRoots +
          4 * (sourcePrefixCells rows + negativeRoots.length) + 37) +
        (4 * (sourcePrefixCells rows + positiveRoots.length) + 9 +
          63 + 7 * (6 * negativeGraph.nodeCount + negativeGraph.childIncidences + negativeGraph.guardIncidences + negativeGraph.roots.length) +
          14 * (n + negativeGraph.nodeCount) + 4288 * negativeGraph.roots.length +
          2772 * negativeGraph.childIncidences + 387 * negativeGraph.guardIncidences + 13 * n + 2) ∧
      peak ≤ state.liveWords + 3 * (buildRoots positiveGraph).count + 2 * n + 6 +
        (2 * (n + negativeGraph.nodeCount) + 146 * negativeGraph.roots.length +
          105 * negativeGraph.childIncidences + 15 * negativeGraph.guardIncidences + 2 * n + 21) ∧
      (answer = true ↔ positiveModel positiveGraph b target ∨
        negativeModel width negativeGraph rows negativeRoots negativeMatched b target) ∧
      (answer = true → positiveOutput width positiveGraph b target state.output final.output ∨
        negativeOutput width negativeGraph rows negativeRoots negativeMatched b target final.output) := by
  let sourceProgram := packetPrelude prior
  let program := mixedResident sourceProgram positiveGraph negativeGraph rows positiveRoots negativeRoots
    negativeMatched weights b target countFits positionFits
  let suffix := word width negativeRoots.length ::
    ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest))
  have positiveLe : sourceProgram.size ≤
      (mixedPositiveProgram sourceProgram positiveGraph rows positiveRoots weights b target countFits positionFits).size := by
    cases chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected with
    | none =>
      rw [mixed_none_program sourceProgram positiveGraph rows positiveRoots weights b target countFits positionFits chosen,
        mixedBranchPrefix_size]
      omega
    | some candidate =>
      rw [mixed_selected_program sourceProgram positiveGraph rows positiveRoots weights b target countFits positionFits candidate chosen,
        weightedResident_size, mixedBranchPrefix_size]
      omega
  have sourceRoomCode : prior.size + 145 < 2 ^ width := by
    have fullRoom : program.size < 2 ^ width := programRoom
    unfold program mixedResident negativeResident ForestZeroSourcePlan.residentProgram at fullRoom
    rw [ForestZeroResident.materialize_size, ForestZeroSourcePlan.coldPrefix_size, negativePrior_size] at fullRoom
    dsimp only [sourceProgram] at positiveLe fullRoom
    rw [packetPrelude_size] at positiveLe
    omega
  have packetFits : (inputPacket n 0 rows positiveRoots).length ≤ 2 ^ width := by
    have actual := matched_input_packet_length 0 positiveGraph rows positiveRoots positiveMatched positiveRootsMatch
    obtain ⟨children, guards⟩ := matched_incidence_lengths positiveGraph rows positiveMatched
    have rootsLength : positiveRoots.length = positiveGraph.roots.length := by rw [positiveRootsMatch]; simp
    unfold sourceAllocatedCells sourcePrefixCells at sourceRoom
    rw [positiveMatched.length_eq, children, guards, rootsLength] at sourceRoom
    omega
  obtain ⟨clearAt, loaderAt⟩ := packetPrelude_loader_at prior program
    (fun address before => mixed_resident_prior_fetch sourceProgram positiveGraph negativeGraph rows
      positiveRoots negativeRoots negativeMatched weights b target countFits positionFits address before)
  obtain ⟨loaded, firstTrace, loadedHeap, loadedStack, loadedOutput, loadedPC, loadedRunning, loadedFrame⟩ :=
    projected_source_load_execution program (prior.size + 111) positiveGraph rows positiveRoots
      positiveMatched positiveRootsMatch state suffix position running empty stack
      (by omega) packetFits clearAt (by simpa only [Nat.add_assoc, Nat.reduceAdd] using loaderAt)
  have loadedPosition : loaded.pc = word width sourceProgram.size := by
    change loaded.pc = word width (packetPrelude prior).size
    rw [packetPrelude_size]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using loadedPC
  obtain ⟨answer, final, lastTicks, lastPeak, lastTrace, halted, tag, lastTime, lastSpace, meaning, model⟩ :=
    mixed_execution sourceProgram positiveGraph negativeGraph positiveForest positiveGuarded negativeForest negativeGuarded
      rows positiveRoots negativeRoots positiveMatched positiveRootsMatch negativeMatched negativeRootsMatch
      weights nonnegative b target countFits positionFits loaded rest loadedPosition loadedRunning loadedHeap
      loadedStack sourceRoom packetRoom programRoom wordRoom
  have loadedLive : loaded.liveWords ≤ state.liveWords := Execution.final_storage_le firstTrace
  refine ⟨answer, final,
    (28 + 7 * (6 * positiveGraph.nodeCount + positiveGraph.childIncidences + positiveGraph.guardIncidences + positiveGraph.roots.length)) + lastTicks,
    max state.liveWords lastPeak, firstTrace.append lastTrace, halted, tag, by omega, ?_, meaning, ?_⟩
  · exact max_le (by omega) (lastSpace.trans (by omega))
  · intro yes
    have witness := model yes
    simpa only [loadedOutput] using witness

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem evaluated_mixed_execution (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (positiveForest : positiveGraph.FormulaForest) (positiveGuarded : positiveGraph.Guarded)
    (negativeForest : negativeGraph.FormulaForest) (negativeGuarded : negativeGraph.Guarded)
    (rows : List Row) (originalRoots positiveRoots negativeRoots : List Nat)
    (assignment : Channel n → Bool) (nodes : Fin rows.length → Bool)
    (originalIds : ∀ root ∈ originalRoots, root < rows.length)
    (positiveIds : classifiedIds rows originalRoots nodes false = positiveRoots)
    (negativeIds : classifiedIds rows originalRoots nodes true = negativeRoots)
    (positiveMatched : RowsMatch positiveGraph rows) (positiveRootsMatch : RootsMatch positiveGraph positiveRoots)
    (negativeMatched : RowsMatch negativeGraph rows) (negativeRootsMatch : RootsMatch negativeGraph negativeRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (state : Controller.Cost.State width 8) (rest : List (Word width))
    (position : state.pc = word width prior.size) (running : state.halted = false)
    (heap : state.heap = ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width n rows originalRoots) rows originalRoots assignment nodes)
    (heapFits : state.heap.size < 2 ^ width)
    (stack : state.stack = word width target.val :: rest)
    (sourceRoom : sourceAllocatedCells positiveGraph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (programRoom : (mixedResident (packetPrelude prior) positiveGraph negativeGraph rows positiveRoots negativeRoots
      negativeMatched weights b target countFits positionFits).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) negativeGraph rows negativeRoots target).size +
      2 * (n + negativeGraph.nodeCount) + 14 +
      5 * (5 * negativeGraph.roots.length + 3 * negativeGraph.childIncidences) +
      15 * (8 * negativeGraph.roots.length + 6 * negativeGraph.childIncidences + negativeGraph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (mixedResident (packetPrelude prior) positiveGraph negativeGraph rows positiveRoots negativeRoots
        negativeMatched weights b target countFits positionFits) state final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ (20 * originalRoots.length + 12 * sourcePrefixCells rows + 4 * state.heap.size + 66) +
        28 + 7 * (6 * positiveGraph.nodeCount + positiveGraph.childIncidences +
        positiveGraph.guardIncidences + positiveGraph.roots.length) +
        (18 * (buildRoots positiveGraph).count +
          ForestWitnessAccept.sourceBudget positiveGraph positiveGraph.nodeCount + 12 * n +
          4 * sourceAllocatedCells positiveGraph rows positiveRoots +
          4 * (sourcePrefixCells rows + negativeRoots.length) + 37) +
        (4 * (sourcePrefixCells rows + positiveRoots.length) + 9 +
          63 + 7 * (6 * negativeGraph.nodeCount + negativeGraph.childIncidences + negativeGraph.guardIncidences + negativeGraph.roots.length) +
          14 * (n + negativeGraph.nodeCount) + 4288 * negativeGraph.roots.length +
          2772 * negativeGraph.childIncidences + 387 * negativeGraph.guardIncidences + 13 * n + 2) ∧
      peak ≤ state.liveWords + 2 * sourcePrefixCells rows + originalRoots.length + 1 + 3 * (buildRoots positiveGraph).count + 2 * n + 6 +
        (2 * (n + negativeGraph.nodeCount) + 146 * negativeGraph.roots.length +
          105 * negativeGraph.childIncidences + 15 * negativeGraph.guardIncidences + 2 * n + 21) ∧
      (answer = true ↔ positiveModel positiveGraph b target ∨
        negativeModel width negativeGraph rows negativeRoots negativeMatched b target) ∧
      (answer = true → positiveOutput width positiveGraph b target state.output final.output ∨
        negativeOutput width negativeGraph rows negativeRoots negativeMatched b target final.output) := by
  let sourceProgram := packetPrelude prior
  let program := mixedResident sourceProgram positiveGraph negativeGraph rows positiveRoots negativeRoots
    negativeMatched weights b target countFits positionFits
  have sourceRoomCode : prior.size + 145 < 2 ^ width := by
    have positiveLe : sourceProgram.size ≤
        (mixedPositiveProgram sourceProgram positiveGraph rows positiveRoots weights b target countFits positionFits).size := by
      cases chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected with
      | none =>
        rw [mixed_none_program sourceProgram positiveGraph rows positiveRoots weights b target countFits positionFits chosen,
          mixedBranchPrefix_size]
        omega
      | some candidate =>
        rw [mixed_selected_program sourceProgram positiveGraph rows positiveRoots weights b target countFits positionFits candidate chosen,
          weightedResident_size, mixedBranchPrefix_size]
        omega
    have fullRoom : program.size < 2 ^ width := programRoom
    unfold program mixedResident negativeResident ForestZeroSourcePlan.residentProgram at fullRoom
    rw [ForestZeroResident.materialize_size, ForestZeroSourcePlan.coldPrefix_size, negativePrior_size] at fullRoom
    dsimp only [sourceProgram] at positiveLe fullRoom
    rw [packetPrelude_size] at positiveLe
    omega
  obtain ⟨filtered, firstTicks, firstPeak, firstTrace, firstTime, firstSpace,
      filteredHeap, filteredStack, filteredOutput, filteredPC, filteredRunning, filteredZero⟩ :=
    packet_prelude_execution prior program
      (fun address before => mixed_resident_prior_fetch sourceProgram positiveGraph negativeGraph rows
        positiveRoots negativeRoots negativeMatched weights b target countFits positionFits address before)
      n rows originalRoots assignment nodes originalIds state position running heap heapFits sourceRoomCode
  have loadedStack : filtered.stack = (inputPacket n 0 rows positiveRoots).map (word width) ++
      (word width negativeRoots.length ::
        ((inputPacket n 0 rows negativeRoots).map (word width) ++ (word width target.val :: rest))) := by
    rw [positiveIds, negativeIds, stack] at filteredStack
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using filteredStack
  obtain ⟨answer, final, lastTicks, lastPeak, lastTrace, halted, tag, lastTime, lastSpace, meaning, model⟩ :=
    loaded_mixed_execution prior positiveGraph negativeGraph positiveForest positiveGuarded negativeForest negativeGuarded
      rows positiveRoots negativeRoots positiveMatched positiveRootsMatch negativeMatched negativeRootsMatch
      weights nonnegative b target countFits positionFits filtered rest filteredPC filteredRunning filteredHeap
      loadedStack sourceRoom packetRoom programRoom wordRoom
  have filteredLive : filtered.liveWords ≤ firstPeak := Execution.final_storage_le firstTrace
  refine ⟨answer, final, firstTicks + lastTicks, max firstPeak lastPeak,
    firstTrace.append lastTrace, halted, tag, by omega, ?_, meaning, ?_⟩
  · exact max_le (firstSpace.trans (by omega)) (lastSpace.trans (by omega))
  · intro yes
    have witness := model yes
    simpa only [filteredOutput] using witness

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost
variable {width : Nat}

theorem packetPrelude_prior_fetch (prior : Program width 8) (address : Nat)
    (before : address < prior.size) : (packetPrelude prior)[address]? = prior[address]? := by
  have contents := ForestZeroResident.materialize_contents prior
    ((packetPreludeChunks width prior.size).flatMap Array.toList)
  have cells := congrArg (fun instructions : List (Instruction width 8) => instructions[address]?) contents
  simp only [Array.getElem?_toList] at cells
  rw [List.getElem?_append_left (by simpa only [Array.length_toList] using before)] at cells
  simpa only [packetPrelude, Array.getElem?_toList] using cells

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem mixed_resident_prefix_size (prior : Program width 8) (positiveGraph negativeGraph : DAG n)
    (rows : List Row) (positiveRoots negativeRoots : List Nat)
    (negativeMatched : RowsMatch negativeGraph rows) (weights : Channel n → W)
    (b : Nat) (target : Channel n)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width) :
    prior.size ≤ (mixedResident prior positiveGraph negativeGraph rows positiveRoots negativeRoots
      negativeMatched weights b target countFits positionFits).size := by
  have positive : prior.size ≤
      (mixedPositiveProgram prior positiveGraph rows positiveRoots weights b target countFits positionFits).size := by
    cases chosen : (ForestWeightedIndexed.runAll (source n rows) weights b target positiveRoots).2.selected with
    | none =>
      rw [mixed_none_program prior positiveGraph rows positiveRoots weights b target countFits positionFits chosen,
        mixedBranchPrefix_size]
      omega
    | some candidate =>
      rw [mixed_selected_program prior positiveGraph rows positiveRoots weights b target countFits positionFits candidate chosen,
        weightedResident_size, mixedBranchPrefix_size]
      omega
  unfold mixedResident negativeResident ForestZeroSourcePlan.residentProgram
  rw [ForestZeroResident.materialize_size, ForestZeroSourcePlan.coldPrefix_size, negativePrior_size]
  omega

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.GateProgram
variable {width n : Nat}

/-- The stored node-value view uses the source row length. Its finite cast is
fixed by the checked source-to-graph correspondence. -/
def rowNodeValues (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (assignment : Channel n → Bool) : Fin rows.length → Bool :=
  fun index => graph.evalTable assignment (Fin.cast matched.length_eq index)

theorem evaluation_row_view (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (assignment : Channel n → Bool) :
    ForestInputPrefixStored.evaluationHeap (UniformDAGRun.packetHeaderHeap width n rows roots)
      rows roots assignment (graph.evalTable assignment) =
    ForestInputPrefixStored.evaluationHeap (UniformDAGRun.packetHeaderHeap width n rows roots)
      rows roots assignment (rowNodeValues graph rows matched assignment) := by
  unfold ForestInputPrefixStored.evaluationHeap ForestInputStored.withValues
  have values := List.ofFn_congr matched.length_eq.symm
    (fun index : Fin graph.nodeCount => boolWord width (graph.evalTable assignment index))
  exact congrArg (fun cells : List (Word width) =>
    ForestInputPrefixStored.channelHeap (UniformDAGRun.packetHeaderHeap width n rows roots)
      rows roots assignment ++ cells.toArray) values

def classificationPrior (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (assignment : Channel n → Bool) : Program width 8 :=
  RegisterWiden.widenProgram (UniformDAGResources.program width n rows roots assignment)

@[simp] theorem classificationPrior_size (graph : DAG n) (rows : List Row) (roots : List Nat)
    (assignment : Channel n → Bool) :
    (classificationPrior width graph rows roots assignment).size = 159 + 2 * n := by
  simp only [classificationPrior, RegisterWiden.widenProgram, Array.size_map,
    UniformDAGResources.program_size]

/-- Every evaluation instruction is fetched from the original resident prefix
inside the same eight-register program used by the packet and mixed traces. -/
theorem classification_lower_fetch (program : Program width 8) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (assignment : Channel n → Bool)
    (preserved : ∀ address, address < (classificationPrior width graph rows roots assignment).size →
      program[address]? = (classificationPrior width graph rows roots assignment)[address]?)
    (address : Nat) (before : address < 159 + 2 * n) :
    (ForestZeroCallerWiden.lowerProgram program)[address]? =
      (UniformDAGResources.program width n rows roots assignment)[address]? := by
  simp only [ForestZeroCallerWiden.lowerProgram, Array.getElem?_map]
  rw [preserved address (by simpa only [classificationPrior_size] using before)]
  simp only [classificationPrior, RegisterWiden.widenProgram, Array.getElem?_map,
    Option.map_map]
  cases found : (UniformDAGResources.program width n rows roots assignment)[address]? with
  | none => rfl
  | some instruction => simp only [Option.map_some, Function.comp_apply, ForestZeroCallerWiden.lower_widen]

theorem classification_execution (program : Program width 8) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : RootsMatch graph roots)
    (assignment : Channel n → Bool) (suffix output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (preserved : ∀ position, position < (classificationPrior width graph rows roots assignment).size →
      program[position]? = (classificationPrior width graph rows roots assignment)[position]?)
    (fits : 159 + 2 * n < 2 ^ width)
    (room : (cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots).size +
      n + graph.nodeCount ≤ 2 ^ width) :
    ∃ final ticks peak,
      Execution program
        (RegisterWiden.widenState
          ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
            ((inputPacket n 0 rows roots).map (word width) ++
              List.ofFn (fun channel => boolWord width (assignment channel)) ++ suffix) output) saved)
        final ticks peak ∧
      ticks ≤ 27 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences +
        graph.roots.length) + 2 * n + 43 * graph.nodeCount +
        18 * (graph.childIncidences + graph.guardIncidences) + 6 ∧
      peak ≤ 18 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences +
        graph.roots.length) + n + graph.nodeCount + suffix.length + output.length ∧
      final.heap = ForestInputPrefixStored.evaluationHeap
        (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots assignment
        (rowNodeValues graph rows matched assignment) ∧
      final.stack = suffix ∧ final.output = output ∧
      final.pc = word width (159 + 2 * n) ∧ final.halted = false := by
  obtain ⟨sourceBlock, channelBlock, nodeBlock⟩ := UniformDAGResources.blocks
    (width := width) (rows := rows) (roots := roots) (values := assignment)
  have sourceAt : BlockAt (ForestZeroCallerWiden.lowerProgram program) 0
      (ForestInputMetadata.fullCode width 0) := by
    intro offset bound
    rw [classification_lower_fetch program graph rows roots assignment preserved _ (by
      rw [ForestInputMetadata.fullCode_length] at bound; omega)]
    exact sourceBlock offset bound
  have channelAt : BlockAt (ForestZeroCallerWiden.lowerProgram program) 33 (InputLoad.code n) := by
    intro offset bound
    rw [classification_lower_fetch program graph rows roots assignment preserved _ (by
      rw [InputLoad.code_length] at bound; omega)]
    exact channelBlock offset bound
  have nodeAt : BlockAt (ForestZeroCallerWiden.lowerProgram program) (33 + 2 * n)
      (UniformDAGLoop.code width (33 + 2 * n) 1
        (UniformDAGTypedNode.layout (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots assignment)) := by
    intro offset bound
    rw [classification_lower_fetch program graph rows roots assignment preserved _ (by
      rw [UniformDAGLoop.code_length] at bound; omega)]
    exact nodeBlock offset bound
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, emitted, pc, running⟩ :=
    UniformDAGRun.cold_execution (ForestZeroCallerWiden.lowerProgram program) graph rows roots matched heads
      rootMatches assignment suffix output address loaded temporary 0
      (by omega) room sourceAt channelAt
      (by simpa only [Nat.zero_add, Nat.add_assoc] using nodeAt)
  refine ⟨RegisterWiden.widenState final saved, ticks, peak + 4,
    ForestZeroCallerWiden.execution program _ _ ticks peak trace running saved,
    time, by omega, ?_, stack, emitted, ?_, running⟩
  · exact heap.trans (evaluation_row_view graph rows roots matched assignment)
  · have scalar : 0 + 33 + 2 * n + 126 = 159 + 2 * n := by omega
    simpa only [RegisterWiden.widenState_pc, scalar] using pc

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.Forest
variable {n : Nat}

/-- Original occurrence positions, including repeated root IDs, identify the
families emitted by the executed value-table filter. -/
theorem classifiedIds_family (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (target : Channel n) (healthy : Bool) :
    classifiedIds rows roots (rowNodeValues graph rows matched (assignmentOfSet {target})) healthy =
      familyRootIds graph (healthyPositions graph target healthy) := by
  have rootStream : (List.finRange graph.roots.length).map
      (fun position => (graph.roots.get position).val) = roots := by
    rw [← List.ofFn_eq_map, rootMatches]
    change (List.ofFn fun position : Fin graph.roots.length => (graph.roots[position.val]).val) = _
    exact List.ofFn_getElem_eq_map graph.roots Fin.val
  unfold classifiedIds
  rw [← rootStream, List.filter_map]
  change ((List.finRange graph.roots.length).filter
    (fun position => (if valid : (graph.roots.get position).val < rows.length then
      rowNodeValues graph rows matched (assignmentOfSet {target}) ⟨(graph.roots.get position).val, valid⟩
      else false) == healthy)).map (fun position => (graph.roots.get position).val) = _
  have predicates :
      (fun position : Fin graph.roots.length =>
        (if valid : (graph.roots.get position).val < rows.length then
          rowNodeValues graph rows matched (assignmentOfSet {target}) ⟨(graph.roots.get position).val, valid⟩
          else false) == healthy) =
      (fun position => graph.eval (assignmentOfSet {target}) (graph.roots.get position) == healthy) := by
    funext position
    have valid : (graph.roots.get position).val < rows.length := by
      rw [matched.length_eq]
      exact (graph.roots.get position).isLt
    rw [dite_eq_left valid]
    simp only [rowNodeValues, DAG.evalTable_eq_eval]
    congr 2
  rw [predicates]
  rfl

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost.ForestCursorDescriptors
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def classificationInitial (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (assignment : Channel n → Bool) (target : Channel n) (rest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width) : Controller.Cost.State width 8 :=
  RegisterWiden.widenState
    ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
      ((inputPacket n 0 rows roots).map (word width) ++
        List.ofFn (fun channel => boolWord width (assignment channel)) ++ (word width target.val :: rest)) output) saved

theorem cold_mixed_execution (graph : DAG n) (b : Nat) (target : Channel n) (positiveGraph negativeGraph : DAG n)
    (positiveForest : positiveGraph.FormulaForest) (positiveGuarded : positiveGraph.Guarded)
    (negativeForest : negativeGraph.FormulaForest) (negativeGuarded : negativeGraph.Guarded)
    (rows : List Row) (originalRoots positiveRoots negativeRoots : List Nat)
    (originalMatched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows originalMatched)
    (originalRootsMatch : RootsMatch graph originalRoots)
    (positiveIds : classifiedIds rows originalRoots (rowNodeValues graph rows originalMatched (assignmentOfSet {target})) false = positiveRoots)
    (negativeIds : classifiedIds rows originalRoots (rowNodeValues graph rows originalMatched (assignmentOfSet {target})) true = negativeRoots)
    (positiveMatched : RowsMatch positiveGraph rows) (positiveRootsMatch : RootsMatch positiveGraph positiveRoots)
    (negativeMatched : RowsMatch negativeGraph rows) (negativeRootsMatch : RootsMatch negativeGraph negativeRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (countFits : (buildRoots positiveGraph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots positiveGraph).entries, entry.position < 2 ^ width)
    (rest output : List (Word width)) (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (evaluationRoom : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width n rows originalRoots) rows originalRoots
      (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))).size < 2 ^ width)
    (sourceRoom : sourceAllocatedCells positiveGraph rows positiveRoots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + negativeRoots.length < 2 ^ width)
    (programRoom : (mixedResident (packetPrelude (classificationPrior width graph rows originalRoots (assignmentOfSet {target}))) positiveGraph negativeGraph rows positiveRoots negativeRoots
      negativeMatched weights b target countFits positionFits).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) negativeGraph rows negativeRoots target).size +
      2 * (n + negativeGraph.nodeCount) + 14 +
      5 * (5 * negativeGraph.roots.length + 3 * negativeGraph.childIncidences) +
      15 * (8 * negativeGraph.roots.length + 6 * negativeGraph.childIncidences + negativeGraph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (mixedResident (packetPrelude (classificationPrior width graph rows originalRoots (assignmentOfSet {target}))) positiveGraph negativeGraph rows positiveRoots negativeRoots
        negativeMatched weights b target countFits positionFits) (classificationInitial width graph rows originalRoots (assignmentOfSet {target}) target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ (27 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        2 * n + 43 * graph.nodeCount + 18 * (graph.childIncidences + graph.guardIncidences) + 6) +
        (20 * originalRoots.length + 12 * sourcePrefixCells rows + 4 * (ForestInputPrefixStored.evaluationHeap
          (UniformDAGRun.packetHeaderHeap width n rows originalRoots) rows originalRoots
          (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))).size + 66) +
        28 + 7 * (6 * positiveGraph.nodeCount + positiveGraph.childIncidences +
        positiveGraph.guardIncidences + positiveGraph.roots.length) +
        (18 * (buildRoots positiveGraph).count +
          ForestWitnessAccept.sourceBudget positiveGraph positiveGraph.nodeCount + 12 * n +
          4 * sourceAllocatedCells positiveGraph rows positiveRoots +
          4 * (sourcePrefixCells rows + negativeRoots.length) + 37) +
        (4 * (sourcePrefixCells rows + positiveRoots.length) + 9 +
          63 + 7 * (6 * negativeGraph.nodeCount + negativeGraph.childIncidences + negativeGraph.guardIncidences + negativeGraph.roots.length) +
          14 * (n + negativeGraph.nodeCount) + 4288 * negativeGraph.roots.length +
          2772 * negativeGraph.childIncidences + 387 * negativeGraph.guardIncidences + 13 * n + 2) ∧
      peak ≤ (18 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        n + graph.nodeCount + (1 + rest.length) + output.length) + 2 * sourcePrefixCells rows + originalRoots.length + 1 + 3 * (buildRoots positiveGraph).count + 2 * n + 6 +
        (2 * (n + negativeGraph.nodeCount) + 146 * negativeGraph.roots.length +
          105 * negativeGraph.childIncidences + 15 * negativeGraph.guardIncidences + 2 * n + 21) ∧
      (answer = true ↔ positiveModel positiveGraph b target ∨
        negativeModel width negativeGraph rows negativeRoots negativeMatched b target) ∧
      (answer = true → positiveOutput width positiveGraph b target output final.output ∨
        negativeOutput width negativeGraph rows negativeRoots negativeMatched b target final.output) := by
  let assignment : Channel n → Bool := assignmentOfSet {target}
  let prior := classificationPrior width graph rows originalRoots assignment
  let program := mixedResident (packetPrelude prior) positiveGraph negativeGraph rows positiveRoots negativeRoots
    negativeMatched weights b target countFits positionFits
  have roomCode : 159 + 2 * n < 2 ^ width := by
    have included := mixed_resident_prefix_size (packetPrelude prior) positiveGraph negativeGraph rows
      positiveRoots negativeRoots negativeMatched weights b target countFits positionFits
    dsimp only [prior, assignment] at included
    rw [packetPrelude_size, classificationPrior_size] at included
    omega
  have sourceRoomEval : (cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows originalRoots)
      rows originalRoots).size + n + graph.nodeCount ≤ 2 ^ width := by
    simpa only [ForestInputPrefixStored.evaluationHeap_size, ForestInputPrefixStored.channelHeap_size] using
      Nat.le_of_lt evaluationRoom
  obtain ⟨evaluated, firstTicks, firstPeak, firstTrace, firstTime, firstSpace,
      evaluatedHeap, evaluatedStack, evaluatedOutput, evaluatedPC, evaluatedRunning⟩ :=
    classification_execution program graph rows originalRoots originalMatched heads originalRootsMatch
      assignment (word width target.val :: rest) output address loaded temporary saved
      (fun position before =>
        (mixed_resident_prior_fetch (packetPrelude prior) positiveGraph negativeGraph rows
          positiveRoots negativeRoots negativeMatched weights b target countFits positionFits position
          (by rw [packetPrelude_size]; exact Nat.lt_of_lt_of_le before (Nat.le_add_right _ _))).trans
          (packetPrelude_prior_fetch prior position before))
      roomCode sourceRoomEval
  have originalIds : ∀ root ∈ originalRoots, root < rows.length := by
    intro root member
    rw [originalRootsMatch] at member
    obtain ⟨owner, _, same⟩ := List.mem_map.mp member
    rw [← same, originalMatched.length_eq]
    exact owner.isLt
  have evaluatedRoom : evaluated.heap.size < 2 ^ width := by
    rw [evaluatedHeap, ← evaluation_row_view graph rows originalRoots originalMatched assignment]
    exact evaluationRoom
  have evaluatedPosition : evaluated.pc = word width prior.size := by
    rw [classificationPrior_size]
    exact evaluatedPC
  obtain ⟨answer, final, lastTicks, lastPeak, lastTrace, halted, tag, lastTime, lastSpace, meaning, model⟩ :=
    evaluated_mixed_execution prior positiveGraph negativeGraph positiveForest positiveGuarded negativeForest negativeGuarded
      rows originalRoots positiveRoots negativeRoots assignment (rowNodeValues graph rows originalMatched assignment)
      originalIds positiveIds negativeIds positiveMatched positiveRootsMatch negativeMatched negativeRootsMatch
      weights nonnegative b target countFits positionFits evaluated rest evaluatedPosition evaluatedRunning
      evaluatedHeap evaluatedRoom evaluatedStack sourceRoom packetRoom programRoom wordRoom
  have evaluatedLive : evaluated.liveWords ≤ firstPeak := Execution.final_storage_le firstTrace
  have evaluatedSize : evaluated.heap.size = (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width n rows originalRoots) rows originalRoots assignment
      (graph.evalTable assignment)).size := by
    rw [evaluatedHeap, ← evaluation_row_view graph rows originalRoots originalMatched assignment]
  rw [evaluatedSize] at lastTime
  dsimp only [assignment] at lastTime
  simp only [List.length_cons] at firstSpace
  refine ⟨answer, final, firstTicks + lastTicks, max firstPeak lastPeak,
    firstTrace.append lastTrace, halted, tag, by omega, ?_, meaning, ?_⟩
  · exact max_le (firstSpace.trans (by omega)) (lastSpace.trans (by omega))
  · intro yes
    have witness := model yes
    simpa only [evaluatedOutput] using witness

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorDescriptors
variable {n : Nat}

def DownBound (limit : Nat) : CursorOp n → Prop
  | .down _ position _ => position < limit
  | _ => True

theorem node_children_le_incidence (graph : DAG n) (node : Fin graph.nodeCount) :
    (graph.node node).children.length ≤ graph.childIncidences := by
  rw [DAG.childIncidences, List.sum_ofFn]
  exact Finset.single_le_sum (f := fun index : Fin graph.nodeCount => (graph.node index).children.length)
    (fun index _ => Nat.zero_le _) (Finset.mem_univ node)

theorem cursor_down_bound (graph : DAG n) (node : Fin graph.nodeCount) (route : LeafRoute) :
    ∀ operation ∈ cursorOps graph node route, DownBound graph.childIncidences operation := by
  have claim : ∀ rank : Nat, ∀ owner : Fin graph.nodeCount, owner.val = rank →
      ∀ route : LeafRoute, ∀ operation ∈ cursorOps graph owner route,
        DownBound graph.childIncidences operation := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner rankEq route
      rw [cursorOps]
      intro operation member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      cases nodeEq : graph.node owner with
      | zero => simp only [nodeEq, List.not_mem_nil] at member
      | input head =>
          simp only [nodeEq, List.mem_singleton] at member
          subst operation
          trivial
      | liveAnd first second => simp only [nodeEq, List.not_mem_nil] at member
      | disj refs =>
          simp only [nodeEq] at member
          obtain ⟨position, _, occurrence⟩ := List.mem_flatMap.mp member
          simp only [List.singleton_append, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, or_assoc] at occurrence
          rcases occurrence with rfl | childMember | rfl
          · have lengthBound := node_children_le_incidence graph owner
            simp only [nodeEq, Gate.children] at lengthBound
            exact position.isLt.trans_le lengthBound
          · exact ih (graph.childIndex owner (refs.get position)).val
              (by have earlier := graph.childIndex_lt owner (refs.get position); omega)
              (graph.childIndex owner (refs.get position)) rfl _ operation childMember
          · trivial
      | guard child labels =>
          simp only [nodeEq, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, or_assoc] at member
          rcases member with entered | rfl | childMember | rfl | exited
          · obtain ⟨position, _, same⟩ := List.mem_map.mp entered
            subst operation
            trivial
          · have lengthBound := node_children_le_incidence graph owner
            simp only [nodeEq, Gate.children, List.length_cons, List.length_nil] at lengthBound
            change 0 < graph.childIncidences
            omega
          · exact ih (graph.childIndex owner child).val
              (by have earlier := graph.childIndex_lt owner child; omega)
              (graph.childIndex owner child) rfl _ operation childMember
          · trivial
          · obtain ⟨position, _, same⟩ := List.mem_map.mp exited
            subst operation
            trivial
  exact claim node.val node rfl route

def PositionsBound (limit : Nat) (builder : Builder) : Prop :=
  ∀ entry ∈ builder.entries, entry.position < limit

theorem descriptor_step_positions (limit root : Nat) (builder : Builder)
    (bounded : PositionsBound limit builder) (operation : CursorOp n)
    (source : DownBound limit operation) : PositionsBound limit (ForestCursorDescriptors.step root builder operation) := by
  cases operation with
  | down owner position child =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | old
      · exact source
      · exact bounded entry old
  | node owner => exact bounded
  | up => exact bounded
  | enter owner position channel => exact bounded
  | leave owner position channel => exact bounded
  | leaf owner route head => exact bounded

theorem descriptor_scan_positions (limit root : Nat) (builder : Builder)
    (bounded : PositionsBound limit builder) (operations : List (CursorOp n))
    (source : ∀ operation ∈ operations, DownBound limit operation) :
    PositionsBound limit (scan root builder operations) := by
  induction operations generalizing builder with
  | nil => exact bounded
  | cons operation rest ih =>
      exact ih (ForestCursorDescriptors.step root builder operation)
        (descriptor_step_positions limit root builder bounded operation (source operation List.mem_cons_self))
        (fun later member => source later (List.mem_cons_of_mem operation member))

theorem descriptor_roots_positions (graph : DAG n) (builder : Builder)
    (bounded : PositionsBound graph.childIncidences builder) (positions : List (Fin graph.roots.length)) :
    PositionsBound graph.childIncidences (scanRoots graph builder positions) := by
  induction positions generalizing builder with
  | nil => exact bounded
  | cons position rest ih =>
      apply ih
      exact descriptor_scan_positions graph.childIncidences position.val (beginRoot builder) bounded
        (cursorOps graph (graph.roots.get position) []) (cursor_down_bound graph _ [])

theorem buildRoots_position_bound (graph : DAG n) :
    ∀ entry ∈ (buildRoots graph).entries, entry.position < graph.childIncidences := by
  exact descriptor_roots_positions graph initial (by intro entry member; cases member) _

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def healthyGraph (graph : DAG n) (target : Channel n) (healthy : Bool) : DAG n :=
  Forest.rootFamily graph (Forest.healthyPositions graph target healthy)

def healthyRootIds (graph : DAG n) (target : Channel n) (healthy : Bool) : List Nat :=
  Forest.familyRootIds graph (Forest.healthyPositions graph target healthy)

theorem original_cold_execution (graph : DAG n) (forest : graph.FormulaForest) (b : Nat) (target : Channel n)
    (rows : List Row) (originalRoots : List Nat)
    (originalMatched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows originalMatched)
    (originalRootsMatch : RootsMatch graph originalRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (countFits : (buildRoots (healthyGraph graph target false)).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots (healthyGraph graph target false)).entries, entry.position < 2 ^ width)
    (rest output : List (Word width)) (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (evaluationRoom : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width n rows originalRoots) rows originalRoots
      (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))).size < 2 ^ width)
    (sourceRoom : sourceAllocatedCells (healthyGraph graph target false) rows (healthyRootIds graph target false) < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + (healthyRootIds graph target true).length < 2 ^ width)
    (programRoom : (mixedResident (packetPrelude (classificationPrior width graph rows originalRoots (assignmentOfSet {target}))) (healthyGraph graph target false) (healthyGraph graph target true) rows (healthyRootIds graph target false) (healthyRootIds graph target true)
      (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) weights b target countFits positionFits).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) (healthyGraph graph target true) rows (healthyRootIds graph target true) target).size +
      2 * (n + (healthyGraph graph target true).nodeCount) + 14 +
      5 * (5 * (healthyGraph graph target true).roots.length + 3 * (healthyGraph graph target true).childIncidences) +
      15 * (8 * (healthyGraph graph target true).roots.length + 6 * (healthyGraph graph target true).childIncidences + (healthyGraph graph target true).guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (mixedResident (packetPrelude (classificationPrior width graph rows originalRoots (assignmentOfSet {target}))) (healthyGraph graph target false) (healthyGraph graph target true) rows (healthyRootIds graph target false) (healthyRootIds graph target true)
        (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) weights b target countFits positionFits) (classificationInitial width graph rows originalRoots (assignmentOfSet {target}) target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ (27 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        2 * n + 43 * graph.nodeCount + 18 * (graph.childIncidences + graph.guardIncidences) + 6) +
        (20 * originalRoots.length + 12 * sourcePrefixCells rows + 4 * (ForestInputPrefixStored.evaluationHeap
          (UniformDAGRun.packetHeaderHeap width n rows originalRoots) rows originalRoots
          (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))).size + 66) +
        28 + 7 * (6 * (healthyGraph graph target false).nodeCount + (healthyGraph graph target false).childIncidences +
        (healthyGraph graph target false).guardIncidences + (healthyGraph graph target false).roots.length) +
        (18 * (buildRoots (healthyGraph graph target false)).count +
          ForestWitnessAccept.sourceBudget (healthyGraph graph target false) (healthyGraph graph target false).nodeCount + 12 * n +
          4 * sourceAllocatedCells (healthyGraph graph target false) rows (healthyRootIds graph target false) +
          4 * (sourcePrefixCells rows + (healthyRootIds graph target true).length) + 37) +
        (4 * (sourcePrefixCells rows + (healthyRootIds graph target false).length) + 9 +
          63 + 7 * (6 * (healthyGraph graph target true).nodeCount + (healthyGraph graph target true).childIncidences + (healthyGraph graph target true).guardIncidences + (healthyGraph graph target true).roots.length) +
          14 * (n + (healthyGraph graph target true).nodeCount) + 4288 * (healthyGraph graph target true).roots.length +
          2772 * (healthyGraph graph target true).childIncidences + 387 * (healthyGraph graph target true).guardIncidences + 13 * n + 2) ∧
      peak ≤ (18 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        n + graph.nodeCount + (1 + rest.length) + output.length) + 2 * sourcePrefixCells rows + originalRoots.length + 1 + 3 * (buildRoots (healthyGraph graph target false)).count + 2 * n + 6 +
        (2 * (n + (healthyGraph graph target true).nodeCount) + 146 * (healthyGraph graph target true).roots.length +
          105 * (healthyGraph graph target true).childIncidences + 15 * (healthyGraph graph target true).guardIncidences + 2 * n + 21) ∧
      (answer = true ↔ positiveModel (healthyGraph graph target false) b target ∨
        negativeModel width (healthyGraph graph target true) rows (healthyRootIds graph target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) b target) ∧
      (answer = true → positiveOutput width (healthyGraph graph target false) b target output final.output ∨
        negativeOutput width (healthyGraph graph target true) rows (healthyRootIds graph target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) b target final.output) := by
  have positiveForest := Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target false)
    (Forest.healthyPositions_nodup graph target false)
  have negativeForest := Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target true)
    (Forest.healthyPositions_nodup graph target true)
  exact cold_mixed_execution graph b target (healthyGraph graph target false) (healthyGraph graph target true)
    positiveForest positiveForest.1 negativeForest negativeForest.1 rows originalRoots
    (healthyRootIds graph target false) (healthyRootIds graph target true) originalMatched heads originalRootsMatch
    (classifiedIds_family graph rows originalRoots originalMatched originalRootsMatch target false)
    (classifiedIds_family graph rows originalRoots originalMatched originalRootsMatch target true)
    (Forest.rootFamily_rows graph _ rows originalMatched) (Forest.rootFamily_rootIds graph _)
    (Forest.rootFamily_rows graph _ rows originalMatched) (Forest.rootFamily_rootIds graph _)
    weights nonnegative countFits positionFits rest output address loaded temporary saved
    evaluationRoom sourceRoom packetRoom programRoom wordRoom

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
variable {n : Nat}

theorem healthy_geometry (graph : DAG n) (target : Channel n) (healthy : Bool) :
    (healthyGraph graph target healthy).nodeCount = graph.nodeCount ∧
    (healthyGraph graph target healthy).childIncidences = graph.childIncidences ∧
    (healthyGraph graph target healthy).guardIncidences = graph.guardIncidences ∧
    (healthyGraph graph target healthy).roots.length = (Forest.healthyPositions graph target healthy).length ∧
    (healthyRootIds graph target healthy).length = (Forest.healthyPositions graph target healthy).length := by
  exact ⟨rfl, rfl, rfl, by simp only [healthyGraph, Forest.rootFamily, List.length_map],
    by simp only [healthyRootIds, Forest.familyRootIds, List.length_map]⟩

theorem actual_descriptor_count_bound (graph : DAG n) (forest : graph.FormulaForest) :
    (buildRoots graph).count ≤ 4 * (graph.roots.length + graph.childIncidences) + 2 * graph.guardIncidences := by
  have count := ForestCursorWholeProgram.descriptor_count_le_operations graph
  rw [ForestCursorWholeProgram.rootOperations_total] at count
  exact count.trans (ForestCursorCharging.all_root_budget_bound graph forest)

theorem source_prefix_size (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows) :
    sourcePrefixCells rows = 5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  unfold sourcePrefixCells
  rw [matched.length_eq, children, guards]

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem original_cold_linear_execution (graph : DAG n) (forest : graph.FormulaForest) (b : Nat) (target : Channel n)
    (rows : List Row) (originalRoots : List Nat)
    (originalMatched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows originalMatched)
    (originalRootsMatch : RootsMatch graph originalRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (countFits : (buildRoots (healthyGraph graph target false)).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots (healthyGraph graph target false)).entries, entry.position < 2 ^ width)
    (rest output : List (Word width)) (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (evaluationRoom : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width n rows originalRoots) rows originalRoots
      (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))).size < 2 ^ width)
    (sourceRoom : sourceAllocatedCells (healthyGraph graph target false) rows (healthyRootIds graph target false) < 2 ^ width)
    (packetRoom : sourcePrefixCells rows + (healthyRootIds graph target true).length < 2 ^ width)
    (programRoom : (mixedResident (packetPrelude (classificationPrior width graph rows originalRoots (assignmentOfSet {target}))) (healthyGraph graph target false) (healthyGraph graph target true) rows (healthyRootIds graph target false) (healthyRootIds graph target true)
      (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) weights b target countFits positionFits).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) (healthyGraph graph target true) rows (healthyRootIds graph target true) target).size +
      2 * (n + (healthyGraph graph target true).nodeCount) + 14 +
      5 * (5 * (healthyGraph graph target true).roots.length + 3 * (healthyGraph graph target true).childIncidences) +
      15 * (8 * (healthyGraph graph target true).roots.length + 6 * (healthyGraph graph target true).childIncidences + (healthyGraph graph target true).guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (mixedResident (packetPrelude (classificationPrior width graph rows originalRoots (assignmentOfSet {target}))) (healthyGraph graph target false) (healthyGraph graph target true) rows (healthyRootIds graph target false) (healthyRootIds graph target true)
        (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) weights b target countFits positionFits) (classificationInitial width graph rows originalRoots (assignmentOfSet {target}) target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 4721 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) + 450 ∧
      peak ≤ 169 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) +
        57 + rest.length + output.length ∧
      (answer = true ↔ positiveModel (healthyGraph graph target false) b target ∨
        negativeModel width (healthyGraph graph target true) rows (healthyRootIds graph target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) b target) ∧
      (answer = true → positiveOutput width (healthyGraph graph target false) b target output final.output ∨
        negativeOutput width (healthyGraph graph target true) rows (healthyRootIds graph target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) b target final.output) := by
  obtain ⟨answer, final, ticks, peak, trace, halted, tag, time, space, meaning, model⟩ :=
    original_cold_execution graph forest b target rows originalRoots originalMatched heads originalRootsMatch
      weights nonnegative countFits positionFits rest output address loaded temporary saved
      evaluationRoom sourceRoom packetRoom programRoom wordRoom
  have positiveGeometry := healthy_geometry graph target false
  have negativeGeometry := healthy_geometry graph target true
  have partition := Forest.healthyPositions_length_sum graph target
  have rawLength : originalRoots.length = graph.roots.length := by rw [originalRootsMatch]; simp only [List.length_map]
  have prefixSize := source_prefix_size graph rows originalMatched
  have positiveForest := Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target false)
    (Forest.healthyPositions_nodup graph target false)
  have descriptorBound := actual_descriptor_count_bound (healthyGraph graph target false) positiveForest
  have rootLengths :
      (healthyRootIds graph target false).length + (healthyRootIds graph target true).length = graph.roots.length := by
    rw [positiveGeometry.2.2.2.2, negativeGeometry.2.2.2.2]
    exact partition
  have evaluatedSize : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width n rows originalRoots) rows originalRoots
      (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))).size =
      sourcePrefixCells rows + originalRoots.length + n + graph.nodeCount := by
    simp only [ForestInputPrefixStored.evaluationHeap_size, ForestInputPrefixStored.channelHeap_size,
      cacheHeap_size, UniformDAGRun.packetHeaderHeap_size]
    unfold sourcePrefixCells
    omega
  rw [ForestWeightedCaller.sourceBudget_exact, evaluatedSize] at time
  simp only [sourceAllocatedCells] at time
  simp only [positiveGeometry.1, positiveGeometry.2.1, positiveGeometry.2.2.1,
    positiveGeometry.2.2.2.1, positiveGeometry.2.2.2.2,
    negativeGeometry.1, negativeGeometry.2.1, negativeGeometry.2.2.1,
    negativeGeometry.2.2.2.1, negativeGeometry.2.2.2.2, prefixSize, rawLength] at time space descriptorBound
  refine ⟨answer, final, ticks, peak, trace, halted, tag, by omega, by omega, meaning, model⟩

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem original_resident_linear (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots (healthyGraph graph target false)).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots (healthyGraph graph target false)).entries, entry.position < 2 ^ width) :
    (mixedResident (packetPrelude (classificationPrior width graph rows roots (assignmentOfSet {target})))
      (healthyGraph graph target false) (healthyGraph graph target true) rows
      (healthyRootIds graph target false) (healthyRootIds graph target true)
      (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows matched)
      weights b target countFits positionFits).size ≤
      833 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) + 507 := by
  have positiveForest := Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target false)
    (Forest.healthyPositions_nodup graph target false)
  have negativeForest := Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target true)
    (Forest.healthyPositions_nodup graph target true)
  have bound := mixed_resident_size_bound
    (classificationPrior width graph rows roots (assignmentOfSet {target}))
    (healthyGraph graph target false) (healthyGraph graph target true) rows
    (healthyRootIds graph target false) (healthyRootIds graph target true)
    (Forest.rootFamily_rows graph _ rows matched) (Forest.rootFamily_rootIds graph _)
    (Forest.rootFamily_rows graph _ rows matched) negativeForest weights b target countFits positionFits
  have count := actual_descriptor_count_bound (healthyGraph graph target false) positiveForest
  have positiveGeometry := healthy_geometry graph target false
  have negativeGeometry := healthy_geometry graph target true
  have partition := Forest.healthyPositions_length_sum graph target
  simp only [classificationPrior_size, positiveGeometry.1, negativeGeometry.1, positiveGeometry.2.1, positiveGeometry.2.2.1,
    positiveGeometry.2.2.2.1, negativeGeometry.2.1, negativeGeometry.2.2.1,
    negativeGeometry.2.2.2.1] at bound count
  have positiveLength := positiveGeometry.2.2.2.2
  have negativeLength := negativeGeometry.2.2.2.2
  omega

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def forestSize (graph : DAG n) : Nat :=
  n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences

def chosenMixedWidth (graph : DAG n) : Nat := Nat.log 2 (10000 * (forestSize graph + 1)) + 1

theorem chosenMixedCapacity (graph : DAG n) :
    10000 * (forestSize graph + 1) < 2 ^ chosenMixedWidth graph :=
  Nat.lt_pow_succ_log_self (by decide : 1 < 2) _

theorem original_descriptor_capacity (graph : DAG n) (forest : graph.FormulaForest) (target : Channel n) :
    (buildRoots (healthyGraph graph target false)).count < 2 ^ chosenMixedWidth graph ∧
    ∀ entry ∈ (buildRoots (healthyGraph graph target false)).entries,
      entry.position < 2 ^ chosenMixedWidth graph := by
  have cap := chosenMixedCapacity graph
  have geometry := healthy_geometry graph target false
  have positiveForest := Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target false)
    (Forest.healthyPositions_nodup graph target false)
  have count := actual_descriptor_count_bound (healthyGraph graph target false) positiveForest
  have rootCount := Forest.healthyPositions_length_le graph target false
  simp only [geometry.2.1, geometry.2.2.1, geometry.2.2.2.1] at count
  unfold forestSize at cap
  constructor
  · omega
  · intro entry member
    have bound := buildRoots_position_bound (healthyGraph graph target false) entry member
    rw [geometry.2.1] at bound
    omega

theorem original_numeric_capacity (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots (healthyGraph graph target false)).count < 2 ^ chosenMixedWidth graph)
    (positionFits : ∀ entry ∈ (buildRoots (healthyGraph graph target false)).entries,
      entry.position < 2 ^ chosenMixedWidth graph) :
    (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap (chosenMixedWidth graph) n rows roots) rows roots
      (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))).size < 2 ^ chosenMixedWidth graph ∧
    sourceAllocatedCells (healthyGraph graph target false) rows (healthyRootIds graph target false) < 2 ^ chosenMixedWidth graph ∧
    sourcePrefixCells rows + (healthyRootIds graph target true).length < 2 ^ chosenMixedWidth graph ∧
    (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows roots (assignmentOfSet {target})))
      (healthyGraph graph target false) (healthyGraph graph target true) rows
      (healthyRootIds graph target false) (healthyRootIds graph target true)
      (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows matched)
      weights b target countFits positionFits).size < 2 ^ chosenMixedWidth graph ∧
    (controlledHeap (width := chosenMixedWidth graph) (healthyGraph graph target true) rows
      (healthyRootIds graph target true) target).size +
      2 * (n + (healthyGraph graph target true).nodeCount) + 14 +
      5 * (5 * (healthyGraph graph target true).roots.length + 3 * (healthyGraph graph target true).childIncidences) +
      15 * (8 * (healthyGraph graph target true).roots.length + 6 * (healthyGraph graph target true).childIncidences +
        (healthyGraph graph target true).guardIncidences) < 2 ^ chosenMixedWidth graph := by
  have cap := chosenMixedCapacity graph
  have positiveCount := Forest.healthyPositions_length_le graph target false
  have negativeCount := Forest.healthyPositions_length_le graph target true
  have positiveGeometry := healthy_geometry graph target false
  have negativeGeometry := healthy_geometry graph target true
  have rawLength : roots.length = graph.roots.length := by rw [rootMatches]; simp only [List.length_map]
  have prefixSize := source_prefix_size graph rows matched
  have positiveForest := Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target false)
    (Forest.healthyPositions_nodup graph target false)
  have descriptors := actual_descriptor_count_bound (healthyGraph graph target false) positiveForest
  have programSize := original_resident_linear graph forest rows roots matched weights b target countFits positionFits
  have evaluationSize : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap (chosenMixedWidth graph) n rows roots) rows roots
      (assignmentOfSet {target}) (graph.evalTable (assignmentOfSet {target}))).size =
      sourcePrefixCells rows + roots.length + n + graph.nodeCount := by
    simp only [ForestInputPrefixStored.evaluationHeap_size, ForestInputPrefixStored.channelHeap_size,
      cacheHeap_size, UniformDAGRun.packetHeaderHeap_size]
    unfold sourcePrefixCells
    omega
  have controlledSize : (controlledHeap (width := chosenMixedWidth graph) (healthyGraph graph target true) rows
      (healthyRootIds graph target true) target).size =
      sourcePrefixCells rows + (healthyRootIds graph target true).length + 1 + 2 * (n + graph.nodeCount) := by
    simp only [controlledHeap, ForestZeroInitialize.reserveHeap_size, Array.size_push,
      ForestZeroSource.packetHeap_size, negativeGeometry.1]
    unfold sourcePrefixCells
    omega
  simp only [positiveGeometry.2.1, positiveGeometry.2.2.1, positiveGeometry.2.2.2.1] at descriptors
  unfold forestSize at cap
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [evaluationSize, prefixSize, rawLength]
    omega
  · unfold sourceAllocatedCells
    rw [prefixSize, positiveGeometry.2.2.2.2]
    omega
  · rw [prefixSize, negativeGeometry.2.2.2.2]
    omega
  · omega
  · rw [controlledSize, prefixSize]
    simp only [negativeGeometry.1, negativeGeometry.2.1, negativeGeometry.2.2.1,
      negativeGeometry.2.2.2.1, negativeGeometry.2.2.2.2]
    omega

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The word width and every capacity premise are computed from the original
serialized source, including every declared root occurrence. -/
theorem original_chosen_execution (graph : DAG n) (forest : graph.FormulaForest)
    (b : Nat) (target : Channel n) (rows : List Row) (originalRoots : List Nat)
    (originalMatched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows originalMatched)
    (originalRootsMatch : RootsMatch graph originalRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (rest output : List (Word (chosenMixedWidth graph)))
    (address loaded temporary : Word (chosenMixedWidth graph))
    (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {target}))) (healthyGraph graph target false) (healthyGraph graph target true) rows (healthyRootIds graph target false) (healthyRootIds graph target true)
        (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) weights b target (original_descriptor_capacity graph forest target).1 (original_descriptor_capacity graph forest target).2) (classificationInitial (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {target}) target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth graph) (if answer then 1 else 0) ∧
      ticks ≤ 4721 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) + 450 ∧
      peak ≤ 169 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) +
        57 + rest.length + output.length ∧
      (answer = true ↔ positiveModel (healthyGraph graph target false) b target ∨
        negativeModel (chosenMixedWidth graph) (healthyGraph graph target true) rows (healthyRootIds graph target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) b target) ∧
      (answer = true → positiveOutput (chosenMixedWidth graph) (healthyGraph graph target false) b target output final.output ∨
        negativeOutput (chosenMixedWidth graph) (healthyGraph graph target true) rows (healthyRootIds graph target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) b target final.output) := by
  have capacities := original_numeric_capacity graph forest rows originalRoots originalMatched
    originalRootsMatch weights b target (original_descriptor_capacity graph forest target).1
    (original_descriptor_capacity graph forest target).2
  exact original_cold_linear_execution graph forest b target rows originalRoots originalMatched heads
    originalRootsMatch weights nonnegative (original_descriptor_capacity graph forest target).1
    (original_descriptor_capacity graph forest target).2 rest output address loaded temporary saved
    capacities.1 capacities.2.1 capacities.2.2.1 capacities.2.2.2.1 capacities.2.2.2.2

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- All source decoding, recursive control frames, root-index pairs, counters,
and retained descriptors are included in the indexed state bound. Weight
arithmetic is counted separately from the bit lengths of weight values. -/
theorem original_indexed_linear (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (matched : RowsMatch graph rows) (weights : Channel n → W)
    (b : Nat) (target : Channel n) :
    (runAll (source n rows) weights b target (healthyRootIds graph target false)).2.operations ≤
      4 * forestSize graph ∧
    (runAll (source n rows) weights b target (healthyRootIds graph target false)).2.arithmetic ≤
      8 * forestSize graph ∧
    ∃ storePeak, StoreTrace weights
      (runAll (source n rows) weights b target (healthyRootIds graph target false)).1 b target
      ⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩
      (runAll (source n rows) weights b target (healthyRootIds graph target false)).2 storePeak ∧
      storePeak + sourceWords n rows + controlBudget (source n rows) graph.nodeCount +
        (6 * graph.nodeCount + 2 * graph.childIncidences + 2 * graph.guardIncidences +
          2 * (healthyGraph graph target false).roots.length + 5) +
          6 * (healthyGraph graph target false).roots.length + 7 ≤ 57 * forestSize graph + 21 := by
  have positiveForest := Forest.rootFamily_forest graph forest (Forest.healthyPositions graph target false)
    (Forest.healthyPositions_nodup graph target false)
  have matchesRows := Forest.rootFamily_rows graph (Forest.healthyPositions graph target false) rows matched
  have matchesRoots := Forest.rootFamily_rootIds graph (Forest.healthyPositions graph target false)
  have geometry := healthy_geometry graph target false
  have rootCount := Forest.healthyPositions_length_le graph target false
  have operations := runAll_operations_bound (healthyGraph graph target false) positiveForest
    rows (healthyRootIds graph target false) matchesRows matchesRoots weights b target
  have arithmetic := runAll_arithmetic_bound (healthyGraph graph target false) rows
    (healthyRootIds graph target false) matchesRows matchesRoots positiveForest weights b target
  obtain ⟨storePeak, trace, bound⟩ := indexed_store_total_bound (healthyGraph graph target false)
    positiveForest rows (healthyRootIds graph target false) matchesRows matchesRoots weights b target
  simp only [geometry.1, geometry.2.1, geometry.2.2.1, geometry.2.2.2.1] at operations arithmetic bound
  unfold forestSize
  refine ⟨by omega, by omega, storePeak, trace, ?_⟩
  simp only [geometry.2.2.2.1]
  omega

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Fetched RAM storage, the resident program, and the actual indexed
weighted state have a joint linear bound. Weight-operation counts remain
separate from their operand bit lengths and fetched RAM ticks. -/
theorem original_total_resource_execution (graph : DAG n) (forest : graph.FormulaForest)
    (b : Nat) (target : Channel n) (rows : List Row) (originalRoots : List Nat)
    (originalMatched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows originalMatched)
    (originalRootsMatch : RootsMatch graph originalRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (rest output : List (Word (chosenMixedWidth graph)))
    (address loaded temporary : Word (chosenMixedWidth graph))
    (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    ∃ answer : Bool, ∃ final ticks peak storePeak,
      Execution (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {target}))) (healthyGraph graph target false) (healthyGraph graph target true) rows (healthyRootIds graph target false) (healthyRootIds graph target true)
        (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) weights b target (original_descriptor_capacity graph forest target).1 (original_descriptor_capacity graph forest target).2) (classificationInitial (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {target}) target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth graph) (if answer then 1 else 0) ∧
      ticks ≤ 4721 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) + 450 ∧
      peak ≤ 169 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) +
        57 + rest.length + output.length ∧
      (runAll (source n rows) weights b target (healthyRootIds graph target false)).2.operations ≤ 4 * forestSize graph ∧
      (runAll (source n rows) weights b target (healthyRootIds graph target false)).2.arithmetic ≤ 8 * forestSize graph ∧
      StoreTrace weights (runAll (source n rows) weights b target (healthyRootIds graph target false)).1 b target
        ⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩
        (runAll (source n rows) weights b target (healthyRootIds graph target false)).2 storePeak ∧
      programWords (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {target})))
        (healthyGraph graph target false) (healthyGraph graph target true) rows
        (healthyRootIds graph target false) (healthyRootIds graph target true)
        (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched)
        weights b target (original_descriptor_capacity graph forest target).1
        (original_descriptor_capacity graph forest target).2) + peak +
        (storePeak + sourceWords n rows + controlBudget (source n rows) graph.nodeCount +
          (6 * graph.nodeCount + 2 * graph.childIncidences + 2 * graph.guardIncidences +
            2 * (healthyGraph graph target false).roots.length + 5) +
            6 * (healthyGraph graph target false).roots.length + 7) ≤
          3558 * forestSize graph + 2106 + rest.length + output.length ∧
      (answer = true ↔ positiveModel (healthyGraph graph target false) b target ∨
        negativeModel (chosenMixedWidth graph) (healthyGraph graph target true) rows (healthyRootIds graph target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) b target) ∧
      (answer = true → positiveOutput (chosenMixedWidth graph) (healthyGraph graph target false) b target output final.output ∨
        negativeOutput (chosenMixedWidth graph) (healthyGraph graph target true) rows (healthyRootIds graph target true) (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows originalMatched) b target final.output) := by
  obtain ⟨answer, final, ticks, peak, trace, halted, tag, time, space, meaning, model⟩ :=
    original_chosen_execution graph forest b target rows originalRoots originalMatched heads
      originalRootsMatch weights nonnegative rest output address loaded temporary saved
  obtain ⟨operations, arithmetic, storePeak, stored, storeBound⟩ :=
    original_indexed_linear graph forest rows originalMatched weights b target
  have programSize := original_resident_linear graph forest rows originalRoots originalMatched weights b target
    (original_descriptor_capacity graph forest target).1 (original_descriptor_capacity graph forest target).2
  refine ⟨answer, final, ticks, peak, storePeak, trace, halted, tag, time, space,
    operations, arithmetic, stored, ?_, meaning, model⟩
  unfold programWords
  unfold forestSize at storeBound ⊢
  omega

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestZeroResident
variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Formation records the computed instruction array, its four source-derived
fields per instruction, and their actual backing pushes. These primitive
construction calls are distinct from fetched compiler execution ticks. -/
theorem original_resident_formation (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n) :
    let resident := mixedResident
      (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows roots (assignmentOfSet {target})))
      (healthyGraph graph target false) (healthyGraph graph target true) rows
      (healthyRootIds graph target false) (healthyRootIds graph target true)
      (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows matched)
      weights b target (original_descriptor_capacity graph forest target).1
      (original_descriptor_capacity graph forest target).2
    CompilerArrayTrace.Trace resident.toList #[] resident resident.size ∧
    BackingTrace resident.toList #[] (backing resident.toList #[]) (4 * resident.size) (4 * resident.size) ∧
    CompilerArrayTrace.Trace (sourceItems n rows) #[] (source n rows) rows.length ∧
    FormationTrace ((inputPacket n 0 rows roots).map (FieldInput.natural (width := chosenMixedWidth graph)))
      ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))) (inputPacket n 0 rows roots).length ∧
    CompilerArrayTrace.Trace ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))) #[]
      ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph))).toArray
      (inputPacket n 0 rows roots).length ∧
    9 * resident.size + rows.length + 2 * (inputPacket n 0 rows roots).length + n ≤
      7520 * forestSize graph + 4600 := by
  intro resident
  have instructions := CompilerArrayTrace.empty_array resident.toList
  have fields := backing_trace resident.toList (#[] : Array (Word (chosenMixedWidth graph)))
  have size := original_resident_linear graph forest rows roots matched weights b target
    (original_descriptor_capacity graph forest target).1 (original_descriptor_capacity graph forest target).2
  have packetLength : (inputPacket n 0 rows roots).length =
      5 + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length := by
    have size := congrArg Array.size (UniformDAGRun.input_packet_cache (width := chosenMixedWidth graph) n rows roots)
    simpa only [List.size_toArray, List.length_map, cacheHeap_size,
      UniformDAGRun.packetHeaderHeap_size] using size
  have rowLength := matched.length_eq
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp only [List.length_map]
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have packetFields := formation_trace ((inputPacket n 0 rows roots).map
    (FieldInput.natural (width := chosenMixedWidth graph)))
  refine ⟨?_, ?_, source_formation n rows, ?_, ?_, ?_⟩
  · simpa only [Array.toArray_toList, Array.length_toList] using instructions
  · simpa only [Array.length_toList] using fields
  · simpa only [List.length_map, List.map_map, FieldInput.value, Function.comp_def] using packetFields
  · simpa only [List.length_map] using CompilerArrayTrace.empty_array
      ((inputPacket n 0 rows roots).map (word (chosenMixedWidth graph)))
  · change 9 * resident.size + rows.length + 2 * (inputPacket n 0 rows roots).length + n ≤ _
    change resident.size ≤ _ at size
    rw [matched.length_eq, children, guards, rootLength] at packetLength
    unfold forestSize
    omega

end Controller.Cost.ForestRootProjection

namespace Controller.Cost.ForestRootProjection
open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Source validation scans every stored child and guard occurrence. The
counter array is initialized once before the whole root stream, and the
validation work is added to the actual indexed operations. -/
theorem original_preparation_linear (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (matched : RowsMatch graph rows) (weights : Channel n → W)
    (b : Nat) (target : Channel n) :
    ∃ checks cells, SourceValidationTrace n 0 rows (sourceItems n rows) checks cells ∧
      CompilerArrayTrace.Trace (List.replicate n (0 : Nat)) #[] (Array.replicate n 0) n ∧
      checks + (runAll (source n rows) weights b target (healthyRootIds graph target false)).2.operations + n ≤
        9 * forestSize graph ∧ cells ≤ sourceWords n rows := by
  obtain ⟨checks, cells, decoded, checksBound, cellsBound⟩ := source_validation_bound graph rows matched
  have operations := (original_indexed_linear graph forest rows matched weights b target).1
  have sourceSize := sourceWords_exact graph rows matched
  refine ⟨checks, cells, decoded, initial_counter_trace n, ?_, ?_⟩
  · unfold forestSize at operations ⊢
    omega
  · omega

end Controller.Cost.ForestRootProjection
