module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.InitializeCommon
public import Controller.Horn.ResetTouched
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Reusable contiguous buffers for normalizer labels

Labels are prepended by moving a cursor backward through a reserved region.
This represents list cons in the same order as the indexed normalizer. The
region can be allocated once and reused between rows; its old contents impose
no condition when the represented list is empty. Stores preserve every other
heap cell, including a preceding mark table.
-/

namespace Controller.Horn.LabelBuffer

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

/-- The represented list occupies the suffix from `cursor` up to `limit`. -/
structure BufferStored (labels : List (Fin n)) (lower cursor limit : Nat)
    (heap : Array (Word width)) : Prop where
  lower_le_cursor : lower ≤ cursor
  ends : cursor + labels.length = limit
  fits : limit ≤ heap.size
  labels : ResetTouched.LabelsStored labels cursor heap

theorem empty_stored (heap : Array (Word width)) (lower limit : Nat)
    (ordered : lower ≤ limit) (fits : limit ≤ heap.size) :
    BufferStored ([] : List (Fin n)) lower limit limit heap := by
  refine ⟨ordered, by simp, fits, ?_⟩
  refine ⟨by simpa using fits, ?_⟩
  intro index
  exact Fin.elim0 index

theorem BufferStored.cursor_le_heap {labels : List (Fin n)}
    {lower cursor limit : Nat} {heap : Array (Word width)}
    (stored : BufferStored labels lower cursor limit heap) : cursor ≤ heap.size := by
  have := stored.ends
  have := stored.fits
  omega

theorem BufferStored.prepend_bound {labels : List (Fin n)}
    {lower cursor limit : Nat} {heap : Array (Word width)}
    (stored : BufferStored labels lower cursor limit heap) (room : lower < cursor) :
    cursor - 1 < heap.size := by
  have := stored.cursor_le_heap
  omega

/-- A declared-channel-sized buffer has room for every fresh touched label. -/
theorem room_of_fresh {labels : List (Fin n)} {lower cursor : Nat} {heap : Array (Word width)}
    (stored : BufferStored labels lower cursor (lower + n) heap)
    (distinct : labels.Nodup) (label : Fin n) (fresh : label ∉ labels) : lower < cursor := by
  have extended : (label :: labels).Nodup := List.nodup_cons.mpr ⟨fresh, distinct⟩
  have lengthBound : labels.length + 1 ≤ n := by
    simpa using extended.length_le_card
  have := stored.ends
  omega

theorem touched_length_le_channels {clause : CNF.Clause (Fin n)} {row : Row n}
    (correct : row.Correct clause) : row.touched.length ≤ n := by
  simpa using (Row.touched_nodup correct).length_le_card

def prependHeap (labels : List (Fin n)) (lower cursor limit : Nat)
    (heap : Array (Word width)) (stored : BufferStored labels lower cursor limit heap)
    (room : lower < cursor) (label : Fin n) : Array (Word width) :=
  heap.set (cursor - 1) (word width label.val) (stored.prepend_bound room)

@[simp] theorem prependHeap_size (labels : List (Fin n)) (lower cursor limit : Nat)
    (heap : Array (Word width)) (stored : BufferStored labels lower cursor limit heap)
    (room : lower < cursor) (label : Fin n) :
    (prependHeap labels lower cursor limit heap stored room label).size = heap.size := by
  simp [prependHeap]

theorem prepend_stored (labels : List (Fin n)) (lower cursor limit : Nat)
    (heap : Array (Word width)) (stored : BufferStored labels lower cursor limit heap)
    (room : lower < cursor) (label : Fin n) :
    BufferStored (label :: labels) lower (cursor - 1) limit
      (prependHeap labels lower cursor limit heap stored room label) := by
  refine ⟨by omega, ?_, by simpa only [prependHeap_size] using stored.fits, ?_⟩
  · have := stored.ends
    simp only [List.length_cons]
    omega
  · refine ⟨?_, ?_⟩
    · have := stored.labels.fits
      simp only [prependHeap_size, List.length_cons]
      omega
    · intro index
      refine Fin.cases ?_ (fun previous => ?_) index
      · change (heap.set (cursor - 1) (word width label.val) (stored.prepend_bound room))[cursor - 1]'(by
          simpa using stored.prepend_bound room) = word width label.val
        simp
      · have position : cursor - 1 + (previous.val + 1) = cursor + previous.val := by omega
        have oldBound : cursor + previous.val < heap.size := by
          have := stored.labels.fits
          have := previous.isLt
          omega
        have preserved := Array.getElem_set_ne (xs := heap) (v := word width label.val)
          (stored.prepend_bound room) oldBound (by omega : cursor - 1 ≠ cursor + previous.val)
        simpa only [prependHeap, Fin.val_succ, List.getElem_cons_succ, position] using
          preserved.trans (stored.labels.entry previous)

/-- Only the newly occupied cell changes. -/
theorem prepend_frame (labels : List (Fin n)) (lower cursor limit : Nat)
    (heap : Array (Word width)) (stored : BufferStored labels lower cursor limit heap)
    (room : lower < cursor) (label : Fin n) (index : Nat) (different : cursor - 1 ≠ index) :
    (prependHeap labels lower cursor limit heap stored room label)[index]? = heap[index]? := by
  exact Array.getElem?_set_ne (stored.prepend_bound room) different

theorem prepend_preserves_marks (labels : List (Fin n)) (lower cursor limit : Nat)
    (heap : Array (Word width)) (stored : BufferStored labels lower cursor limit heap)
    (room : lower < cursor) (label : Fin n) (marks : Marks n) (markBase : Nat)
    (marked : MarkStorage.Stored marks markBase heap) (separate : markBase + 2 * n ≤ lower) :
    MarkStorage.Stored marks markBase (prependHeap labels lower cursor limit heap stored room label) := by
  refine ⟨by simpa only [prependHeap_size] using marked.fits, ?_⟩
  intro literal
  have upper := MarkStorage.address_lt markBase literal
  have different : cursor - 1 ≠ MarkStorage.address markBase literal := by omega
  have preserved := Array.getElem_set_ne (xs := heap) (v := word width label.val)
    (stored.prepend_bound room) (marked.bound literal) different
  simpa only [prependHeap] using preserved.trans (marked.entry literal)

def prependCode (width : Nat) : Program width 8 := #[.add 4 4 6, .store 4 3]

def PrependAt (destination : Program width 8) (entry : Nat) : Prop :=
  destination[entry]? = some (.add 4 4 6) ∧ destination[entry + 1]? = some (.store 4 3)

def prependedState (state : State width 8) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : BufferStored labels lower cursor limit state.heap) (room : lower < cursor)
    (label : Fin n) : State width 8 :=
  { (state.advance.put 4 (word width (cursor - 1))).advance with
    heap := prependHeap labels lower cursor limit state.heap stored room label }

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

/-- Two fetched instructions prepend the held label: decrement its cursor, then
store the label. The strict room premise prevents pointer underflow. -/
theorem prepend_execution (destination : Program width 8) (entry : Nat)
    (present : PrependAt destination entry) (state : State width 8)
    (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : BufferStored labels lower cursor limit state.heap) (room : lower < cursor)
    (label : Fin n) (held : state.reg 3 = word width label.val)
    (points : state.reg 4 = word width cursor)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 2 < 2 ^ width) (cursorFits : cursor < 2 ^ width) :
    Execution destination state (prependedState state labels lower cursor limit stored room label)
      2 state.liveWords ∧
    BufferStored (label :: labels) lower (cursor - 1) limit
      (prependedState state labels lower cursor limit stored room label).heap := by
  have entryFits : entry < 2 ^ width := by omega
  have nextFits : entry + 1 < 2 ^ width := by omega
  have positive : 0 < cursor := by omega
  have subtract : cursor - 1 + 1 = cursor := by omega
  have arithmetic : word width ((word width cursor).val + (word width (2 ^ width - 1)).val) =
      word width (cursor - 1) := by
    have result := Initialize.word_decrement (cursor - 1) (by omega : cursor - 1 + 1 < 2 ^ width)
    simpa only [subtract] using result
  let middle := state.advance.put 4 (word width (cursor - 1))
  have middlePC : middle.pc = word width (entry + 1) := by
    simp only [middle, State.put, State.advance, position, word_val entry entryFits]
  have middleRunning : middle.halted = false := running
  have first : programStep destination state = some middle := by
    have fetched : destination[state.pc.val]? = some (.add 4 4 6) := by
      rw [position, word_val entry entryFits]
      exact present.1
    unfold programStep
    rw [fetched]
    change step (.add 4 4 6) state = _
    simp only [step, running, Bool.false_eq_true, ite_false, points, decrement, arithmetic]
    rfl
  have cellFits : cursor - 1 < 2 ^ width := by omega
  have cellBound := stored.prepend_bound room
  have second : programStep destination middle =
      some (prependedState state labels lower cursor limit stored room label) := by
    have fetched : destination[middle.pc.val]? = some (.store 4 3) := by
      rw [middlePC, word_val (entry + 1) nextFits]
      exact present.2
    unfold programStep
    rw [fetched]
    change step (.store 4 3) middle = _
    simp only [step, middleRunning, Bool.false_eq_true, ite_false]
    have pointer : (middle.reg 4).val = cursor - 1 := by
      simp only [middle, State.put, ite_true]
      exact word_val (cursor - 1) cellFits
    have value : middle.reg 3 = word width label.val := by
      simpa [middle, State.put, State.advance] using held
    have valid : (middle.reg 4).val < middle.heap.size := by
      rw [pointer]
      exact cellBound
    simp only [valid, dite_eq_left, value]
    simp only [pointer, prependedState, prependHeap, middle]
    rfl
  constructor
  · have trace := Execution.cons first (Execution.cons second
      (Execution.refl (prependedState state labels lower cursor limit stored room label)))
    simpa [middle, prependedState, State.liveWords, State.put, State.advance] using trace
  · exact prepend_stored labels lower cursor limit state.heap stored room label

theorem prepended_frame (state : State width 8) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : BufferStored labels lower cursor limit state.heap) (room : lower < cursor) (label : Fin n) :
    (∀ register : Fin 8, register ≠ 4 →
      (prependedState state labels lower cursor limit stored room label).reg register = state.reg register) ∧
    (prependedState state labels lower cursor limit stored room label).stack = state.stack ∧
    (prependedState state labels lower cursor limit stored room label).output = state.output := by
  refine ⟨?_, rfl, rfl⟩
  intro register different
  simp [prependedState, State.advance, State.put, different]

theorem prepended_position (state : State width 8) (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : BufferStored labels lower cursor limit state.heap) (room : lower < cursor) (label : Fin n)
    (entry : Nat) (position : state.pc = word width entry) (capacity : entry + 2 < 2 ^ width) :
    (prependedState state labels lower cursor limit stored room label).pc = word width (entry + 2) := by
  simp only [prependedState, State.put, State.advance, position,
    word_val entry (by omega : entry < 2 ^ width),
    word_val (entry + 1) (by omega : entry + 1 < 2 ^ width)]

theorem prepend_representable (destination : Program width 8) (state : State width 8)
    (labels : List (Fin n)) (lower cursor limit : Nat)
    (stored : BufferStored labels lower cursor limit state.heap) (room : lower < cursor) (label : Fin n)
    (represented : Representable destination state) :
    Representable destination (prependedState state labels lower cursor limit stored room label) := by
  refine ⟨represented.1, represented.2.1, ?_⟩
  simpa only [prependedState, prependHeap, Array.size_set] using represented.2.2

/-- Cache the requested capacity, allocate the region, then compute its end
cursor in register 4. The old heap end is supplied in that register. -/
def allocateCode (width entry : Nat) : Program width 8 :=
  #[.copy 3 1, .branchZero 1 (word width (entry + 5)), .allocate 2,
    .add 1 1 6, .branchZero 2 (word width (entry + 1)), .add 4 4 3]

@[simp] theorem allocateCode_size (width entry : Nat) : (allocateCode width entry).size = 6 := rfl

def AllocateAt (destination : Program width 8) (entry : Nat) : Prop :=
  ∀ phase : Fin 6,
    destination[entry + phase.val]? = some (allocateCode width entry)[phase.val]

theorem allocator_at (destination : Program width 8) (entry : Nat)
    (present : AllocateAt destination entry) : InitializeCommon.CodeAt destination (entry + 1) := by
  intro phase
  have fetched := present ⟨phase.val + 1, by have := phase.isLt; omega⟩
  have choices : phase.val = 0 ∨ phase.val = 1 ∨ phase.val = 2 ∨ phase.val = 3 := by
    have := phase.isLt
    omega
  rcases choices with equal | equal | equal | equal <;>
    simpa [allocateCode, InitializeCommon.code, equal, Nat.add_assoc] using fetched

def allocatedState (state : State width 8) (entry capacity : Nat) : State width 8 :=
  let copied := state.advance.put 3 (word width capacity)
  let allocated := InitializeCommon.configuration copied
    (state.heap ++ Array.replicate capacity (word width 0)) 0 (entry + 5)
  allocated.advance.put 4 (word width (state.heap.size + capacity))

@[simp] theorem allocatedState_heap (state : State width 8) (entry capacity : Nat) :
    (allocatedState state entry capacity).heap = state.heap ++ Array.replicate capacity (word width 0) := rfl

@[simp] theorem allocatedState_running (state : State width 8) (entry capacity : Nat) :
    (allocatedState state entry capacity).halted = false := rfl

@[simp] theorem allocatedState_pointer (state : State width 8) (entry capacity : Nat) :
    (allocatedState state entry capacity).reg 4 = word width (state.heap.size + capacity) := by
  simp [allocatedState, State.put]

@[simp] theorem allocatedState_liveWords (state : State width 8) (entry capacity : Nat) :
    (allocatedState state entry capacity).liveWords = state.liveWords + capacity := by
  simp [allocatedState, InitializeCommon.configuration, State.put, State.advance, State.liveWords]
  omega

theorem allocated_position (state : State width 8) (entry capacity : Nat)
    (fits : entry + 6 < 2 ^ width) :
    (allocatedState state entry capacity).pc = word width (entry + 6) := by
  simp only [allocatedState, InitializeCommon.configuration, State.put, State.advance,
    word_val (entry + 5) (by omega : entry + 5 < 2 ^ width)]

theorem allocate_representable (destination : Program width 8) (state : State width 8)
    (entry capacity : Nat) (represented : Representable destination state)
    (fits : state.heap.size + capacity < 2 ^ width) :
    Representable destination (allocatedState state entry capacity) := by
  refine ⟨represented.1, represented.2.1, ?_⟩
  simpa only [allocatedState_heap, Array.size_append, Array.size_replicate] using fits.le

/-- The allocated region is empty as a list, with the actual end pointer ready
for future backward stores. No condition is imposed on reused buffer contents. -/
theorem allocated_stored (state : State width 8) (entry capacity : Nat) :
    BufferStored ([] : List (Fin n)) state.heap.size (state.heap.size + capacity)
      (state.heap.size + capacity) (allocatedState state entry capacity).heap := by
  apply empty_stored
  · omega
  · simp

theorem allocated_frame (state : State width 8) (entry capacity : Nat) :
    (∀ register : Fin 8, register ≠ 1 → register ≠ 3 → register ≠ 4 →
      (allocatedState state entry capacity).reg register = state.reg register) ∧
    (allocatedState state entry capacity).stack = state.stack ∧
    (allocatedState state entry capacity).output = state.output ∧
    (∀ index : Fin state.heap.size,
      (allocatedState state entry capacity).heap[index.val]'(by simp; omega) = state.heap[index.val]) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro register counter label pointer
    simp [allocatedState, InitializeCommon.configuration, State.put, State.advance, counter, label, pointer]
  · exact Initialize.buffer_preserves state.heap capacity

/-- Allocation and cursor setup are actual instructions in the same destination
program. A caller can allocate the declared-variable capacity once and reuse it. -/
theorem allocate_execution (destination : Program width 8) (entry : Nat)
    (present : AllocateAt destination entry) (state : State width 8) (length : Nat)
    (counter : state.reg 1 = word width length) (pointer : state.reg 4 = word width state.heap.size)
    (zero : state.reg 2 = word width 0) (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 6 < 2 ^ width) (fits : state.heap.size + length < 2 ^ width) :
    Execution destination state (allocatedState state entry length)
      (4 * length + 3) (state.liveWords + length) := by
  have entryFits : entry < 2 ^ width := by omega
  have heapFits : state.heap.size < 2 ^ width := by omega
  have lengthFits : length < 2 ^ width := by omega
  let copied := state.advance.put 3 (word width length)
  let allocated := InitializeCommon.configuration copied
    (state.heap ++ Array.replicate length (word width 0)) 0 (entry + 5)
  have first : programStep destination state = some copied := by
    have fetched : destination[state.pc.val]? = some (.copy 3 1) := by
      rw [position, word_val entry entryFits]
      simpa [allocateCode] using present ⟨0, by decide⟩
    unfold programStep
    rw [fetched]
    change step (.copy 3 1) state = _
    simp only [step, running, Bool.false_eq_true, ite_false, counter]
    rfl
  have copiedCounter : copied.reg 1 = word width length := by
    simpa [copied, State.put, State.advance] using counter
  have copiedPosition : copied.pc = word width (entry + 1) := by
    simp only [copied, State.put, State.advance, position, word_val entry entryFits]
  have copiedZero : copied.reg 2 = word width 0 := by
    simpa [copied, State.put, State.advance] using zero
  have copiedDecrement : copied.reg 6 = word width (2 ^ width - 1) := by
    simpa [copied, State.put, State.advance] using decrement
  have allocation : Execution destination copied allocated (4 * length + 1) (state.liveWords + length) := by
    have trace := InitializeCommon.execution_from_state destination (entry + 1)
      (allocator_at destination entry present) copied length copiedCounter copiedPosition
      running copiedZero copiedDecrement (by omega) fits
    simpa only [Nat.add_assoc, Nat.reduceAdd, allocated, copied,
      State.put, State.advance, State.liveWords] using trace
  have last : programStep destination allocated = some (allocatedState state entry length) := by
    have fetched : destination[allocated.pc.val]? = some (.add 4 4 3) := by
      change destination[(word width (entry + 5)).val]? = _
      rw [word_val (entry + 5) (by omega)]
      simpa [allocateCode] using present ⟨5, by decide⟩
    have oldPointer : allocated.reg 4 = word width state.heap.size := by
      simpa [allocated, copied, InitializeCommon.configuration, State.put, State.advance] using pointer
    have cached : allocated.reg 3 = word width length := by
      simp [allocated, copied, InitializeCommon.configuration, State.put, State.advance]
    unfold programStep
    rw [fetched]
    change step (.add 4 4 3) allocated = _
    simp only [step, show allocated.halted = false from rfl, Bool.false_eq_true, ite_false,
      oldPointer, cached, word_val state.heap.size heapFits, word_val length lengthFits]
    rfl
  have allocatedWords : allocated.liveWords = state.liveWords + length := by
    simp [allocated, copied, InitializeCommon.configuration, State.put, State.advance, State.liveWords]
    omega
  have lastTrace : Execution destination allocated (allocatedState state entry length)
      1 (state.liveWords + length) := by
    have trace := Execution.cons last (Execution.refl (allocatedState state entry length))
    simpa only [allocatedState_liveWords, allocatedWords, Nat.zero_add, Nat.max_self] using trace
  have trace := Execution.cons first (allocation.append lastTrace)
  convert trace using 1 <;> omega

theorem allocate_with_continuation (destination : Program width 8) (entry : Nat)
    (present : AllocateAt destination entry) (state : State width 8) (length : Nat)
    (counter : state.reg 1 = word width length) (pointer : state.reg 4 = word width state.heap.size)
    (zero : state.reg 2 = word width 0) (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 6 < 2 ^ width) (fits : state.heap.size + length < 2 ^ width)
    (final : State width 8) (ticks peak : Nat)
    (continuation : Execution destination (allocatedState state entry length) final ticks peak) :
    Execution destination state final (4 * length + 3 + ticks) (max (state.liveWords + length) peak) :=
  (allocate_execution destination entry present state length counter pointer zero decrement position running capacity fits).append
    continuation

end Controller.Horn.LabelBuffer
