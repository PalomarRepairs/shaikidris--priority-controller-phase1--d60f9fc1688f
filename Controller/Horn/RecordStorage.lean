module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.LabelBuffer

@[expose] public section

/-!
# Heap-held cursors for the indexed normalizer

Each retained-sign or touched-label list uses a reserved suffix buffer and a
heap header holding its cursor. Reading that header, prepending the current
label, and storing the new cursor takes four fetched instructions. Headers
allow the three lists to reuse the same register without increasing the common
eight-register machine. The complete literal-dispatch program is separate.
-/
namespace Controller.Horn.RecordStorage

open Controller.Cost Controller.Horn.LabelBuffer

/-- A heap update outside a represented buffer preserves all its entries. -/
theorem buffer_after_store {labels : List (Fin n)} {lower cursor limit : Nat}
    {heap : Array (Word width)} (stored : BufferStored labels lower cursor limit heap)
    (index : Nat) (bound : index < heap.size) (value : Word width)
    (outside : index < lower ∨ limit ≤ index) :
    BufferStored labels lower cursor limit (heap.set index value bound) := by
  refine ⟨stored.lower_le_cursor, stored.ends, by simpa using stored.fits, ?_⟩
  refine ⟨by simpa using stored.labels.fits, ?_⟩
  intro position
  have valid : cursor + position.val < heap.size := by
    have := stored.labels.fits
    have := position.isLt
    omega
  have different : index ≠ cursor + position.val := by
    have := stored.lower_le_cursor
    have := stored.ends
    have := position.isLt
    omega
  exact (Array.getElem_set_ne bound valid different).trans (stored.labels.entry position)

/-- One cursor header is separate from its reserved label cells. -/
structure HeaderStored (labels : List (Fin n)) (header lower cursor limit : Nat)
    (heap : Array (Word width)) : Prop where
  buffer : BufferStored labels lower cursor limit heap
  bound : header < heap.size
  separate : header < lower ∨ limit ≤ header
  value : heap[header]'bound = word width cursor

def code (width : Nat) : Program width 8 :=
  #[.load 4 0, .add 4 4 6, .store 4 3, .store 0 4]

@[simp] theorem code_size (width : Nat) : (code width).size = 4 := rfl

def CodeAt (destination : Program width 8) (entry : Nat) : Prop :=
  ∀ phase : Fin 4, destination[entry + phase.val]? = some (code width)[phase.val]

def loaded (state : State width 8) (cursor : Nat) : State width 8 :=
  state.advance.put 4 (word width cursor)

def afterPrepend (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) : State width 8 :=
  LabelBuffer.prependedState (loaded state cursor) labels lower cursor limit stored.buffer room label

@[simp] theorem afterPrepend_size (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) :
    (afterPrepend state labels header lower cursor limit stored room label).heap.size = state.heap.size := by
  simp [afterPrepend, LabelBuffer.prependedState, loaded, State.advance, State.put]

def finished (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) : State width 8 :=
  let middle := afterPrepend state labels header lower cursor limit stored room label
  { middle.advance with heap := (middle.heap.set header (word width (cursor - 1))
      (by simpa only [middle, afterPrepend_size] using stored.bound)) }

/-- The final cursor header and suffix buffer describe the same prepended list. -/
theorem finished_stored (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) :
    HeaderStored (label :: labels) header lower (cursor - 1) limit
      (finished state labels header lower cursor limit stored room label).heap := by
  have represented := LabelBuffer.prepend_stored labels lower cursor limit state.heap stored.buffer room label
  refine ⟨?_, by simpa [finished] using stored.bound, stored.separate, ?_⟩
  · exact buffer_after_store represented header (by simpa using stored.bound)
      (word width (cursor - 1)) stored.separate
  · simp [finished]

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

/-- The four instructions share one program and one machine state. No list
traversal or host-side cursor update substitutes for a fetched operation. -/
theorem execution (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (state : State width 8)
    (labels : List (Fin n)) (header lower cursor limit : Nat)
    (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n)
    (headerHeld : state.reg 0 = word width header)
    (labelHeld : state.reg 3 = word width label.val)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 4 < 2 ^ width) (headerFits : header < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) :
    Execution destination state
      (finished state labels header lower cursor limit stored room label)
      4 state.liveWords := by
  have entryFits : entry < 2 ^ width := by omega
  have headerValue : (state.reg 0).val = header := by
    rw [headerHeld, word_val header headerFits]
  have first : programStep destination state = some (loaded state cursor) := by
    have fetched : destination[state.pc.val]? = some (.load 4 0) := by
      rw [position, word_val entry entryFits]
      simpa [code] using present ⟨0, by decide⟩
    unfold programStep
    rw [fetched]
    change step (.load 4 0) state = _
    simp only [step, running, Bool.false_eq_true, ite_false]
    have valid : (state.reg 0).val < state.heap.size := by
      rw [headerValue]
      exact stored.bound
    simp only [headerValue, stored.bound, dite_eq_left, stored.value]
    rfl
  have loadedPosition : (loaded state cursor).pc = word width (entry + 1) := by
    simp only [loaded, State.put, State.advance, position, word_val entry entryFits]
  have blocks : LabelBuffer.PrependAt destination (entry + 1) := by
    constructor
    · simpa [code] using present ⟨1, by decide⟩
    · simpa [code, Nat.add_assoc] using present ⟨2, by decide⟩
  have preload := LabelBuffer.prepend_execution destination (entry + 1) blocks
    (loaded state cursor) labels lower cursor limit stored.buffer room label
    (by simpa [loaded, State.put, State.advance] using labelHeld)
    (by simp [loaded, State.put])
    (by simpa [loaded, State.put, State.advance] using decrement)
    loadedPosition running (by omega) cursorFits
  have middlePosition :
      (afterPrepend state labels header lower cursor limit stored room label).pc =
        word width (entry + 3) := by
    simpa [afterPrepend, Nat.add_assoc] using
      LabelBuffer.prepended_position (loaded state cursor) labels lower cursor limit
        stored.buffer room label (entry + 1) loadedPosition (by omega)
  have middleHeader :
      (afterPrepend state labels header lower cursor limit stored room label).reg 0 = word width header := by
    simpa [afterPrepend, LabelBuffer.prependedState, loaded, State.put, State.advance] using headerHeld
  have middlePointer :
      (afterPrepend state labels header lower cursor limit stored room label).reg 4 = word width (cursor - 1) := by
    simp [afterPrepend, LabelBuffer.prependedState, State.advance, State.put]
  have last : programStep destination
      (afterPrepend state labels header lower cursor limit stored room label) =
      some (finished state labels header lower cursor limit stored room label) := by
    have fetched : destination[
        (afterPrepend state labels header lower cursor limit stored room label).pc.val]? =
        some (.store 0 4) := by
      rw [middlePosition, word_val (entry + 3) (by omega)]
      simpa [code] using present ⟨3, by decide⟩
    have middleRunning :
        (afterPrepend state labels header lower cursor limit stored room label).halted = false := running
    have middleValue :
        ((afterPrepend state labels header lower cursor limit stored room label).reg 0).val = header := by
      rw [middleHeader, word_val header headerFits]
    have valid :
        ((afterPrepend state labels header lower cursor limit stored room label).reg 0).val <
          (afterPrepend state labels header lower cursor limit stored room label).heap.size := by
      rw [middleValue, afterPrepend_size]
      exact stored.bound
    unfold programStep
    rw [fetched]
    change step (.store 0 4) _ = _
    have headerBound : header < (afterPrepend state labels header lower cursor limit stored room label).heap.size := by
      simpa using stored.bound
    simp only [step, middleRunning, Bool.false_eq_true, ite_false, middleValue, headerBound, dite_eq_left, middlePointer]
    rfl
  have trace := Execution.cons first (preload.1.append
    (Execution.cons last (Execution.refl
      (finished state labels header lower cursor limit stored room label))))
  simpa [afterPrepend, finished, LabelBuffer.prependedState, loaded,
    State.put, State.advance, State.liveWords] using trace

theorem finished_position (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) (entry : Nat)
    (position : state.pc = word width entry) (capacity : entry + 4 < 2 ^ width) :
    (finished state labels header lower cursor limit stored room label).pc = word width (entry + 4) := by
  have initial : (loaded state cursor).pc = word width (entry + 1) := by
    simp only [loaded, State.put, State.advance, position,
      word_val entry (by omega : entry < 2 ^ width)]
  have middle := LabelBuffer.prepended_position (loaded state cursor) labels lower cursor limit
    stored.buffer room label (entry + 1) initial (by omega)
  change (afterPrepend state labels header lower cursor limit stored room label).advance.pc = _
  simp only [State.advance]
  rw [show (afterPrepend state labels header lower cursor limit stored room label).pc =
    word width (entry + 3) by simpa [afterPrepend, Nat.add_assoc] using middle]
  rw [word_val (entry + 3) (by omega)]

theorem finished_frame (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) :
    (∀ register : Fin 8, register ≠ 4 →
      (finished state labels header lower cursor limit stored room label).reg register = state.reg register) ∧
    (finished state labels header lower cursor limit stored room label).stack = state.stack ∧
    (finished state labels header lower cursor limit stored room label).output = state.output := by
  refine ⟨?_, rfl, rfl⟩
  intro register different
  simp [finished, afterPrepend, LabelBuffer.prependedState, loaded, State.advance, State.put, different]

/-- Exactly two cells may change: the newly occupied suffix cell and its header. -/
theorem finished_heap_frame (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) (index : Nat)
    (notHeader : header ≠ index) (notLabel : cursor - 1 ≠ index) :
    (finished state labels header lower cursor limit stored room label).heap[index]? = state.heap[index]? := by
  change ((LabelBuffer.prependHeap labels lower cursor limit state.heap stored.buffer room label).set
    header (word width (cursor - 1)) (by simpa using stored.bound))[index]? = _
  rw [Array.getElem?_set_ne _ notHeader]
  exact LabelBuffer.prepend_frame labels lower cursor limit state.heap stored.buffer room label index notLabel

/-- Updating one cursor/list pair preserves a disjoint second list. -/
theorem finished_preserves_buffer (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) (other : List (Fin m))
    (otherLower otherCursor otherLimit : Nat)
    (represented : BufferStored other otherLower otherCursor otherLimit state.heap)
    (labelOutside : cursor - 1 < otherLower ∨ otherLimit ≤ cursor - 1)
    (headerOutside : header < otherLower ∨ otherLimit ≤ header) :
    BufferStored other otherLower otherCursor otherLimit
      (finished state labels header lower cursor limit stored room label).heap := by
  have first := buffer_after_store represented (cursor - 1) (stored.buffer.prepend_bound room)
    (word width label.val) labelOutside
  have second := buffer_after_store first header (by simpa using stored.bound)
    (word width (cursor - 1)) headerOutside
  exact second

/-- Other list headers retain their cursor as well as their represented cells. -/
theorem finished_preserves_header (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) (other : List (Fin m))
    (otherHeader otherLower otherCursor otherLimit : Nat)
    (represented : HeaderStored other otherHeader otherLower otherCursor otherLimit state.heap)
    (labelOutside : cursor - 1 < otherLower ∨ otherLimit ≤ cursor - 1)
    (headerOutside : header < otherLower ∨ otherLimit ≤ header)
    (differentHeaders : header ≠ otherHeader) (differentLabel : cursor - 1 ≠ otherHeader) :
    HeaderStored other otherHeader otherLower otherCursor otherLimit
      (finished state labels header lower cursor limit stored room label).heap := by
  refine ⟨finished_preserves_buffer state labels header lower cursor limit stored room label
    other otherLower otherCursor otherLimit represented.buffer labelOutside headerOutside,
    by simpa [finished] using represented.bound, represented.separate, ?_⟩
  have unchanged := finished_heap_frame state labels header lower cursor limit stored room label
    otherHeader differentHeaders differentLabel
  have before : state.heap[otherHeader]? = some (word width otherCursor) := by
    rw [Array.getElem?_eq_getElem represented.bound, represented.value]
  have after : (finished state labels header lower cursor limit stored room label).heap[otherHeader]? =
      some (word width otherCursor) := unchanged.trans before
  rw [Array.getElem?_eq_getElem (by simpa [finished] using represented.bound)] at after
  exact Option.some.inj after

/-- Both stores are framed away from the two-polarity mark table. -/
theorem finished_preserves_marks (state : State width 8) (labels : List (Fin n))
    (header lower cursor limit : Nat) (stored : HeaderStored labels header lower cursor limit state.heap)
    (room : lower < cursor) (label : Fin n) (marks : Worklist.IndexedNormalize.Marks m)
    (markBase : Nat) (represented : MarkStorage.Stored marks markBase state.heap)
    (labelOutside : cursor - 1 < markBase ∨ markBase + 2 * m ≤ cursor - 1)
    (headerOutside : header < markBase ∨ markBase + 2 * m ≤ header) :
    MarkStorage.Stored marks markBase
      (finished state labels header lower cursor limit stored room label).heap := by
  refine ⟨by simpa [finished] using represented.fits, ?_⟩
  intro literal
  have upper := MarkStorage.address_lt markBase literal
  have lowerAddress : markBase ≤ MarkStorage.address markBase literal := by
    unfold MarkStorage.address
    omega
  have differentHeader : header ≠ MarkStorage.address markBase literal := by omega
  have differentLabel : cursor - 1 ≠ MarkStorage.address markBase literal := by omega
  have unchanged := finished_heap_frame state labels header lower cursor limit stored room label
    (MarkStorage.address markBase literal) differentHeader differentLabel
  have before : state.heap[MarkStorage.address markBase literal]? =
      some (MarkStorage.encode width (marks.read literal)) := by
    rw [Array.getElem?_eq_getElem (represented.bound literal), represented.entry literal]
  have after := unchanged.trans before
  rw [Array.getElem?_eq_getElem (by simpa [finished] using represented.bound literal)] at after
  exact Option.some.inj after

end Controller.Horn.RecordStorage
