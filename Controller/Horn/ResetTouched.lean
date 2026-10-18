module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.MarkStorage

@[expose] public section

/-!
# Machine traversal of a touched-label buffer

The reset loop reads its labels from a contiguous heap buffer. That buffer lies
after the mark region, so resetting marks preserves every future label read.
The loop code depends only on its entry address and word width. Each iteration
loads a label, computes both polarity addresses, performs the stores, advances
the input pointer and decrements the counter. Code and data are separate.
-/

namespace Controller.Horn.ResetTouched

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize
open Controller.Horn.MarkStorage

/-- The touched list is represented by its actual channel numbers in heap words. -/
structure LabelsStored (labels : List (Fin n)) (offset : Nat)
    (heap : Array (Word width)) : Prop where
  fits : offset + labels.length ≤ heap.size
  entry : ∀ index : Fin labels.length,
    heap[offset + index.val]'(by omega) = word width (labels[index.val].val)

theorem LabelsStored.head {head : Fin n} {tail : List (Fin n)} {offset : Nat}
    {heap : Array (Word width)} (stored : LabelsStored (head :: tail) offset heap) :
    heap[offset]'(by have := stored.fits; simp only [List.length_cons] at this; omega) =
      word width head.val := by
  simpa using stored.entry 0

theorem LabelsStored.tail {head : Fin n} {tail : List (Fin n)} {offset : Nat}
    {heap : Array (Word width)} (stored : LabelsStored (head :: tail) offset heap) :
    LabelsStored tail (offset + 1) heap := by
  refine ⟨by have := stored.fits; simp only [List.length_cons] at this; omega, ?_⟩
  intro index
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using stored.entry index.succ

/-- A mark store cannot change a later touched-list region. -/
theorem LabelsStored.after_store {labels : List (Fin n)} {offset markBase : Nat}
    {heap : Array (Word width)} {marks : Marks n}
    (stored : LabelsStored labels offset heap) (marked : Stored marks markBase heap)
    (separate : markBase + 2 * n ≤ offset) (literal : CNF.Literal (Fin n)) (value : Bool) :
    LabelsStored labels offset
      (heap.set (address markBase literal) (encode width value) (marked.bound literal)) := by
  refine ⟨by simpa only [Array.size_set] using stored.fits, ?_⟩
  intro index
  have valid : offset + index.val < heap.size := by have := stored.fits; have := index.isLt; omega
  have frame := store_preserves_outside marked literal value ⟨offset + index.val, valid⟩
    (Or.inr (by change markBase + 2 * n ≤ offset + index.val; omega))
  exact frame.trans (stored.entry index)

/-- The two actual cell updates for one label. -/
def clearHeap (marks : Marks n) (offset : Nat) (heap : Array (Word width))
    (stored : Stored marks offset heap) (label : Fin n) : Array (Word width) :=
  let first := heap.set (address offset (label, true)) (encode width false) (stored.bound (label, true))
  first.set (address offset (label, false)) (encode width false)
    (by simpa only [first, Array.size_set] using stored.bound (label, false))

@[simp] theorem clearHeap_size (marks : Marks n) (offset : Nat) (heap : Array (Word width))
    (stored : Stored marks offset heap) (label : Fin n) :
    (clearHeap marks offset heap stored label).size = heap.size := by
  simp [clearHeap]

theorem clearHeap_stored (marks : Marks n) (offset : Nat) (heap : Array (Word width))
    (stored : Stored marks offset heap) (label : Fin n) :
    Stored (Marks.clear [label] marks) offset (clearHeap marks offset heap stored label) := by
  have result := (stored.write (label, true) false).write (label, false) false
  simpa only [clearHeap, write_pair_false, Marks.clear] using result

theorem clearHeap_labels (marks : Marks n) (markBase : Nat) (heap : Array (Word width))
    (marked : Stored marks markBase heap) (label : Fin n)
    (labels : List (Fin n)) (offset : Nat) (stored : LabelsStored labels offset heap)
    (separate : markBase + 2 * n ≤ offset) :
    LabelsStored labels offset (clearHeap marks markBase heap marked label) := by
  have first := stored.after_store marked separate (label, true) false
  have second := first.after_store (marked.write (label, true) false) separate (label, false) false
  exact second

/-- Every cell outside the mark table is preserved, including unused buffer cells. -/
def Frame (n base : Nat) (before after : Array (Word width)) : Prop :=
  ∀ index : Nat, (index < base ∨ base + 2 * n ≤ index) → after[index]? = before[index]?

theorem Frame.refl (n base : Nat) (heap : Array (Word width)) : Frame n base heap heap := by
  intro _ _
  rfl

theorem Frame.trans {before middle after : Array (Word width)}
    (first : Frame n base before middle) (second : Frame n base middle after) :
    Frame n base before after := by
  intro index outside
  exact (second index outside).trans (first index outside)

theorem clearHeap_frame (marks : Marks n) (base : Nat) (heap : Array (Word width))
    (stored : Stored marks base heap) (label : Fin n) :
    Frame n base heap (clearHeap marks base heap stored label) := by
  intro index outside
  have positiveLower : base ≤ address base (label, true) := by unfold address; omega
  have negativeLower : base ≤ address base (label, false) := by unfold address; omega
  have positiveUpper := address_lt base (label, true)
  have negativeUpper := address_lt base (label, false)
  have positiveNe : address base (label, true) ≠ index := by omega
  have negativeNe : address base (label, false) ≠ index := by omega
  simp [clearHeap, positiveNe, negativeNe]

/-- Pointer, count, zero, label scratch, address scratch, one, decrement, base. -/
def configuration (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor : Nat) : State width 8 where
  reg := fun register => word width <| match register.val with
    | 0 => pointer
    | 1 => remaining
    | 2 => 0
    | 3 => labelScratch
    | 4 => addressScratch
    | 5 => 1
    | 6 => 2 ^ width - 1
    | 7 => base
    | _ => 0
  heap := heap
  stack := []
  output := []
  pc := word width cursor
  halted := false

/-- The block is relocatable; both branch targets use the same entry address. -/
def code (width entry : Nat) : Program width 8 :=
  #[.branchZero 1 (word width (entry + 10)), .load 3 0,
    .add 4 3 3, .add 4 4 7, .store 4 2, .add 4 4 5, .store 4 2,
    .add 0 0 5, .add 1 1 6, .branchZero 2 (word width entry)]

@[simp] theorem code_size (width entry : Nat) : (code width entry).size = 10 := rfl

/-- A destination contains the actual reset instructions at its chosen entry. -/
def CodeAt (destination : Program width 8) (entry : Nat) : Prop :=
  ∀ index : Fin 10,
    destination[entry + index.val]? = some (code width entry)[index.val]

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem add_words (left right : Nat) (leftFits : left < 2 ^ width)
    (rightFits : right < 2 ^ width) :
    word width ((word width left).val + (word width right).val) = word width (left + right) := by
  rw [word_val left leftFits, word_val right rightFits]

@[simp] theorem configuration_running (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor : Nat) :
    (configuration heap pointer remaining base labelScratch addressScratch cursor).halted = false := rfl

@[simp] theorem configuration_heap (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor : Nat) :
    (configuration heap pointer remaining base labelScratch addressScratch cursor).heap = heap := rfl

@[simp] theorem configuration_liveWords (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor : Nat) :
    (configuration heap pointer remaining base labelScratch addressScratch cursor).liveWords = 9 + heap.size := by
  simp [configuration, State.liveWords]
  omega

theorem configuration_advance (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor : Nat) (fits : cursor < 2 ^ width) :
    (configuration heap pointer remaining base labelScratch addressScratch cursor).advance =
      configuration heap pointer remaining base labelScratch addressScratch (cursor + 1) := by
  unfold State.advance configuration
  rw [word_val cursor fits]

private theorem register_cases (register : Fin 8) :
    register.val = 0 ∨ register.val = 1 ∨ register.val = 2 ∨ register.val = 3 ∨
      register.val = 4 ∨ register.val = 5 ∨ register.val = 6 ∨ register.val = 7 := by
  have := register.isLt
  omega

theorem put_pointer (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor next : Nat) :
    (configuration heap pointer remaining base labelScratch addressScratch cursor).put 0 (word width next) =
      configuration heap next remaining base labelScratch addressScratch cursor := by
  unfold State.put configuration
  congr 1
  funext register
  rcases register_cases register with h | h | h | h | h | h | h | h <;>
    simp [h, Fin.ext_iff]

theorem put_counter (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor next : Nat) :
    (configuration heap pointer remaining base labelScratch addressScratch cursor).put 1 (word width next) =
      configuration heap pointer next base labelScratch addressScratch cursor := by
  unfold State.put configuration
  congr 1
  funext register
  rcases register_cases register with h | h | h | h | h | h | h | h <;>
    simp [h, Fin.ext_iff]

theorem put_label (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor next : Nat) :
    (configuration heap pointer remaining base labelScratch addressScratch cursor).put 3 (word width next) =
      configuration heap pointer remaining base next addressScratch cursor := by
  unfold State.put configuration
  congr 1
  funext register
  rcases register_cases register with h | h | h | h | h | h | h | h <;>
    simp [h, Fin.ext_iff]

theorem put_address (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch cursor next : Nat) :
    (configuration heap pointer remaining base labelScratch addressScratch cursor).put 4 (word width next) =
      configuration heap pointer remaining base labelScratch next cursor := by
  unfold State.put configuration
  congr 1
  funext register
  rcases register_cases register with h | h | h | h | h | h | h | h <;>
    simp [h, Fin.ext_iff]

theorem configured_fetch (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch : Nat) (phase : Fin 10)
    (capacity : entry + 10 < 2 ^ width) :
    destination[(configuration heap pointer remaining base labelScratch addressScratch
      (entry + phase.val)).pc.val]? = some (code width entry)[phase.val] := by
  change destination[(word width (entry + phase.val)).val]? = _
  rw [word_val (entry + phase.val) (by have := phase.isLt; omega)]
  exact present phase

/-- The zero-count branch jumps directly to the continuation, before any read. -/
theorem zero_transition (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (heap : Array (Word width))
    (pointer base labelScratch addressScratch : Nat) (capacity : entry + 10 < 2 ^ width) :
    programStep destination (configuration heap pointer 0 base labelScratch addressScratch entry) =
      some (configuration heap pointer 0 base labelScratch addressScratch (entry + 10)) := by
  have fetched := configured_fetch destination entry present heap pointer 0 base labelScratch addressScratch
    ⟨0, by decide⟩ capacity
  simp only [Nat.add_zero] at fetched
  unfold programStep
  rw [fetched]
  change step (.branchZero 1 (word width (entry + 10)))
    (configuration heap pointer 0 base labelScratch addressScratch entry) = _
  simp [step, configuration, State.advance, word]

theorem zero_execution (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (heap : Array (Word width))
    (pointer base labelScratch addressScratch : Nat) (capacity : entry + 10 < 2 ^ width) :
    Execution destination (configuration heap pointer 0 base labelScratch addressScratch entry)
      (configuration heap pointer 0 base labelScratch addressScratch (entry + 10))
      1 (9 + heap.size) := by
  have trace := Execution.cons
    (zero_transition destination entry present heap pointer base labelScratch addressScratch capacity)
    (Execution.refl (configuration heap pointer 0 base labelScratch addressScratch (entry + 10)))
  simpa only [configuration_liveWords, Nat.zero_add, Nat.max_self] using trace

private theorem step_at (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (heap : Array (Word width))
    (pointer remaining base labelScratch addressScratch : Nat) (phase : Fin 10)
    (capacity : entry + 10 < 2 ^ width) :
    programStep destination (configuration heap pointer remaining base labelScratch addressScratch
      (entry + phase.val)) =
    step (code width entry)[phase.val] (configuration heap pointer remaining base labelScratch
      addressScratch (entry + phase.val)) := by
  unfold programStep
  rw [configured_fetch destination entry present heap pointer remaining base labelScratch addressScratch phase capacity]
  rfl

/-- One iteration consists of ten fetched instructions, including both address
computations. Its label is loaded from the given buffer, not from code. -/
theorem iteration (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (heap : Array (Word width))
    (marks : Marks n) (base pointer labelScratch addressScratch : Nat)
    (marked : Stored marks base heap) (head : Fin n) (tail : List (Fin n))
    (labels : LabelsStored (head :: tail) pointer heap)
    (capacity : entry + 10 < 2 ^ width) (heapFits : heap.size < 2 ^ width) :
    Execution destination (configuration heap pointer (tail.length + 1) base labelScratch addressScratch entry)
      (configuration (clearHeap marks base heap marked head) (pointer + 1) tail.length base
        head.val (address base (head, false)) entry) 10 (9 + heap.size) := by
  have pointerBound : pointer < heap.size := by have := labels.fits; simp only [List.length_cons] at this; omega
  have pointerFits : pointer < 2 ^ width := pointerBound.trans heapFits
  have counterFits : tail.length + 1 < 2 ^ width := by
    have := labels.fits
    simp only [List.length_cons] at this
    omega
  have positiveFits : address base (head, true) < 2 ^ width :=
    (marked.bound (head, true)).trans heapFits
  have negativeFits : address base (head, false) < 2 ^ width :=
    (marked.bound (head, false)).trans heapFits
  have baseFits : base < 2 ^ width := by have := marked.fits; omega
  have doubledFits : 2 * head.val < 2 ^ width := by
    simp only [address, ite_true, Nat.add_zero] at positiveFits
    omega
  have labelFits : head.val < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  let firstHeap := heap.set (address base (head, true)) (encode width false) (marked.bound (head, true))
  let finalHeap := clearHeap marks base heap marked head
  have firstStored : Stored (write marks (head, true) false) base firstHeap := marked.write (head, true) false
  have firstStep : programStep destination
      (configuration heap pointer (tail.length + 1) base labelScratch addressScratch entry) =
      some (configuration heap pointer (tail.length + 1) base labelScratch addressScratch (entry + 1)) := by
    have fetched := step_at destination entry present heap pointer (tail.length + 1) base labelScratch addressScratch
      ⟨0, by decide⟩ capacity
    simp only [Nat.add_zero] at fetched
    rw [fetched]
    change step (.branchZero 1 (word width (entry + 10)))
      (configuration heap pointer (tail.length + 1) base labelScratch addressScratch entry) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some (if (word width (tail.length + 1)).val = 0 then _ else _) = _
    rw [word_val (tail.length + 1) counterFits, ite_eq_right (by omega)]
    rw [configuration_advance heap pointer (tail.length + 1) base labelScratch addressScratch entry (by omega)]
  have readStep : programStep destination
      (configuration heap pointer (tail.length + 1) base labelScratch addressScratch (entry + 1)) =
      some (configuration heap pointer (tail.length + 1) base head.val addressScratch (entry + 2)) := by
    rw [step_at destination entry present heap pointer (tail.length + 1) base labelScratch addressScratch
      ⟨1, by decide⟩ capacity]
    change step (.load 3 0)
      (configuration heap pointer (tail.length + 1) base labelScratch addressScratch (entry + 1)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change (if valid : (word width pointer).val < heap.size then
      some ((configuration heap pointer (tail.length + 1) base labelScratch addressScratch
        (entry + 1)).advance.put 3 (heap[(word width pointer).val]'valid)) else none) = _
    have valid : (word width pointer).val < heap.size := by
      rw [word_val pointer pointerFits]
      exact pointerBound
    rw [dite_eq_left valid]
    have read : heap[(word width pointer).val]'valid = word width head.val := by
      simpa only [word_val pointer pointerFits] using labels.head
    rw [read, configuration_advance heap pointer (tail.length + 1) base labelScratch addressScratch
      (entry + 1) (by omega), put_label]
  have doubleStep : programStep destination
      (configuration heap pointer (tail.length + 1) base head.val addressScratch (entry + 2)) =
      some (configuration heap pointer (tail.length + 1) base head.val (2 * head.val) (entry + 3)) := by
    rw [step_at destination entry present heap pointer (tail.length + 1) base head.val addressScratch
      ⟨2, by decide⟩ capacity]
    change step (.add 4 3 3)
      (configuration heap pointer (tail.length + 1) base head.val addressScratch (entry + 2)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration heap pointer (tail.length + 1) base head.val addressScratch
      (entry + 2)).advance.put 4
      (word width ((word width head.val).val + (word width head.val).val))) = _
    rw [add_words head.val head.val labelFits labelFits,
      configuration_advance heap pointer (tail.length + 1) base head.val addressScratch (entry + 2) (by omega),
      put_address, show head.val + head.val = 2 * head.val by omega]
  have baseStep : programStep destination
      (configuration heap pointer (tail.length + 1) base head.val (2 * head.val) (entry + 3)) =
      some (configuration heap pointer (tail.length + 1) base head.val
        (address base (head, true)) (entry + 4)) := by
    rw [step_at destination entry present heap pointer (tail.length + 1) base head.val (2 * head.val)
      ⟨3, by decide⟩ capacity]
    change step (.add 4 4 7)
      (configuration heap pointer (tail.length + 1) base head.val (2 * head.val) (entry + 3)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration heap pointer (tail.length + 1) base head.val (2 * head.val)
      (entry + 3)).advance.put 4
      (word width ((word width (2 * head.val)).val + (word width base).val))) = _
    rw [add_words (2 * head.val) base doubledFits baseFits,
      configuration_advance heap pointer (tail.length + 1) base head.val (2 * head.val) (entry + 3) (by omega),
      put_address]
    simp [address, Nat.add_comm, Nat.add_left_comm]
  have positiveStep : programStep destination
      (configuration heap pointer (tail.length + 1) base head.val (address base (head, true)) (entry + 4)) =
      some (configuration firstHeap pointer (tail.length + 1) base head.val
        (address base (head, true)) (entry + 5)) := by
    have result := store_mark destination
      (configuration heap pointer (tail.length + 1) base head.val (address base (head, true)) (entry + 4))
      marks base marked (head, true) false 4 2 rfl
      (configured_fetch destination entry present heap pointer (tail.length + 1) base head.val
        (address base (head, true)) ⟨4, by decide⟩ capacity)
      (word_val _ positiveFits) rfl
    rw [configuration_advance heap pointer (tail.length + 1) base head.val (address base (head, true))
      (entry + 4) (by omega)] at result
    exact result
  have nextAddressStep : programStep destination
      (configuration firstHeap pointer (tail.length + 1) base head.val (address base (head, true)) (entry + 5)) =
      some (configuration firstHeap pointer (tail.length + 1) base head.val
        (address base (head, false)) (entry + 6)) := by
    rw [step_at destination entry present firstHeap pointer (tail.length + 1) base head.val
      (address base (head, true)) ⟨5, by decide⟩ capacity]
    change step (.add 4 4 5)
      (configuration firstHeap pointer (tail.length + 1) base head.val (address base (head, true)) (entry + 5)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration firstHeap pointer (tail.length + 1) base head.val
      (address base (head, true)) (entry + 5)).advance.put 4
      (word width ((word width (address base (head, true))).val + (word width 1).val))) = _
    rw [add_words (address base (head, true)) 1 positiveFits oneFits,
      configuration_advance firstHeap pointer (tail.length + 1) base head.val (address base (head, true))
        (entry + 5) (by omega), put_address]
    simp [address, Nat.add_assoc]
  have negativeStep : programStep destination
      (configuration firstHeap pointer (tail.length + 1) base head.val (address base (head, false)) (entry + 6)) =
      some (configuration finalHeap pointer (tail.length + 1) base head.val
        (address base (head, false)) (entry + 7)) := by
    have result := store_mark destination
      (configuration firstHeap pointer (tail.length + 1) base head.val (address base (head, false)) (entry + 6))
      (write marks (head, true) false) base firstStored (head, false) false 4 2 rfl
      (configured_fetch destination entry present firstHeap pointer (tail.length + 1) base head.val
        (address base (head, false)) ⟨6, by decide⟩ capacity)
      (word_val _ negativeFits) rfl
    rw [configuration_advance firstHeap pointer (tail.length + 1) base head.val (address base (head, false))
      (entry + 6) (by omega)] at result
    exact result
  have pointerStep : programStep destination
      (configuration finalHeap pointer (tail.length + 1) base head.val (address base (head, false)) (entry + 7)) =
      some (configuration finalHeap (pointer + 1) (tail.length + 1) base head.val
        (address base (head, false)) (entry + 8)) := by
    rw [step_at destination entry present finalHeap pointer (tail.length + 1) base head.val
      (address base (head, false)) ⟨7, by decide⟩ capacity]
    change step (.add 0 0 5)
      (configuration finalHeap pointer (tail.length + 1) base head.val (address base (head, false)) (entry + 7)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration finalHeap pointer (tail.length + 1) base head.val
      (address base (head, false)) (entry + 7)).advance.put 0
      (word width ((word width pointer).val + (word width 1).val))) = _
    rw [add_words pointer 1 pointerFits oneFits,
      configuration_advance finalHeap pointer (tail.length + 1) base head.val (address base (head, false))
        (entry + 7) (by omega), put_pointer]
  have counterStep : programStep destination
      (configuration finalHeap (pointer + 1) (tail.length + 1) base head.val (address base (head, false)) (entry + 8)) =
      some (configuration finalHeap (pointer + 1) tail.length base head.val
        (address base (head, false)) (entry + 9)) := by
    rw [step_at destination entry present finalHeap (pointer + 1) (tail.length + 1) base head.val
      (address base (head, false)) ⟨8, by decide⟩ capacity]
    change step (.add 1 1 6)
      (configuration finalHeap (pointer + 1) (tail.length + 1) base head.val (address base (head, false)) (entry + 8)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration finalHeap (pointer + 1) (tail.length + 1) base head.val
      (address base (head, false)) (entry + 8)).advance.put 1
      (word width ((word width (tail.length + 1)).val + (word width (2 ^ width - 1)).val))) = _
    rw [Initialize.word_decrement tail.length counterFits,
      configuration_advance finalHeap (pointer + 1) (tail.length + 1) base head.val (address base (head, false))
        (entry + 8) (by omega), put_counter]
  have returnStep : programStep destination
      (configuration finalHeap (pointer + 1) tail.length base head.val (address base (head, false)) (entry + 9)) =
      some (configuration finalHeap (pointer + 1) tail.length base head.val (address base (head, false)) entry) := by
    rw [step_at destination entry present finalHeap (pointer + 1) tail.length base head.val
      (address base (head, false)) ⟨9, by decide⟩ capacity]
    change step (.branchZero 2 (word width entry))
      (configuration finalHeap (pointer + 1) tail.length base head.val (address base (head, false)) (entry + 9)) = _
    simp [step, configuration, State.advance, word]
  have trace := Execution.cons firstStep (Execution.cons readStep (Execution.cons doubleStep
    (Execution.cons baseStep (Execution.cons positiveStep (Execution.cons nextAddressStep
      (Execution.cons negativeStep (Execution.cons pointerStep (Execution.cons counterStep
        (Execution.cons returnStep (Execution.refl
          (configuration finalHeap (pointer + 1) tail.length base head.val (address base (head, false)) entry)))))))))))
  simpa [configuration_liveWords, firstHeap, finalHeap] using trace

/-- The fixed loop reads and clears the whole stored list. It leaves the input
buffer and all other non-mark storage intact, and exits without halting. -/
theorem execution (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (labels : List (Fin n))
    (heap : Array (Word width)) (marks : Marks n)
    (base pointer labelScratch addressScratch : Nat) (marked : Stored marks base heap)
    (stored : LabelsStored labels pointer heap) (separate : base + 2 * n ≤ pointer)
    (capacity : entry + 10 < 2 ^ width) (heapFits : heap.size < 2 ^ width) :
    ∃ (finalHeap : Array (Word width)) (finalLabel finalAddress : Nat),
      Execution destination (configuration heap pointer labels.length base labelScratch addressScratch entry)
        (configuration finalHeap (pointer + labels.length) 0 base finalLabel finalAddress (entry + 10))
        (10 * labels.length + 1) (9 + heap.size) ∧
      Stored (Marks.clear labels marks) base finalHeap ∧
      finalHeap.size = heap.size ∧ Frame n base heap finalHeap := by
  induction labels generalizing heap marks pointer labelScratch addressScratch with
  | nil =>
      refine ⟨heap, labelScratch, addressScratch, ?_, marked, rfl, Frame.refl n base heap⟩
      simpa using zero_execution destination entry present heap pointer base labelScratch addressScratch capacity
  | cons head tail ih =>
      let cleared := clearHeap marks base heap marked head
      have clearedSize : cleared.size = heap.size := clearHeap_size marks base heap marked head
      have clearedMarked : Stored (Marks.clear [head] marks) base cleared :=
        clearHeap_stored marks base heap marked head
      have tailStored : LabelsStored tail (pointer + 1) cleared :=
        (clearHeap_labels marks base heap marked head (head :: tail) pointer stored separate).tail
      obtain ⟨finalHeap, finalLabel, finalAddress, rest, finalMarked, finalSize, finalFrame⟩ :=
        ih cleared (Marks.clear [head] marks) (pointer + 1) head.val (address base (head, false))
          clearedMarked tailStored (by omega) (by simpa only [clearedSize] using heapFits)
      have first := iteration destination entry present heap marks base pointer labelScratch addressScratch
        marked head tail stored capacity heapFits
      have trace := first.append rest
      refine ⟨finalHeap, finalLabel, finalAddress, ?_, ?_, finalSize.trans clearedSize, ?_⟩
      · simpa only [List.length_cons, clearedSize, Nat.max_self, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace
      · simpa only [Marks.clear] using finalMarked
      · exact (clearHeap_frame marks base heap marked head).trans finalFrame

/-- A correct row clears every ambient mark after visiting only its touched
labels. Its reset trace has at most ten instructions per input literal, plus
the final zero-count branch. -/
theorem row_execution (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (clause : CNF.Clause (Fin n))
    (row : Row n) (correct : row.Correct clause) (heap : Array (Word width))
    (base pointer labelScratch addressScratch : Nat) (marked : Stored row.marks base heap)
    (stored : LabelsStored row.touched pointer heap) (separate : base + 2 * n ≤ pointer)
    (capacity : entry + 10 < 2 ^ width) (heapFits : heap.size < 2 ^ width) :
    ∃ (finalHeap : Array (Word width)) (finalLabel finalAddress : Nat),
      Execution destination
        (configuration heap pointer row.touched.length base labelScratch addressScratch entry)
        (configuration finalHeap (pointer + row.touched.length) 0 base finalLabel finalAddress (entry + 10))
        (10 * row.touched.length + 1) (9 + heap.size) ∧
      Stored (Marks.clear row.touched row.marks) base finalHeap ∧
      (Marks.clear row.touched row.marks).Clean ∧
      10 * row.touched.length + 1 ≤ 10 * clause.length + 1 ∧
      finalHeap.size = heap.size ∧ Frame n base heap finalHeap := by
  obtain ⟨finalHeap, finalLabel, finalAddress, trace, finalMarked, finalSize, finalFrame⟩ :=
    execution destination entry present row.touched heap row.marks base pointer labelScratch addressScratch
      marked stored separate capacity heapFits
  refine ⟨finalHeap, finalLabel, finalAddress, trace, finalMarked, Row.clear_clean correct, ?_, finalSize, finalFrame⟩
  have lengthBound := Row.touched_length_le correct
  omega

end Controller.Horn.ResetTouched
