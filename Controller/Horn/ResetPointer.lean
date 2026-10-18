module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.JoinedLiteral
public import Controller.Horn.ResetTouched

@[expose] public section

/-!
# Pointer-controlled traversal of the stored touched-label buffer

The fixed loop compares its actual pointer with the canonical buffer end. It
never receives a semantic list length in a counter register. The end is a
layout constant in the fetched code; the starting pointer is loaded from the
actual touched-header word by the caller's setup instructions.
-/
namespace Controller.Horn.ResetPointer

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize
open Controller.Horn.MarkStorage Controller.Horn.ResetTouched

def code (width entry limit : Nat) : Program width 8 :=
  #[.constant 1 (word width limit), .xor 1 0 1,
    .branchZero 1 (word width (entry + 11)), .load 3 0,
    .add 4 3 3, .add 4 4 7, .store 4 2, .add 4 4 5, .store 4 2,
    .add 0 0 5, .branchZero 2 (word width entry)]

@[simp] theorem code_size (width entry limit : Nat) : (code width entry limit).size = 11 := rfl

def CodeAt (destination : Program width 8) (entry limit : Nat) : Prop :=
  ∀ index : Fin 11, destination[entry + index.val]? = some (code width entry limit)[index.val]

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem add_words (left right : Nat) (leftFits : left < 2 ^ width)
    (rightFits : right < 2 ^ width) :
    word width ((word width left).val + (word width right).val) = word width (left + right) := by
  rw [word_val left leftFits, word_val right rightFits]

theorem xor_zero_iff (left right : Nat) : Nat.xor left right = 0 ↔ left = right := by
  constructor
  · intro equal
    have canceled := congrArg (fun value : Nat => Nat.xor value right) equal
    simpa [Nat.xor_assoc] using canceled
  · rintro rfl
    exact Nat.xor_self _

theorem configured_fetch (destination : Program width 8) (entry limit : Nat)
    (present : CodeAt destination entry limit) (heap : Array (Word width))
    (pointer comparison base labelScratch addressScratch : Nat) (phase : Fin 11)
    (capacity : entry + 11 < 2 ^ width) :
    destination[(configuration heap pointer comparison base labelScratch addressScratch
      (entry + phase.val)).pc.val]? = some (code width entry limit)[phase.val] := by
  change destination[(word width (entry + phase.val)).val]? = _
  rw [word_val (width := width) (entry + phase.val) (by have := phase.isLt; omega)]
  exact present phase

private theorem step_at (destination : Program width 8) (entry limit : Nat)
    (present : CodeAt destination entry limit) (heap : Array (Word width))
    (pointer comparison base labelScratch addressScratch : Nat) (phase : Fin 11)
    (capacity : entry + 11 < 2 ^ width) :
    programStep destination (configuration heap pointer comparison base labelScratch addressScratch (entry + phase.val)) =
      step (code width entry limit)[phase.val]
        (configuration heap pointer comparison base labelScratch addressScratch (entry + phase.val)) := by
  unfold programStep
  rw [configured_fetch destination entry limit present heap pointer comparison base labelScratch addressScratch phase capacity]
  rfl

/-- The three pointer-comparison instructions load the layout end and compare
it with the actual pointer. Their scratch result is a word-sized XOR. -/
theorem compare_execution (destination : Program width 8) (entry limit : Nat)
    (present : CodeAt destination entry limit) (heap : Array (Word width))
    (pointer comparison base labelScratch addressScratch : Nat)
    (capacity : entry + 11 < 2 ^ width) (pointerFits : pointer < 2 ^ width)
    (limitFits : limit < 2 ^ width) (different : pointer ≠ limit) :
    Execution destination (configuration heap pointer comparison base labelScratch addressScratch entry)
      (configuration heap pointer (Nat.xor pointer limit) base labelScratch addressScratch (entry + 3))
      3 (9 + heap.size) := by
  have first : programStep destination (configuration heap pointer comparison base labelScratch addressScratch entry) =
      some (configuration heap pointer limit base labelScratch addressScratch (entry + 1)) := by
    change programStep destination (configuration heap pointer comparison base labelScratch addressScratch (entry + 0)) = _
    rw [step_at destination entry limit present heap pointer comparison base labelScratch addressScratch ⟨0, by decide⟩ capacity]
    change step (.constant 1 (word width limit)) _ = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    rw [configuration_advance _ _ _ _ _ _ _ (by omega), put_counter]
  have second : programStep destination (configuration heap pointer limit base labelScratch addressScratch (entry + 1)) =
      some (configuration heap pointer (Nat.xor pointer limit) base labelScratch addressScratch (entry + 2)) := by
    rw [step_at destination entry limit present heap pointer limit base labelScratch addressScratch ⟨1, by decide⟩ capacity]
    change step (.xor 1 0 1) _ = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration heap pointer limit base labelScratch addressScratch (entry + 1)).advance.put 1
      (word width (Nat.xor (word width pointer).val (word width limit).val))) = _
    rw [word_val pointer pointerFits, word_val limit limitFits,
      configuration_advance _ _ _ _ _ _ _ (by omega), put_counter]
  have xorFits : Nat.xor pointer limit < 2 ^ width := Nat.xor_lt_two_pow pointerFits limitFits
  have nonzero : Nat.xor pointer limit ≠ 0 := fun equal => different ((xor_zero_iff _ _).mp equal)
  have third : programStep destination (configuration heap pointer (Nat.xor pointer limit) base labelScratch addressScratch (entry + 2)) =
      some (configuration heap pointer (Nat.xor pointer limit) base labelScratch addressScratch (entry + 3)) := by
    rw [step_at destination entry limit present heap pointer (Nat.xor pointer limit) base labelScratch addressScratch ⟨2, by decide⟩ capacity]
    change step (.branchZero 1 (word width (entry + 11))) _ = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some (if (word width (Nat.xor pointer limit)).val = 0 then _ else _) = _
    rw [word_val (Nat.xor pointer limit) xorFits, ite_eq_right nonzero, configuration_advance _ _ _ _ _ _ _ (by omega)]
  have trace := Execution.cons first (Execution.cons second (Execution.cons third
    (Execution.refl (configuration heap pointer (Nat.xor pointer limit) base labelScratch addressScratch (entry + 3)))))
  simpa only [configuration_liveWords, Nat.zero_add, Nat.max_self] using trace

/-- A nonempty stored suffix supplies the strict pointer/end inequality used by
actual XOR control. The eight remaining instructions clear one channel. -/
theorem iteration (destination : Program width 8) (entry limit : Nat)
    (present : CodeAt destination entry limit) (heap : Array (Word width))
    (marks : Marks n) (base pointer comparison labelScratch addressScratch : Nat)
    (marked : Stored marks base heap) (head : Fin n) (tail : List (Fin n))
    (labels : LabelsStored (head :: tail) pointer heap)
    (ends : pointer + (head :: tail).length = limit)
    (capacity : entry + 11 < 2 ^ width) (heapFits : heap.size < 2 ^ width) :
    Execution destination (configuration heap pointer comparison base labelScratch addressScratch entry)
      (configuration (clearHeap marks base heap marked head) (pointer + 1) (Nat.xor pointer limit) base
        head.val (address base (head, false)) entry) 11 (9 + heap.size) := by
  have pointerBound : pointer < heap.size := by have := labels.fits; simp only [List.length_cons] at this; omega
  have pointerFits : pointer < 2 ^ width := pointerBound.trans heapFits
  have limitFits : limit < 2 ^ width := by have := labels.fits; omega
  have positiveFits : address base (head, true) < 2 ^ width := (marked.bound (head, true)).trans heapFits
  have negativeFits : address base (head, false) < 2 ^ width := (marked.bound (head, false)).trans heapFits
  have baseFits : base < 2 ^ width := by have := marked.fits; omega
  have doubledFits : 2 * head.val < 2 ^ width := by simp only [address, ite_true, Nat.add_zero] at positiveFits; omega
  have labelFits : head.val < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  let comparisonValue := Nat.xor pointer limit
  let firstHeap := heap.set (address base (head, true)) (encode width false) (marked.bound (head, true))
  let finalHeap := clearHeap marks base heap marked head
  have firstStored : Stored (write marks (head, true) false) base firstHeap := marked.write (head, true) false
  have comparisonTrace := compare_execution destination entry limit present heap pointer comparison base labelScratch addressScratch
    capacity pointerFits limitFits (by simp only [List.length_cons] at ends; omega)
  have readStep : programStep destination
      (configuration heap pointer comparisonValue base labelScratch addressScratch (entry + 3)) =
      some (configuration heap pointer comparisonValue base head.val addressScratch (entry + 4)) := by
    rw [step_at destination entry limit present heap pointer comparisonValue base labelScratch addressScratch
      ⟨3, by decide⟩ capacity]
    change step (.load 3 0)
      (configuration heap pointer comparisonValue base labelScratch addressScratch (entry + 3)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change (if valid : (word width pointer).val < heap.size then
      some ((configuration heap pointer comparisonValue base labelScratch addressScratch
        (entry + 3)).advance.put 3 (heap[(word width pointer).val]'valid)) else none) = _
    have valid : (word width pointer).val < heap.size := by
      rw [word_val pointer pointerFits]
      exact pointerBound
    rw [dite_eq_left valid]
    have read : heap[(word width pointer).val]'valid = word width head.val := by
      simpa only [word_val pointer pointerFits] using labels.head
    rw [read, configuration_advance heap pointer comparisonValue base labelScratch addressScratch
      (entry + 3) (by omega), put_label]
  have doubleStep : programStep destination
      (configuration heap pointer comparisonValue base head.val addressScratch (entry + 4)) =
      some (configuration heap pointer comparisonValue base head.val (2 * head.val) (entry + 5)) := by
    rw [step_at destination entry limit present heap pointer comparisonValue base head.val addressScratch
      ⟨4, by decide⟩ capacity]
    change step (.add 4 3 3)
      (configuration heap pointer comparisonValue base head.val addressScratch (entry + 4)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration heap pointer comparisonValue base head.val addressScratch
      (entry + 4)).advance.put 4
      (word width ((word width head.val).val + (word width head.val).val))) = _
    rw [add_words head.val head.val labelFits labelFits,
      configuration_advance heap pointer comparisonValue base head.val addressScratch (entry + 4) (by omega),
      put_address, show head.val + head.val = 2 * head.val by omega]
  have baseStep : programStep destination
      (configuration heap pointer comparisonValue base head.val (2 * head.val) (entry + 5)) =
      some (configuration heap pointer comparisonValue base head.val
        (address base (head, true)) (entry + 6)) := by
    rw [step_at destination entry limit present heap pointer comparisonValue base head.val (2 * head.val)
      ⟨5, by decide⟩ capacity]
    change step (.add 4 4 7)
      (configuration heap pointer comparisonValue base head.val (2 * head.val) (entry + 5)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration heap pointer comparisonValue base head.val (2 * head.val)
      (entry + 5)).advance.put 4
      (word width ((word width (2 * head.val)).val + (word width base).val))) = _
    rw [add_words (2 * head.val) base doubledFits baseFits,
      configuration_advance heap pointer comparisonValue base head.val (2 * head.val) (entry + 5) (by omega),
      put_address]
    simp [address, Nat.add_comm, Nat.add_left_comm]
  have positiveStep : programStep destination
      (configuration heap pointer comparisonValue base head.val (address base (head, true)) (entry + 6)) =
      some (configuration firstHeap pointer comparisonValue base head.val
        (address base (head, true)) (entry + 7)) := by
    have result := store_mark destination
      (configuration heap pointer comparisonValue base head.val (address base (head, true)) (entry + 6))
      marks base marked (head, true) false 4 2 rfl
      (configured_fetch destination entry limit present heap pointer comparisonValue base head.val
        (address base (head, true)) ⟨6, by decide⟩ capacity)
      (word_val _ positiveFits) rfl
    rw [configuration_advance heap pointer comparisonValue base head.val (address base (head, true))
      (entry + 6) (by omega)] at result
    exact result
  have nextAddressStep : programStep destination
      (configuration firstHeap pointer comparisonValue base head.val (address base (head, true)) (entry + 7)) =
      some (configuration firstHeap pointer comparisonValue base head.val
        (address base (head, false)) (entry + 8)) := by
    rw [step_at destination entry limit present firstHeap pointer comparisonValue base head.val
      (address base (head, true)) ⟨7, by decide⟩ capacity]
    change step (.add 4 4 5)
      (configuration firstHeap pointer comparisonValue base head.val (address base (head, true)) (entry + 7)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration firstHeap pointer comparisonValue base head.val
      (address base (head, true)) (entry + 7)).advance.put 4
      (word width ((word width (address base (head, true))).val + (word width 1).val))) = _
    rw [add_words (address base (head, true)) 1 positiveFits oneFits,
      configuration_advance firstHeap pointer comparisonValue base head.val (address base (head, true))
        (entry + 7) (by omega), put_address]
    simp [address, Nat.add_assoc]
  have negativeStep : programStep destination
      (configuration firstHeap pointer comparisonValue base head.val (address base (head, false)) (entry + 8)) =
      some (configuration finalHeap pointer comparisonValue base head.val
        (address base (head, false)) (entry + 9)) := by
    have result := store_mark destination
      (configuration firstHeap pointer comparisonValue base head.val (address base (head, false)) (entry + 8))
      (write marks (head, true) false) base firstStored (head, false) false 4 2 rfl
      (configured_fetch destination entry limit present firstHeap pointer comparisonValue base head.val
        (address base (head, false)) ⟨8, by decide⟩ capacity)
      (word_val _ negativeFits) rfl
    rw [configuration_advance firstHeap pointer comparisonValue base head.val (address base (head, false))
      (entry + 8) (by omega)] at result
    exact result
  have pointerStep : programStep destination
      (configuration finalHeap pointer comparisonValue base head.val (address base (head, false)) (entry + 9)) =
      some (configuration finalHeap (pointer + 1) comparisonValue base head.val
        (address base (head, false)) (entry + 10)) := by
    rw [step_at destination entry limit present finalHeap pointer comparisonValue base head.val
      (address base (head, false)) ⟨9, by decide⟩ capacity]
    change step (.add 0 0 5)
      (configuration finalHeap pointer comparisonValue base head.val (address base (head, false)) (entry + 9)) = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration finalHeap pointer comparisonValue base head.val
      (address base (head, false)) (entry + 9)).advance.put 0
      (word width ((word width pointer).val + (word width 1).val))) = _
    rw [add_words pointer 1 pointerFits oneFits,
      configuration_advance finalHeap pointer comparisonValue base head.val (address base (head, false))
        (entry + 9) (by omega), put_pointer]
  have returnStep : programStep destination
      (configuration finalHeap (pointer + 1) comparisonValue base head.val (address base (head, false)) (entry + 10)) =
      some (configuration finalHeap (pointer + 1) comparisonValue base head.val (address base (head, false)) entry) := by
    rw [step_at destination entry limit present finalHeap (pointer + 1) comparisonValue base head.val
      (address base (head, false)) ⟨10, by decide⟩ capacity]
    change step (.branchZero 2 (word width entry)) _ = _
    simp [step, configuration, State.advance, word]
  have tailTrace := Execution.cons readStep (Execution.cons doubleStep (Execution.cons baseStep
    (Execution.cons positiveStep (Execution.cons nextAddressStep (Execution.cons negativeStep
      (Execution.cons pointerStep (Execution.cons returnStep (Execution.refl
        (configuration finalHeap (pointer + 1) comparisonValue base head.val (address base (head, false)) entry)))))))))
  have trace := comparisonTrace.append tailTrace
  simpa [configuration_liveWords, firstHeap, finalHeap, comparisonValue] using trace


/-- When the actual pointer equals the region end, the fixed comparison prefix
exits before any heap read. Even an arbitrary incoming scratch word is allowed. -/
theorem empty_execution (destination : Program width 8) (entry limit : Nat)
    (present : CodeAt destination entry limit) (heap : Array (Word width))
    (comparison base labelScratch addressScratch : Nat)
    (capacity : entry + 11 < 2 ^ width) (limitFits : limit < 2 ^ width) :
    Execution destination (configuration heap limit comparison base labelScratch addressScratch entry)
      (configuration heap limit 0 base labelScratch addressScratch (entry + 11)) 3 (9 + heap.size) := by
  have first : programStep destination (configuration heap limit comparison base labelScratch addressScratch entry) =
      some (configuration heap limit limit base labelScratch addressScratch (entry + 1)) := by
    change programStep destination (configuration heap limit comparison base labelScratch addressScratch (entry + 0)) = _
    rw [step_at destination entry limit present heap limit comparison base labelScratch addressScratch ⟨0, by decide⟩ capacity]
    change step (.constant 1 (word width limit)) _ = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    rw [configuration_advance _ _ _ _ _ _ _ (by omega), put_counter]
  have second : programStep destination (configuration heap limit limit base labelScratch addressScratch (entry + 1)) =
      some (configuration heap limit 0 base labelScratch addressScratch (entry + 2)) := by
    rw [step_at destination entry limit present heap limit limit base labelScratch addressScratch ⟨1, by decide⟩ capacity]
    change step (.xor 1 0 1) _ = _
    simp only [step, configuration_running, Bool.false_eq_true, ite_false]
    change some ((configuration heap limit limit base labelScratch addressScratch (entry + 1)).advance.put 1
      (word width (Nat.xor (word width limit).val (word width limit).val))) = _
    rw [word_val limit limitFits]
    simp only [Nat.xor_eq, Nat.xor_self]
    rw [
      configuration_advance _ _ _ _ _ _ _ (by omega), put_counter]
  have third : programStep destination (configuration heap limit 0 base labelScratch addressScratch (entry + 2)) =
      some (configuration heap limit 0 base labelScratch addressScratch (entry + 11)) := by
    rw [step_at destination entry limit present heap limit 0 base labelScratch addressScratch ⟨2, by decide⟩ capacity]
    change step (.branchZero 1 (word width (entry + 11))) _ = _
    simp [step, configuration, State.advance, word]
  have trace := Execution.cons first (Execution.cons second (Execution.cons third
    (Execution.refl (configuration heap limit 0 base labelScratch addressScratch (entry + 11)))))
  simpa only [configuration_liveWords, Nat.zero_add, Nat.max_self] using trace

/-- Universal same-program pointer traversal. List length appears only in the
representation invariant and the proved cost, never in the input registers. -/
theorem execution (destination : Program width 8) (entry limit : Nat)
    (present : CodeAt destination entry limit) (labels : List (Fin n))
    (heap : Array (Word width)) (marks : Marks n)
    (base pointer comparison labelScratch addressScratch : Nat) (marked : Stored marks base heap)
    (stored : LabelsStored labels pointer heap) (ends : pointer + labels.length = limit)
    (separate : base + 2 * n ≤ pointer)
    (capacity : entry + 11 < 2 ^ width) (heapFits : heap.size < 2 ^ width) :
    ∃ (finalHeap : Array (Word width)) (finalLabel finalAddress : Nat),
      Execution destination (configuration heap pointer comparison base labelScratch addressScratch entry)
        (configuration finalHeap limit 0 base finalLabel finalAddress (entry + 11))
        (11 * labels.length + 3) (9 + heap.size) ∧
      Stored (Marks.clear labels marks) base finalHeap ∧
      finalHeap.size = heap.size ∧ Frame n base heap finalHeap := by
  induction labels generalizing heap marks pointer comparison labelScratch addressScratch with
  | nil =>
      have pointerEq : pointer = limit := by simpa using ends
      subst pointer
      refine ⟨heap, labelScratch, addressScratch, ?_, marked, rfl, Frame.refl n base heap⟩
      simpa using empty_execution destination entry limit present heap comparison base labelScratch addressScratch
        capacity (by have := stored.fits; simp only [List.length_nil, Nat.add_zero] at this; omega)
  | cons head tail ih =>
      let cleared := clearHeap marks base heap marked head
      have clearedSize : cleared.size = heap.size := clearHeap_size marks base heap marked head
      have clearedMarked : Stored (Marks.clear [head] marks) base cleared := clearHeap_stored marks base heap marked head
      have tailStored : LabelsStored tail (pointer + 1) cleared :=
        (clearHeap_labels marks base heap marked head (head :: tail) pointer stored separate).tail
      obtain ⟨finalHeap, finalLabel, finalAddress, rest, finalMarked, finalSize, finalFrame⟩ :=
        ih cleared (Marks.clear [head] marks) (pointer + 1) (Nat.xor pointer limit)
          head.val (address base (head, false)) clearedMarked tailStored
          (by simp only [List.length_cons] at ends; omega) (by omega)
          (by simpa only [clearedSize] using heapFits)
      have first := iteration destination entry limit present heap marks base pointer comparison labelScratch addressScratch
        marked head tail stored ends capacity heapFits
      have trace := first.append rest
      refine ⟨finalHeap, finalLabel, finalAddress, ?_, ?_, finalSize.trans clearedSize, ?_⟩
      · simpa only [List.length_cons, clearedSize, Nat.max_self, Nat.mul_add, Nat.mul_one,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace
      · simpa only [Marks.clear] using finalMarked
      · exact (clearHeap_frame marks base heap marked head).trans finalFrame


/-- The caller setup loads the actual touched cursor and installs the mark base.
The region end is encoded only in the fixed reset loop, not as a length word. -/
def setupCode (width header base : Nat) : Program width 8 :=
  #[.constant 0 (word width header), .load 0 0, .constant 7 (word width base)]

def SetupAt (destination : Program width 8) (entry header base : Nat) : Prop :=
  ∀ index : Fin 3, destination[entry + index.val]? = some (setupCode width header base)[index.val]

def setupMiddle (state : State width 8) (header pointer : Nat) : State width 8 :=
  (state.advance.put 0 (word width header)).advance.put 0 (word width pointer)

def setupFinished (state : State width 8) (header pointer base : Nat) : State width 8 :=
  (setupMiddle state header pointer).advance.put 7 (word width base)

theorem setup_execution (destination : Program width 8) (entry header base pointer : Nat)
    (present : SetupAt destination entry header base) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 3 < 2 ^ width) (headerBound : header < state.heap.size)
    (headerFits : header < 2 ^ width) (stored : state.heap[header]'headerBound = word width pointer) :
    Execution destination state (setupFinished state header pointer base) 3 state.liveWords := by
  let first := state.advance.put 0 (word width header)
  have firstPosition : first.pc = word width (entry + 1) := by
    simp only [first, State.advance, State.put, position, word_val (width := width) entry (by omega)]
    all_goals rfl
  have secondPosition : (setupMiddle state header pointer).pc = word width (entry + 2) := by
    simp only [setupMiddle, State.advance, State.put, position, word_val (width := width) entry (by omega),
      word_val (width := width) (entry + 1) (by omega)]
    all_goals rfl
  have fetch0 : destination[state.pc.val]? = some (.constant 0 (word width header)) := by
    rw [position, word_val (width := width) entry (by omega)]
    simpa [setupCode] using present ⟨0, by decide⟩
  have fetch1 : destination[first.pc.val]? = some (.load 0 0) := by
    rw [firstPosition, word_val (width := width) (entry + 1) (by omega)]
    simpa [setupCode] using present ⟨1, by decide⟩
  have fetch2 : destination[(setupMiddle state header pointer).pc.val]? = some (.constant 7 (word width base)) := by
    rw [secondPosition, word_val (width := width) (entry + 2) (by omega)]
    simpa [setupCode] using present ⟨2, by decide⟩
  have one : programStep destination state = some first := by
    unfold programStep
    rw [fetch0]
    simp [step, running, first]
  have two : programStep destination first = some (setupMiddle state header pointer) := by
    unfold programStep
    rw [fetch1]
    change step (.load 0 0) first = _
    have points : (first.reg 0).val = header := by
      simp only [first, State.put, ite_true]
      exact word_val (width := width) header headerFits
    simp only [step, show first.halted = false from running, Bool.false_eq_true, ite_false, points]
    have valid : header < first.heap.size := headerBound
    rw [dite_eq_left valid]
    change some (first.advance.put 0 (state.heap[header]'headerBound)) =
      some (first.advance.put 0 (word width pointer))
    exact congrArg (fun value => some (first.advance.put 0 value)) stored
  have three : programStep destination (setupMiddle state header pointer) = some (setupFinished state header pointer base) := by
    unfold programStep
    rw [fetch2]
    simp [step, show (setupMiddle state header pointer).halted = false from running, setupFinished]
  have trace := Execution.cons one (Execution.cons two (Execution.cons three
    (Execution.refl (setupFinished state header pointer base))))
  simpa [first, setupFinished, setupMiddle, State.advance, State.put, State.liveWords] using trace

theorem setupFinished_pointer (state : State width 8) (header pointer base : Nat) :
    (setupFinished state header pointer base).reg 0 = word width pointer := by
  simp [setupFinished, setupMiddle, State.put, State.advance]

theorem setupFinished_base (state : State width 8) (header pointer base : Nat) :
    (setupFinished state header pointer base).reg 7 = word width base := by
  simp [setupFinished, State.put]

theorem setupFinished_frame (state : State width 8) (header pointer base : Nat) :
    (∀ register : Fin 8, register ≠ 0 → register ≠ 7 →
      (setupFinished state header pointer base).reg register = state.reg register) ∧
    (setupFinished state header pointer base).heap = state.heap ∧
    (setupFinished state header pointer base).stack = state.stack ∧
    (setupFinished state header pointer base).output = state.output := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro register pointerRegister baseRegister
  simp [setupFinished, setupMiddle, State.put, State.advance, pointerRegister, baseRegister]


theorem setupFinished_position (state : State width 8) (header pointer base entry : Nat)
    (position : state.pc = word width entry) (capacity : entry + 3 < 2 ^ width) :
    (setupFinished state header pointer base).pc = word width (entry + 3) := by
  simp only [setupFinished, setupMiddle, State.advance, State.put, position,
    word_val (width := width) entry (by omega), word_val (width := width) (entry + 1) (by omega),
    word_val (width := width) (entry + 2) (by omega)]

end Controller.Horn.ResetPointer
