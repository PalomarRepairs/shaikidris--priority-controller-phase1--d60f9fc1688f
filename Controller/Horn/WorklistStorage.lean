module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.NormalizeCold
public import Controller.Horn.Worklist

@[expose] public section

/-! Original normalized rules remain the specification after propagation mutates
record counts and scheduling tags. Head/body words retain their original values.
The clean normalizer mark cells become bucket heads and variable-off flags. -/
namespace Controller.Horn.WorklistStorage
open Controller.Cost Controller.Horn.Worklist Controller.Horn.ResetTouched
open Controller.Horn.Worklist.IndexedNormalize
variable {width n : Nat}

/-- Successful fetched transitions survive addition of later program code. -/
theorem step_append (code continuation : Program width registers)
    (before after : Controller.Cost.State width registers)
    (transition : programStep code before = some after) :
    programStep (code ++ continuation) before = some after := by
  cases fetched : code[before.pc.val]? with
  | none => simp [programStep, fetched] at transition
  | some operation =>
    obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp fetched
    unfold programStep at transition ⊢
    rw [Array.getElem?_append_left inside]
    exact transition

/-- Same original state, fetched trace, endpoint, ticks and live peak. Added
program storage is charged independently by `append_program_words`. -/
theorem execution_append {code : Program width registers}
    (continuation : Program width registers) {before after : Controller.Cost.State width registers}
    {ticks peak : Nat} (trace : Execution code before after ticks peak) :
    Execution (code ++ continuation) before after ticks peak := by
  induction trace with
  | refl state => exact Execution.refl state
  | cons transition rest ih => exact Execution.cons (step_append _ _ _ _ transition) ih

@[simp] theorem append_program_words (code continuation : Program width registers) :
    programWords (code ++ continuation) = programWords code + programWords continuation := by
  simp [programWords, Nat.mul_add]

/-- A fired row has tag zero but retains its original head and body. Count zero
and scheduling soundness are obligations of the propagation invariant. -/
structure MutableStored (rule : Rule (Fin n)) (offset count : Nat) (fired : Bool)
    (heap : Array (Word width)) : Prop where
  fits : offset + 3 + rule.positives.length ≤ heap.size
  countFits : count < 2 ^ width
  tagValue : heap[offset]'(by omega) = word width (if fired then 0 else Controller.Horn.RuleCopy.tag rule)
  headValue : heap[offset + 1]'(by omega) = Controller.Horn.RuleCopy.headWord width rule
  countValue : heap[offset + 2]'(by omega) = word width count
  body : LabelsStored rule.positives (offset + 3) heap

/-- Actual copied records, before any scheduling/count mutation. -/
theorem initial {rule : Rule (Fin n)} {offset : Nat} {heap : Array (Word width)}
    (stored : Controller.Horn.RuleCopy.Stored rule offset heap) :
    MutableStored rule offset rule.positives.length false heap := by
  exact ⟨stored.fits, stored.countFits, stored.tagValue, stored.headValue,
    stored.countValue, stored.body⟩

private theorem labels_below_store {labels : List (Fin n)} {offset index : Nat}
    {heap : Array (Word width)} (stored : LabelsStored labels offset heap)
    (bound : index < heap.size) (before : index < offset) (value : Word width) :
    LabelsStored labels offset (heap.set index value bound) := by
  refine ⟨by simpa using stored.fits, ?_⟩
  intro position
  have valid : offset + position.val < heap.size := by have := stored.fits; have := position.isLt; omega
  exact (Array.getElem_set_ne bound valid (by omega)).trans (stored.entry position)

/-- Replacing the physical count preserves original tag, head and every label. -/
theorem store_count {rule : Rule (Fin n)} {offset oldCount newCount : Nat}
    {fired : Bool} {heap : Array (Word width)}
    (stored : MutableStored rule offset oldCount fired heap) (fits : newCount < 2 ^ width) :
    MutableStored rule offset newCount fired
      (heap.set (offset + 2) (word width newCount) (by have := stored.fits; omega)) := by
  have b0 : offset < heap.size := by have := stored.fits; omega
  have b1 : offset + 1 < heap.size := by have := stored.fits; omega
  have b2 : offset + 2 < heap.size := by have := stored.fits; omega
  refine ⟨by simpa using stored.fits, fits, ?_, ?_, ?_,
    labels_below_store stored.body b2 (by omega) (word width newCount)⟩
  · exact (Array.getElem_set_ne b2 b0 (by omega)).trans stored.tagValue
  · exact (Array.getElem_set_ne b2 b1 (by omega)).trans stored.headValue
  · simp

/-- Scheduling changes only the tag. The head remains available on pending rows. -/
theorem store_fired {rule : Rule (Fin n)} {offset count : Nat} {fired : Bool}
    {heap : Array (Word width)} (stored : MutableStored rule offset count fired heap) :
    MutableStored rule offset count true
      (heap.set offset (word width 0) (by have := stored.fits; omega)) := by
  have b0 : offset < heap.size := by have := stored.fits; omega
  have b1 : offset + 1 < heap.size := by have := stored.fits; omega
  have b2 : offset + 2 < heap.size := by have := stored.fits; omega
  refine ⟨by simpa using stored.fits, stored.countFits, ?_, ?_, ?_,
    labels_below_store stored.body b0 (by omega) (word width 0)⟩
  · simp
  · exact (Array.getElem_set_ne b0 b1 (by omega)).trans stored.headValue
  · exact (Array.getElem_set_ne b0 b2 (by omega)).trans stored.countValue

/-- Appending bucket nodes preserves all mutable fields and original body words. -/
theorem MutableStored.after_push {rule : Rule (Fin n)} {offset count : Nat} {fired : Bool}
    {heap : Array (Word width)} (stored : MutableStored rule offset count fired heap)
    (value : Word width) : MutableStored rule offset count fired (heap.push value) := by
  have b0 : offset < heap.size := by have := stored.fits; omega
  have b1 : offset + 1 < heap.size := by have := stored.fits; omega
  have b2 : offset + 2 < heap.size := by have := stored.fits; omega
  exact ⟨by have := stored.fits; simp only [Array.size_push]; omega, stored.countFits,
    (Array.getElem_push_lt b0).trans stored.tagValue,
    (Array.getElem_push_lt b1).trans stored.headValue,
    (Array.getElem_push_lt b2).trans stored.countValue,
    Controller.Horn.RuleCopy.labels_after_push stored.body value⟩

def headAddress (base : Nat) (label : Fin n) : Nat := base + 2 * label.val
def offAddress (base : Nat) (label : Fin n) : Nat := base + 2 * label.val + 1

/-- Clean normalizer marks supply both actual zero words; no new n-channel
initialization scan is assumed or required by the bucket representation. -/
theorem scratch_zero {clauses : List (Controller.CNF.Clause (Fin n))}
    {layout : Controller.Horn.SourceDirectory.Layout clauses} {recordStart index : Nat}
    {marks : Marks n} {state : Controller.Cost.State width 8}
    (invariant : Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart index marks state)
    (label : Fin n) :
    state.heap[headAddress layout.base label]? = some (word width 0) ∧
    state.heap[offAddress layout.base label]? = some (word width 0) := by
  have positive := invariant.scratch.marks.entry (label, true)
  have negative := invariant.scratch.marks.entry (label, false)
  have positiveZero := invariant.clean.marked (label, true)
  have negativeZero := invariant.clean.marked (label, false)
  simp only [List.not_mem_nil, decide_false] at positiveZero negativeZero
  constructor
  · have bound := invariant.scratch.marks.bound (label, true)
    rw [Array.getElem?_eq_getElem (by simpa [headAddress, Controller.Horn.MarkStorage.address] using bound)]
    apply congrArg some
    simpa [headAddress, Controller.Horn.MarkStorage.address, Controller.Horn.MarkStorage.encode,
      positiveZero] using positive
  · have bound := invariant.scratch.marks.bound (label, false)
    rw [Array.getElem?_eq_getElem (by simpa [offAddress, Controller.Horn.MarkStorage.address, Nat.add_assoc] using bound)]
    apply congrArg some
    simpa [offAddress, Controller.Horn.MarkStorage.address, Controller.Horn.MarkStorage.encode,
      negativeZero, Nat.add_assoc] using negative

/-- A link holds a physical row address and the previously stored bucket head.
Zero is the nil pointer; allocated node addresses are separately proved positive. -/
structure NodeStored (rowAddress previous offset : Nat) (heap : Array (Word width)) : Prop where
  fits : offset + 2 ≤ heap.size
  rowFits : rowAddress < 2 ^ width
  previousFits : previous < 2 ^ width
  offsetFits : offset < 2 ^ width
  row : heap[offset]'(by omega) = word width rowAddress
  next : heap[offset + 1]'(by omega) = word width previous

theorem NodeStored.after_push {rowAddress previous offset : Nat} {heap : Array (Word width)}
    (stored : NodeStored rowAddress previous offset heap) (value : Word width) :
    NodeStored rowAddress previous offset (heap.push value) := by
  have first : offset < heap.size := by have := stored.fits; omega
  have second : offset + 1 < heap.size := by have := stored.fits; omega
  exact ⟨by have := stored.fits; simp only [Array.size_push]; omega,
    stored.rowFits, stored.previousFits, stored.offsetFits,
    (Array.getElem_push_lt first).trans stored.row,
    (Array.getElem_push_lt second).trans stored.next⟩

/-- Explicit fit fields make both link words exact natural pointers. -/
theorem NodeStored.row_value {rowAddress previous offset : Nat} {heap : Array (Word width)}
    (stored : NodeStored rowAddress previous offset heap) :
    (heap[offset]'(by have := stored.fits; omega)).val = rowAddress := by
  rw [stored.row]
  exact Nat.mod_eq_of_lt stored.rowFits

theorem NodeStored.next_value {rowAddress previous offset : Nat} {heap : Array (Word width)}
    (stored : NodeStored rowAddress previous offset heap) :
    (heap[offset + 1]'(by have := stored.fits; omega)).val = previous := by
  rw [stored.next]
  exact Nat.mod_eq_of_lt stored.previousFits

end Controller.Horn.WorklistStorage
