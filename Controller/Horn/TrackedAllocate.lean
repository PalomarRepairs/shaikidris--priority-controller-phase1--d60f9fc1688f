module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.InitializeCommon

@[expose] public section

/-! Zero allocation with an operational heap-end register. Register 7 is
incremented after each physical allocation; it identifies the next free cell
at every loop boundary. No semantic row-length or normalized-record list is
used to reconstruct that pointer. -/

namespace Controller.Horn.TrackedAllocate

open Controller.Cost
open Controller.Horn.Worklist.IndexedNormalize Controller.Horn.MarkStorage

/-- Only the counter, heap and control fields vary within the allocation loop. -/
def configuration (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) : State width 8 :=
  { template with
    reg := fun register => if register = 1 then word width remaining else if register = 7 then word width heap.size else template.reg register
    heap := heap
    pc := word width cursor
    halted := false }

def code (width entry : Nat) : Program width 8 :=
  #[.branchZero 1 (word width (entry + 5)), .allocate 2,
    .add 7 7 5, .add 1 1 6, .branchZero 2 (word width entry)]

@[simp] theorem code_size (width entry : Nat) : (code width entry).size = 5 := rfl

/-- Only the five fetched instructions are constrained; the exit belongs to
the continuation. -/
def CodeAt (destination : Program width 8) (entry : Nat) : Prop :=
  ∀ phase : Fin 5,
    destination[entry + phase.val]? = some (code width entry)[phase.val]

@[simp] theorem configuration_counter (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) :
    (configuration template heap remaining cursor).reg 1 = word width remaining := by
  simp [configuration]

@[simp] theorem configuration_other (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) (register : Fin 8) (different : register ≠ 1) (notPointer : register ≠ 7) :
    (configuration template heap remaining cursor).reg register = template.reg register := by
  simp [configuration, different, notPointer]

@[simp] theorem configuration_heap (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) : (configuration template heap remaining cursor).heap = heap := rfl

@[simp] theorem configuration_stack (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) : (configuration template heap remaining cursor).stack = template.stack := rfl

@[simp] theorem configuration_output (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) : (configuration template heap remaining cursor).output = template.output := rfl

@[simp] theorem configuration_running (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) : (configuration template heap remaining cursor).halted = false := rfl

@[simp] theorem configuration_liveWords (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) :
    (configuration template heap remaining cursor).liveWords =
      9 + heap.size + template.stack.length + template.output.length := by
  simp [configuration, State.liveWords]
  omega

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

theorem configuration_advance (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) (fits : cursor < 2 ^ width) :
    (configuration template heap remaining cursor).advance =
      configuration template heap remaining (cursor + 1) := by
  unfold State.advance configuration
  rw [word_val cursor fits]

theorem put_counter (template : State width 8) (heap : Array (Word width))
    (old next cursor : Nat) :
    (configuration template heap old cursor).put 1 (word width next) =
      configuration template heap next cursor := by
  unfold State.put configuration
  congr 1
  funext register
  by_cases counter : register = 1 <;> simp [counter]

theorem configuration_self (state : State width 8) (remaining cursor : Nat)
    (counter : state.reg 1 = word width remaining) (position : state.pc = word width cursor)
    (running : state.halted = false) (pointer : state.reg 7 = word width state.heap.size) :
    configuration state state.heap remaining cursor = state := by
  have registers : (fun register : Fin 8 =>
      if register = 1 then word width remaining else if register = 7 then word width state.heap.size else state.reg register) = state.reg := by
    funext register
    by_cases same : register = 1
    · subst register
      simp [counter]
    · by_cases endpoint : register = 7
      · subst register; simp [same, pointer]
      · simp [same, endpoint]
  unfold configuration
  rw [registers, ← position, ← running]

theorem configured_fetch (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (phase : Fin 5)
    (capacity : entry + 5 < 2 ^ width) :
    destination[(configuration template heap remaining (entry + phase.val)).pc.val]? =
      some (code width entry)[phase.val] := by
  change destination[(word width (entry + phase.val)).val]? = _
  rw [word_val (entry + phase.val) (by have := phase.isLt; omega)]
  exact present phase

private theorem step_at (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (phase : Fin 5)
    (capacity : entry + 5 < 2 ^ width) :
    programStep destination (configuration template heap remaining (entry + phase.val)) =
      step (code width entry)[phase.val] (configuration template heap remaining (entry + phase.val)) := by
  unfold programStep
  rw [configured_fetch destination entry present template heap remaining phase capacity]
  rfl

theorem check_positive (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat)
    (capacity : entry + 5 < 2 ^ width) (fits : remaining + 1 < 2 ^ width) :
    programStep destination (configuration template heap (remaining + 1) entry) =
      some (configuration template heap (remaining + 1) (entry + 1)) := by
  have fetched := step_at destination entry present template heap (remaining + 1) ⟨0, by decide⟩ capacity
  simp only [Nat.add_zero] at fetched
  rw [fetched]
  change step (.branchZero 1 (word width (entry + 5)))
    (configuration template heap (remaining + 1) entry) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_counter, word_val (remaining + 1) fits, Nat.succ_ne_zero]
  rw [configuration_advance template heap (remaining + 1) entry (by omega)]

/-- The allocation transition grows the heap before the pointer increment. -/
def allocated (template : State width 8) (heap : Array (Word width))
    (remaining entry : Nat) : State width 8 :=
  { (configuration template heap remaining (entry + 2)) with
    heap := heap.push (word width 0) }

@[simp] theorem allocated_liveWords (template : State width 8)
    (heap : Array (Word width)) (remaining entry : Nat) :
    (allocated template heap remaining entry).liveWords =
      9 + heap.size + 1 + template.stack.length + template.output.length := by
  simp [allocated, configuration, State.liveWords]
  omega

@[simp] theorem configuration_pointer (template : State width 8)
    (heap : Array (Word width)) (remaining cursor : Nat) :
    (configuration template heap remaining cursor).reg 7 = word width heap.size := by
  simp [configuration]

theorem allocate_zero (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (zero : template.reg 2 = word width 0)
    (capacity : entry + 5 < 2 ^ width) (fits : heap.size < 2 ^ width) :
    programStep destination (configuration template heap remaining (entry + 1)) =
      some (allocated template heap remaining entry) := by
  rw [step_at destination entry present template heap remaining ⟨1, by decide⟩ capacity]
  change step (.allocate 2) (configuration template heap remaining (entry + 1)) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_other template heap remaining (entry + 1) 2 (by decide) (by decide), zero]
  change (if heap.size < 2 ^ width then
    some { (configuration template heap remaining (entry + 1)).advance with
      heap := heap.push (word width 0) } else none) = _
  rw [ite_eq_left fits, configuration_advance template heap remaining (entry + 1) (by omega)]
  rfl

/-- The heap-end register advances through an actual fetched add instruction. -/
theorem increment_pointer (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (one : template.reg 5 = word width 1)
    (capacity : entry + 5 < 2 ^ width) (fits : heap.size + 1 < 2 ^ width) :
    programStep destination (allocated template heap remaining entry) =
      some (configuration template (heap.push (word width 0)) remaining (entry + 3)) := by
  have fetch := present ⟨2, by decide⟩
  change destination[entry + 2]? = some (.add 7 7 5) at fetch
  unfold programStep
  have position : (allocated template heap remaining entry).pc.val = entry + 2 := by
    exact word_val (width := width) (entry + 2) (by omega)
  rw [position, fetch]
  change step (.add 7 7 5) (allocated template heap remaining entry) = _
  have oneFits : 1 < 2 ^ width := by omega
  simp only [step, allocated, configuration_running, Bool.false_eq_true, ite_false,
    configuration_pointer,
    configuration_other template heap remaining (entry + 2) 5 (by decide) (by decide),
    one, word_val (width := width) heap.size (by omega), word_val (width := width) 1 oneFits]
  congr 1
  unfold State.put State.advance configuration
  simp only [word_val (width := width) (entry + 2) (by omega), Array.size_push,
    Nat.add_assoc, Nat.reduceAdd]
  congr 1
  funext register
  by_cases counter : register = 1
  · subst register; simp
  · by_cases pointer : register = 7
    · subst register; simp [word_val (width := width) heap.size (by omega)]
    · simp [counter, pointer]

theorem decrement_counter (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat)
    (decrement : template.reg 6 = word width (2 ^ width - 1))
    (capacity : entry + 5 < 2 ^ width) (fits : remaining + 1 < 2 ^ width) :
    programStep destination (configuration template heap (remaining + 1) (entry + 3)) =
      some (configuration template heap remaining (entry + 4)) := by
  rw [step_at destination entry present template heap (remaining + 1) ⟨3, by decide⟩ capacity]
  change step (.add 1 1 6) (configuration template heap (remaining + 1) (entry + 3)) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false, configuration_counter,
    configuration_other template heap (remaining + 1) (entry + 3) 6 (by decide) (by decide), decrement]
  rw [Initialize.word_decrement remaining fits,
    configuration_advance template heap (remaining + 1) (entry + 3) (by omega), put_counter]

theorem return_to_check (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (zero : template.reg 2 = word width 0)
    (capacity : entry + 5 < 2 ^ width) :
    programStep destination (configuration template heap remaining (entry + 4)) =
      some (configuration template heap remaining entry) := by
  rw [step_at destination entry present template heap remaining ⟨4, by decide⟩ capacity]
  change step (.branchZero 2 (word width entry))
    (configuration template heap remaining (entry + 4)) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_other template heap remaining (entry + 4) 2 (by decide) (by decide), zero,
    word_val 0 (Nat.two_pow_pos width), ite_true]
  rfl

theorem check_zero (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (capacity : entry + 5 < 2 ^ width) :
    programStep destination (configuration template heap 0 entry) =
      some (configuration template heap 0 (entry + 5)) := by
  have fetched := step_at destination entry present template heap 0 ⟨0, by decide⟩ capacity
  simp only [Nat.add_zero] at fetched
  rw [fetched]
  change step (.branchZero 1 (word width (entry + 5))) (configuration template heap 0 entry) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_counter, word_val 0 (Nat.two_pow_pos width), ite_true]
  rfl

/-- Exact allocation trace inside any program containing these five instructions.
Stack and output lengths are included in the peak storage measure. -/
theorem execution (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (length : Nat) (zero : template.reg 2 = word width 0)
    (decrement : template.reg 6 = word width (2 ^ width - 1))
    (one : template.reg 5 = word width 1)
    (capacity : entry + 5 < 2 ^ width) (fits : heap.size + length < 2 ^ width) :
    Execution destination (configuration template heap length entry)
      (configuration template (heap ++ Array.replicate length (word width 0)) 0 (entry + 5))
      (5 * length + 1) ((configuration template heap length entry).liveWords + length) := by
  induction length generalizing heap with
  | zero =>
      have trace := Execution.cons (check_zero destination entry present template heap capacity)
        (Execution.refl (configuration template heap 0 (entry + 5)))
      simpa [configuration_liveWords] using trace
  | succ length ih =>
      have counterFits : length + 1 < 2 ^ width := by omega
      have heapFits : heap.size < 2 ^ width := by omega
      have nextFits : (heap.push (word width 0)).size + length < 2 ^ width := by
        simp only [Array.size_push]
        omega
      have rest := ih (heap.push (word width 0)) nextFits
      have trace := Execution.cons (check_positive destination entry present template heap length capacity counterFits)
        (Execution.cons (allocate_zero destination entry present template heap (length + 1) zero capacity heapFits)
          (Execution.cons (increment_pointer destination entry present template heap
            (length + 1) one capacity (by omega))
          (Execution.cons (decrement_counter destination entry present template
            (heap.push (word width 0)) length decrement capacity counterFits)
            (Execution.cons (return_to_check destination entry present template
              (heap.push (word width 0)) length zero capacity) rest))))
      rw [Initialize.push_buffer] at trace
      convert trace using 1 <;> (try simp only [configuration_liveWords, allocated_liveWords, Array.size_push]) <;> omega

/-- Start at an arbitrary existing machine state satisfying the register and PC
invariants. No surrounding state is rebuilt or discarded. -/
theorem execution_from_state (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (state : State width 8) (length : Nat)
    (counter : state.reg 1 = word width length) (position : state.pc = word width entry)
    (running : state.halted = false) (pointer : state.reg 7 = word width state.heap.size)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (capacity : entry + 5 < 2 ^ width) (fits : state.heap.size + length < 2 ^ width) :
    Execution destination state
      (configuration state (state.heap ++ Array.replicate length (word width 0)) 0 (entry + 5))
      (5 * length + 1) (state.liveWords + length) := by
  simpa only [configuration_self state length entry counter position running pointer] using
    execution destination entry present state state.heap length zero decrement one capacity fits

/-- The endpoint pointer is a result of the traced allocation loop. -/
theorem final_pointer (template : State width 8) (heap : Array (Word width))
    (length entry : Nat) :
    (configuration template (heap ++ Array.replicate length (word width 0))
      0 (entry + 5)).reg 7 = word width (heap.size + length) := by
  simp [configuration]

/-- The allocator preserves the caller and every register except its counter
and operational heap-end pointer. The existing heap prefix is unchanged. -/
theorem final_frame (template : State width 8) (heap : Array (Word width))
    (length entry : Nat) :
    (∀ register : Fin 8, register ≠ 1 → register ≠ 7 →
      (configuration template (heap ++ Array.replicate length (word width 0))
        0 (entry + 5)).reg register = template.reg register) ∧
    (configuration template (heap ++ Array.replicate length (word width 0))
      0 (entry + 5)).stack = template.stack ∧
    (configuration template (heap ++ Array.replicate length (word width 0))
      0 (entry + 5)).output = template.output ∧
    (∀ index : Fin heap.size,
      (configuration template (heap ++ Array.replicate length (word width 0))
        0 (entry + 5)).heap[index.val]'(by simp; omega) = heap[index.val]) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro register notCounter notPointer
    exact configuration_other template _ 0 (entry + 5) register notCounter notPointer
  · exact Initialize.buffer_preserves heap length

end Controller.Horn.TrackedAllocate
