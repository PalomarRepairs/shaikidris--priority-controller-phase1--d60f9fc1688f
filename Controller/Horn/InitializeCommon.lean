module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.MarkStorage

@[expose] public section

/-!
# Zero allocation in the common eight-register machine

The allocator uses counter register 1, zero register 2 and decrement register 6.
The four fetched instructions are relocatable and end at a continuation without
halting. All other registers, the stack, output and existing heap prefix are
preserved. The same register convention is used by the touched-label reset loop.
-/

namespace Controller.Horn.InitializeCommon

open Controller.Cost
open Controller.Horn.Worklist.IndexedNormalize Controller.Horn.MarkStorage

/-- Only the counter, heap and control fields vary within the allocation loop. -/
def configuration (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) : State width 8 :=
  { template with
    reg := fun register => if register = 1 then word width remaining else template.reg register
    heap := heap
    pc := word width cursor
    halted := false }

def code (width entry : Nat) : Program width 8 :=
  #[.branchZero 1 (word width (entry + 4)), .allocate 2,
    .add 1 1 6, .branchZero 2 (word width entry)]

@[simp] theorem code_size (width entry : Nat) : (code width entry).size = 4 := rfl

/-- Only the four fetched instructions are constrained; the exit belongs to
the continuation. -/
def CodeAt (destination : Program width 8) (entry : Nat) : Prop :=
  ∀ phase : Fin 4,
    destination[entry + phase.val]? = some (code width entry)[phase.val]

@[simp] theorem configuration_counter (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) :
    (configuration template heap remaining cursor).reg 1 = word width remaining := by
  simp [configuration]

@[simp] theorem configuration_other (template : State width 8) (heap : Array (Word width))
    (remaining cursor : Nat) (register : Fin 8) (different : register ≠ 1) :
    (configuration template heap remaining cursor).reg register = template.reg register := by
  simp [configuration, different]

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
    (running : state.halted = false) :
    configuration state state.heap remaining cursor = state := by
  have registers : (fun register : Fin 8 =>
      if register = 1 then word width remaining else state.reg register) = state.reg := by
    funext register
    by_cases same : register = 1
    · subst register
      simp [counter]
    · simp [same]
  unfold configuration
  rw [registers, ← position, ← running]

theorem configured_fetch (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (phase : Fin 4)
    (capacity : entry + 4 < 2 ^ width) :
    destination[(configuration template heap remaining (entry + phase.val)).pc.val]? =
      some (code width entry)[phase.val] := by
  change destination[(word width (entry + phase.val)).val]? = _
  rw [word_val (entry + phase.val) (by have := phase.isLt; omega)]
  exact present phase

private theorem step_at (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (phase : Fin 4)
    (capacity : entry + 4 < 2 ^ width) :
    programStep destination (configuration template heap remaining (entry + phase.val)) =
      step (code width entry)[phase.val] (configuration template heap remaining (entry + phase.val)) := by
  unfold programStep
  rw [configured_fetch destination entry present template heap remaining phase capacity]
  rfl

theorem check_positive (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat)
    (capacity : entry + 4 < 2 ^ width) (fits : remaining + 1 < 2 ^ width) :
    programStep destination (configuration template heap (remaining + 1) entry) =
      some (configuration template heap (remaining + 1) (entry + 1)) := by
  have fetched := step_at destination entry present template heap (remaining + 1) ⟨0, by decide⟩ capacity
  simp only [Nat.add_zero] at fetched
  rw [fetched]
  change step (.branchZero 1 (word width (entry + 4)))
    (configuration template heap (remaining + 1) entry) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_counter, word_val (remaining + 1) fits, Nat.succ_ne_zero]
  rw [configuration_advance template heap (remaining + 1) entry (by omega)]

theorem allocate_zero (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (zero : template.reg 2 = word width 0)
    (capacity : entry + 4 < 2 ^ width) (fits : heap.size < 2 ^ width) :
    programStep destination (configuration template heap remaining (entry + 1)) =
      some (configuration template (heap.push (word width 0)) remaining (entry + 2)) := by
  rw [step_at destination entry present template heap remaining ⟨1, by decide⟩ capacity]
  change step (.allocate 2) (configuration template heap remaining (entry + 1)) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_other template heap remaining (entry + 1) 2 (by decide), zero]
  change (if heap.size < 2 ^ width then
    some { (configuration template heap remaining (entry + 1)).advance with
      heap := heap.push (word width 0) } else none) = _
  rw [ite_eq_left fits, configuration_advance template heap remaining (entry + 1) (by omega)]
  rfl

theorem decrement_counter (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat)
    (decrement : template.reg 6 = word width (2 ^ width - 1))
    (capacity : entry + 4 < 2 ^ width) (fits : remaining + 1 < 2 ^ width) :
    programStep destination (configuration template heap (remaining + 1) (entry + 2)) =
      some (configuration template heap remaining (entry + 3)) := by
  rw [step_at destination entry present template heap (remaining + 1) ⟨2, by decide⟩ capacity]
  change step (.add 1 1 6) (configuration template heap (remaining + 1) (entry + 2)) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false, configuration_counter,
    configuration_other template heap (remaining + 1) (entry + 2) 6 (by decide), decrement]
  rw [Initialize.word_decrement remaining fits,
    configuration_advance template heap (remaining + 1) (entry + 2) (by omega), put_counter]

theorem return_to_check (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (remaining : Nat) (zero : template.reg 2 = word width 0)
    (capacity : entry + 4 < 2 ^ width) :
    programStep destination (configuration template heap remaining (entry + 3)) =
      some (configuration template heap remaining entry) := by
  rw [step_at destination entry present template heap remaining ⟨3, by decide⟩ capacity]
  change step (.branchZero 2 (word width entry))
    (configuration template heap remaining (entry + 3)) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_other template heap remaining (entry + 3) 2 (by decide), zero,
    word_val 0 (Nat.two_pow_pos width), ite_true]
  rfl

theorem check_zero (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (capacity : entry + 4 < 2 ^ width) :
    programStep destination (configuration template heap 0 entry) =
      some (configuration template heap 0 (entry + 4)) := by
  have fetched := step_at destination entry present template heap 0 ⟨0, by decide⟩ capacity
  simp only [Nat.add_zero] at fetched
  rw [fetched]
  change step (.branchZero 1 (word width (entry + 4))) (configuration template heap 0 entry) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_counter, word_val 0 (Nat.two_pow_pos width), ite_true]
  rfl

/-- Exact allocation trace inside any program containing these four instructions.
Stack and output lengths are included in the peak storage measure. -/
theorem execution (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (length : Nat) (zero : template.reg 2 = word width 0)
    (decrement : template.reg 6 = word width (2 ^ width - 1))
    (capacity : entry + 4 < 2 ^ width) (fits : heap.size + length < 2 ^ width) :
    Execution destination (configuration template heap length entry)
      (configuration template (heap ++ Array.replicate length (word width 0)) 0 (entry + 4))
      (4 * length + 1) ((configuration template heap length entry).liveWords + length) := by
  induction length generalizing heap with
  | zero =>
      have trace := Execution.cons (check_zero destination entry present template heap capacity)
        (Execution.refl (configuration template heap 0 (entry + 4)))
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
          (Execution.cons (decrement_counter destination entry present template
            (heap.push (word width 0)) length decrement capacity counterFits)
            (Execution.cons (return_to_check destination entry present template
              (heap.push (word width 0)) length zero capacity) rest)))
      rw [Initialize.push_buffer] at trace
      convert trace using 1 <;> (try simp only [configuration_liveWords, Array.size_push]) <;> omega

/-- Start at an arbitrary existing machine state satisfying the register and PC
invariants. No surrounding state is rebuilt or discarded. -/
theorem execution_from_state (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (state : State width 8) (length : Nat)
    (counter : state.reg 1 = word width length) (position : state.pc = word width entry)
    (running : state.halted = false) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (capacity : entry + 4 < 2 ^ width) (fits : state.heap.size + length < 2 ^ width) :
    Execution destination state
      (configuration state (state.heap ++ Array.replicate length (word width 0)) 0 (entry + 4))
      (4 * length + 1) (state.liveWords + length) := by
  simpa only [configuration_self state length entry counter position running] using
    execution destination entry present state state.heap length zero decrement capacity fits

/-- All non-counter registers and existing stack/output cells survive allocation. -/
theorem frame (template : State width 8) (heap : Array (Word width)) (length entry : Nat) :
    (∀ register : Fin 8, register ≠ 1 →
      (configuration template (heap ++ Array.replicate length (word width 0)) 0 (entry + 4)).reg register =
        template.reg register) ∧
    (configuration template (heap ++ Array.replicate length (word width 0)) 0 (entry + 4)).stack = template.stack ∧
    (configuration template (heap ++ Array.replicate length (word width 0)) 0 (entry + 4)).output = template.output ∧
    (∀ index : Fin heap.size,
      (configuration template (heap ++ Array.replicate length (word width 0)) 0 (entry + 4)).heap[index.val]'(by simp; omega) =
        heap[index.val]) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro register different
    exact configuration_other template _ 0 (entry + 4) register different
  · exact Initialize.buffer_preserves heap length

/-- The common-register allocator initializes both marks for every declared channel. -/
theorem marks_execution (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (n : Nat) (zero : template.reg 2 = word width 0)
    (decrement : template.reg 6 = word width (2 ^ width - 1))
    (capacity : entry + 4 < 2 ^ width) (fits : heap.size + 2 * n < 2 ^ width) :
    Execution destination (configuration template heap (2 * n) entry)
      (configuration template (heap ++ Array.replicate (2 * n) (word width 0)) 0 (entry + 4))
      (8 * n + 1) ((configuration template heap (2 * n) entry).liveWords + 2 * n) ∧
    Stored (Marks.initial n) heap.size
      (configuration template (heap ++ Array.replicate (2 * n) (word width 0)) 0 (entry + 4)).heap := by
  constructor
  · simpa only [← Nat.mul_assoc, Nat.reduceMul] using
      execution destination entry present template heap (2 * n) zero decrement capacity fits
  · exact initial_stored heap n

/-- Composition uses a real continuation from the exact final machine state. -/
theorem execution_with_continuation (destination : Program width 8) (entry : Nat)
    (present : CodeAt destination entry) (template : State width 8)
    (heap : Array (Word width)) (length : Nat) (zero : template.reg 2 = word width 0)
    (decrement : template.reg 6 = word width (2 ^ width - 1))
    (capacity : entry + 4 < 2 ^ width) (fits : heap.size + length < 2 ^ width)
    (final : State width 8) (ticks peak : Nat)
    (continuation : Execution destination
      (configuration template (heap ++ Array.replicate length (word width 0)) 0 (entry + 4)) final ticks peak) :
    Execution destination (configuration template heap length entry) final
      (4 * length + 1 + ticks) (max ((configuration template heap length entry).liveWords + length) peak) :=
  (execution destination entry present template heap length zero decrement capacity fits).append continuation

end Controller.Horn.InitializeCommon
