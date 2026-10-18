module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Refinement

@[expose] public section

/-!
# A fixed zero-buffer allocation program

The program appends a zero-filled region to an existing heap. Its initial
registers contain only the requested length and the constants zero and minus
one. The execution theorem counts the fetched branches, allocations and
decrements, including the zero-length case. This is an initialization fragment;
the Horn solver's complete layout and instruction simulation are separate.
-/

namespace Controller.Horn.Initialize

open Controller.Cost

/-- Registers hold the remaining length, zero and the modular decrement. -/
def configuration (heap : Array (Word width)) (remaining cursor : Nat) : State width 3 where
  reg := fun register =>
    if register = 0 then word width remaining
    else if register = 1 then word width 0
    else word width (2 ^ width - 1)
  heap := heap
  stack := []
  output := []
  pc := word width cursor
  halted := false

/-- The same five instructions work for every heap and requested length. -/
def program (width : Nat) : Program width 3 :=
  #[.branchZero 0 (word width 4), .allocate 1, .add 0 0 2,
    .branchZero 1 (word width 0), .halt]

@[simp] theorem program_size (width : Nat) : (program width).size = 5 := rfl

@[simp] theorem configuration_counter (heap : Array (Word width)) (remaining cursor : Nat) :
    (configuration heap remaining cursor).reg 0 = word width remaining := by
  simp [configuration]

@[simp] theorem configuration_zero (heap : Array (Word width)) (remaining cursor : Nat) :
    (configuration heap remaining cursor).reg 1 = word width 0 := by
  simp [configuration]

@[simp] theorem configuration_decrement (heap : Array (Word width)) (remaining cursor : Nat) :
    (configuration heap remaining cursor).reg 2 = word width (2 ^ width - 1) := by
  simp [configuration]

@[simp] theorem configuration_running (heap : Array (Word width)) (remaining cursor : Nat) :
    (configuration heap remaining cursor).halted = false := rfl

@[simp] theorem configuration_liveWords (heap : Array (Word width)) (remaining cursor : Nat) :
    (configuration heap remaining cursor).liveWords = 4 + heap.size := by
  simp [configuration, State.liveWords]
  omega

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

theorem configuration_advance (heap : Array (Word width)) (remaining cursor : Nat)
    (fits : cursor < 2 ^ width) :
    (configuration heap remaining cursor).advance = configuration heap remaining (cursor + 1) := by
  unfold State.advance configuration
  rw [word_val cursor fits]

theorem configuration_put_counter (heap : Array (Word width)) (old next cursor : Nat) :
    (configuration heap old cursor).put 0 (word width next) =
      configuration heap next cursor := by
  unfold State.put configuration
  congr 1
  funext register
  by_cases counter : register = 0 <;> simp [counter]

/-- The positive counter branch uses modular addition without natural-number
underflow. It is never invoked for the zero counter. -/
theorem word_decrement (remaining : Nat) (fits : remaining + 1 < 2 ^ width) :
    word width ((word width (remaining + 1)).val +
      (word width (2 ^ width - 1)).val) = word width remaining := by
  have positive := Nat.two_pow_pos width
  have decrementFits : 2 ^ width - 1 < 2 ^ width := by omega
  rw [word_val (remaining + 1) fits, word_val (2 ^ width - 1) decrementFits]
  have arithmetic : remaining + 1 + (2 ^ width - 1) = remaining + 2 ^ width := by omega
  apply Fin.ext
  change (remaining + 1 + (2 ^ width - 1)) % (2 ^ width) = remaining % (2 ^ width)
  rw [arithmetic, Nat.add_mod_right]

theorem check_positive (heap : Array (Word width)) (remaining : Nat)
    (capacity : 5 < 2 ^ width) (fits : remaining + 1 < 2 ^ width) :
    programStep (program width) (configuration heap (remaining + 1) 0) =
      some (configuration heap (remaining + 1) 1) := by
  have fetched : (program width)[(configuration heap (remaining + 1) 0).pc.val]? =
      some (.branchZero 0 (word width 4)) := by
    simp [program, configuration, word]
  unfold programStep
  rw [fetched]
  change step (.branchZero 0 (word width 4)) (configuration heap (remaining + 1) 0) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_counter, word_val (remaining + 1) fits, Nat.succ_ne_zero]
  rw [configuration_advance heap (remaining + 1) 0 (by omega)]

theorem allocate_zero (heap : Array (Word width)) (remaining : Nat)
    (capacity : 5 < 2 ^ width) (fits : heap.size < 2 ^ width) :
    programStep (program width) (configuration heap remaining 1) =
      some (configuration (heap.push (word width 0)) remaining 2) := by
  have fetched : (program width)[(configuration heap remaining 1).pc.val]? =
      some (.allocate 1) := by
    simp [program, configuration, word, Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)]
  unfold programStep
  rw [fetched]
  change step (.allocate 1) (configuration heap remaining 1) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_zero]
  change (if heap.size < 2 ^ width then
    some { (configuration heap remaining 1).advance with heap := heap.push (word width 0) }
    else none) = _
  rw [ite_eq_left fits, configuration_advance heap remaining 1 (by omega)]
  rfl

theorem decrement_counter (heap : Array (Word width)) (remaining : Nat)
    (capacity : 5 < 2 ^ width) (fits : remaining + 1 < 2 ^ width) :
    programStep (program width) (configuration heap (remaining + 1) 2) =
      some (configuration heap remaining 3) := by
  have fetched : (program width)[(configuration heap (remaining + 1) 2).pc.val]? =
      some (.add 0 0 2) := by
    simp [program, configuration, word, Nat.mod_eq_of_lt (show 2 < 2 ^ width by omega)]
  unfold programStep
  rw [fetched]
  change step (.add 0 0 2) (configuration heap (remaining + 1) 2) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_counter, configuration_decrement]
  rw [word_decrement remaining fits, configuration_advance heap (remaining + 1) 2 (by omega),
    configuration_put_counter]

theorem return_to_check (heap : Array (Word width)) (remaining : Nat)
    (capacity : 5 < 2 ^ width) :
    programStep (program width) (configuration heap remaining 3) =
      some (configuration heap remaining 0) := by
  have fetched : (program width)[(configuration heap remaining 3).pc.val]? =
      some (.branchZero 1 (word width 0)) := by
    simp [program, configuration, word, Nat.mod_eq_of_lt (show 3 < 2 ^ width by omega)]
  unfold programStep
  rw [fetched]
  change step (.branchZero 1 (word width 0)) (configuration heap remaining 3) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_zero, word_val 0 (Nat.two_pow_pos width), ite_true]
  rfl

theorem check_zero (heap : Array (Word width)) (_capacity : 5 < 2 ^ width) :
    programStep (program width) (configuration heap 0 0) =
      some (configuration heap 0 4) := by
  have fetched : (program width)[(configuration heap 0 0).pc.val]? =
      some (.branchZero 0 (word width 4)) := by
    simp [program, configuration, word]
  unfold programStep
  rw [fetched]
  change step (.branchZero 0 (word width 4)) (configuration heap 0 0) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false,
    configuration_counter, word_val 0 (Nat.two_pow_pos width), ite_true]
  rfl

theorem halt (heap : Array (Word width)) (capacity : 5 < 2 ^ width) :
    programStep (program width) (configuration heap 0 4) =
      some { configuration heap 0 5 with halted := true } := by
  have fetched : (program width)[(configuration heap 0 4).pc.val]? = some .halt := by
    simp [program, configuration, word, Nat.mod_eq_of_lt (show 4 < 2 ^ width by omega)]
  unfold programStep
  rw [fetched]
  change step .halt (configuration heap 0 4) = _
  simp only [step, configuration_running, Bool.false_eq_true, ite_false]
  rw [configuration_advance heap 0 4 (by omega)]

theorem push_buffer (heap : Array (Word width)) (length : Nat) :
    (heap.push (word width 0)) ++ Array.replicate length (word width 0) =
      heap ++ Array.replicate (length + 1) (word width 0) := by
  rw [Array.push_eq_append, Array.append_assoc, ← Array.replicate_succ']

/-- The actual program runs four instructions per allocated word, followed by
the zero branch and halt. Program storage is accounted for separately below. -/
theorem execution (heap : Array (Word width)) (length : Nat)
    (capacity : 5 < 2 ^ width) (fits : heap.size + length < 2 ^ width) :
    Execution (program width) (configuration heap length 0)
      { configuration (heap ++ Array.replicate length (word width 0)) 0 5 with halted := true }
      (4 * length + 2) ((configuration heap length 0).liveWords + length) := by
  induction length generalizing heap with
  | zero =>
    have trace := Execution.cons (check_zero heap capacity)
      (Execution.cons (halt heap capacity)
        (Execution.refl { configuration heap 0 5 with halted := true }))
    simpa [configuration, State.liveWords] using trace
  | succ length ih =>
    have counterFits : length + 1 < 2 ^ width := by omega
    have heapFits : heap.size < 2 ^ width := by omega
    have nextFits : (heap.push (word width 0)).size + length < 2 ^ width := by
      simp only [Array.size_push]
      omega
    have tail := ih (heap.push (word width 0)) nextFits
    have trace := Execution.cons (check_positive heap length capacity counterFits)
      (Execution.cons (allocate_zero heap (length + 1) capacity heapFits)
        (Execution.cons (decrement_counter (heap.push (word width 0)) length capacity counterFits)
          (Execution.cons (return_to_check (heap.push (word width 0)) length capacity) tail)))
    rw [push_buffer] at trace
    convert trace using 1 <;> (try simp only [configuration_liveWords, Array.size_push]) <;> omega

/-- The initial heap prefix is retained verbatim. -/
theorem buffer_preserves (heap : Array (Word width)) (length : Nat) (index : Fin heap.size) :
    (heap ++ Array.replicate length (word width 0))[index.val]'(by simp; omega) = heap[index.val] := by
  exact Array.getElem_append_left index.isLt

/-- Every new cell decodes to zero, including cells never used by a clause. -/
theorem buffer_zero (heap : Array (Word width)) (length : Nat) (index : Fin length) :
    (heap ++ Array.replicate length (word width 0))[heap.size + index.val]'(by simp) =
      word width 0 := by
  rw [Array.getElem_append_right' heap (by simp)]
  simp

theorem initial_representable (heap : Array (Word width)) (length : Nat)
    (capacity : 5 < 2 ^ width) (fits : heap.size + length < 2 ^ width) :
    Representable (program width) (configuration heap length 0) := by
  change 3 ≤ 2 ^ width ∧ 5 ≤ 2 ^ width ∧ heap.size ≤ 2 ^ width
  omega

theorem final_representable (heap : Array (Word width)) (length : Nat)
    (capacity : 5 < 2 ^ width) (fits : heap.size + length < 2 ^ width) :
    Representable (program width)
      { configuration (heap ++ Array.replicate length (word width 0)) 0 5 with halted := true } := by
  change 3 ≤ 2 ^ width ∧ 5 ≤ 2 ^ width ∧
    (heap ++ Array.replicate length (word width 0)).size ≤ 2 ^ width
  simp only [Array.size_append, Array.size_replicate]
  omega

/-- Five instructions, three registers and the program counter add 24 words.
The empty stack and output consume no words during this allocation fragment. -/
theorem peak_resident_words (heap : Array (Word width)) (length : Nat) :
    programWords (program width) + (configuration heap length 0).liveWords + length =
      24 + heap.size + length := by
  simp [programWords, configuration_liveWords]
  omega

theorem peak_resident_bits (heap : Array (Word width)) (length : Nat) :
    width * (programWords (program width) + (configuration heap length 0).liveWords + length) =
      width * (24 + heap.size + length) := by
  rw [peak_resident_words]

/-- Only the four loop instructions are fixed. In particular, instruction 4
belongs to the continuation and need not be a halt. -/
def LoopAgreement (destination : Program width 3) : Prop :=
  ∀ cursor : Fin 4, destination[cursor.val]? = (program width)[cursor.val]?

/-- Instruction agreement preserves the fetched transition itself. -/
theorem programStep_agrees (destination : Program width 3)
    (agreement : LoopAgreement destination) (state : State width 3)
    (within : state.pc.val < 4) :
    programStep destination state = programStep (program width) state := by
  unfold programStep
  rw [agreement ⟨state.pc.val, within⟩]

/-- A loop transition can be replayed inside any program with the same loop
prefix. No hypothesis about its result or instruction count is introduced. -/
theorem replay_transition (destination : Program width 3)
    (agreement : LoopAgreement destination) (heap : Array (Word width))
    (remaining cursor : Nat) (within : cursor < 4) (capacity : 5 < 2 ^ width)
    {next : State width 3}
    (transition : programStep (program width) (configuration heap remaining cursor) = some next) :
    programStep destination (configuration heap remaining cursor) = some next := by
  have cursorBound : (configuration heap remaining cursor).pc.val < 4 := by
    change (word width cursor).val < 4
    rw [word_val cursor (by omega)]
    exact within
  rw [programStep_agrees destination agreement _ cursorBound]
  exact transition

/-- The replayed loop exits at PC 4 while still running. Its continuation is
part of the same program and has not yet executed an instruction. -/
theorem loop_execution (destination : Program width 3)
    (agreement : LoopAgreement destination) (heap : Array (Word width)) (length : Nat)
    (capacity : 5 < 2 ^ width) (fits : heap.size + length < 2 ^ width) :
    Execution destination (configuration heap length 0)
      (configuration (heap ++ Array.replicate length (word width 0)) 0 4)
      (4 * length + 1) ((configuration heap length 0).liveWords + length) := by
  induction length generalizing heap with
  | zero =>
    have first := replay_transition destination agreement heap 0 0 (by decide) capacity
      (check_zero heap capacity)
    have trace := Execution.cons first (Execution.refl (configuration heap 0 4))
    simpa [configuration, State.liveWords] using trace
  | succ length ih =>
    have counterFits : length + 1 < 2 ^ width := by omega
    have heapFits : heap.size < 2 ^ width := by omega
    have nextFits : (heap.push (word width 0)).size + length < 2 ^ width := by
      simp only [Array.size_push]
      omega
    have tail := ih (heap.push (word width 0)) nextFits
    have first := replay_transition destination agreement heap (length + 1) 0
      (by decide) capacity (check_positive heap length capacity counterFits)
    have second := replay_transition destination agreement heap (length + 1) 1
      (by decide) capacity (allocate_zero heap (length + 1) capacity heapFits)
    have third := replay_transition destination agreement (heap.push (word width 0))
      (length + 1) 2 (by decide) capacity
      (decrement_counter (heap.push (word width 0)) length capacity counterFits)
    have fourth := replay_transition destination agreement (heap.push (word width 0))
      length 3 (by decide) capacity
      (return_to_check (heap.push (word width 0)) length capacity)
    have trace := Execution.cons first
      (Execution.cons second (Execution.cons third (Execution.cons fourth tail)))
    rw [push_buffer] at trace
    convert trace using 1 <;> (try simp only [configuration_liveWords, Array.size_push]) <;> omega

/-- Even in the standalone program, allocation can be proved up to the
continuation boundary before its final halt instruction is executed. -/
theorem execution_to_exit (heap : Array (Word width)) (length : Nat)
    (capacity : 5 < 2 ^ width) (fits : heap.size + length < 2 ^ width) :
    Execution (program width) (configuration heap length 0)
      (configuration (heap ++ Array.replicate length (word width 0)) 0 4)
      (4 * length + 1) ((configuration heap length 0).liveWords + length) :=
  loop_execution (program width) (fun _ => rfl) heap length capacity fits

/-- Composition retains the destination program and genuine intermediate
machine state; the continuation is charged by its own actual execution. -/
theorem execution_with_continuation (destination : Program width 3)
    (agreement : LoopAgreement destination) (heap : Array (Word width)) (length : Nat)
    (capacity : 5 < 2 ^ width) (fits : heap.size + length < 2 ^ width)
    {final : State width 3} {ticks peak : Nat}
    (continuation : Execution destination
      (configuration (heap ++ Array.replicate length (word width 0)) 0 4) final ticks peak) :
    Execution destination (configuration heap length 0) final (4 * length + 1 + ticks)
      (max ((configuration heap length 0).liveWords + length) peak) :=
  (loop_execution destination agreement heap length capacity fits).append continuation

end Controller.Horn.Initialize
