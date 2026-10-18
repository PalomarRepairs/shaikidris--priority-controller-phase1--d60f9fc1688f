module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.OutputProgram

@[expose] public section

/-! Fetched initialization of a contiguous heap region. A supplied word is
written to each fresh cell; allocation, program storage and existing state
are distinct from input decoding and sparse reuse. -/
namespace Controller.Cost.Initialize
open Controller.Cost.GateProgram

abbrev Code (width : Nat) := List (Instruction width 4)

def cell (value : Word width) : Code width := [.constant 0 value, .allocate 0]
def code (value : Word width) : Nat → Code width
  | 0 => []
  | count + 1 => cell value ++ code value count

@[simp] theorem code_length (value : Word width) (count : Nat) :
    (code value count).length = 2 * count := by
  induction count with
  | zero => simp [code]
  | succ count ih => simp [code, cell, ih]; omega

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : Nat) (instruction : Instruction width 4)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance (s : State width 4) (base : Nat)
    (pc : s.pc = word width base) (fits : base < 2 ^ width) :
    s.advance.pc = word width (base + 1) := by
  simp only [State.advance, pc]
  rw [show (word width base).val = base from Nat.mod_eq_of_lt fits]

/-- Two genuine fetched instructions initialize one fresh heap cell. -/
theorem cell_execution (program : Program width 4) (s : State width 4)
    (value : Word width) (base : Nat) (pc : s.pc = word width base)
    (running : s.halted = false) (fits : base + 2 < 2 ^ width)
    (room : s.heap.size < 2 ^ width) (block : BlockAt program base (cell value)) :
    ∃ final, Execution program s final 2 (s.liveWords + 1) ∧
      final.heap = s.heap.push value ∧ final.stack = s.stack ∧
      final.output = s.output ∧ final.pc = word width (base + 2) ∧
      final.halted = false := by
  let middle := s.advance.put 0 value
  let final := { middle.advance with heap := s.heap.push value }
  have middlePC : middle.pc = word width (base + 1) := advance s base pc (by omega)
  have first : programStep program s = some middle := by
    rw [fetched program s base (.constant 0 value) pc (by omega)
      (by simpa [cell] using block 0 (by simp [cell]))]
    simp [step, running, middle]
  have second : programStep program middle = some final := by
    rw [fetched program middle (base + 1) (.allocate 0) middlePC (by omega)
      (by simpa [cell] using block 1 (by simp [cell]))]
    simp [step, middle, final, State.put, State.advance, running, room]
  have middleLive : middle.liveWords = s.liveWords := rfl
  have finalLive : final.liveWords = s.liveWords + 1 := by
    simp [final, middle, State.put, State.advance, State.liveWords]; omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, running⟩
  · have trace := Execution.cons first (Execution.cons second (Execution.refl final))
    simpa only [middleLive, finalLive, Nat.zero_add, Nat.add_zero,
      show max s.liveWords (s.liveWords + 1) = s.liveWords + 1 by omega] using trace
  · change middle.advance.pc = word width (base + 2)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using advance middle (base + 1) middlePC (by omega)

/-- The actual initializer charges every allocated word and preserves old state. -/
theorem code_execution (program : Program width 4) (s : State width 4)
    (value : Word width) (base count : Nat) (pc : s.pc = word width base)
    (running : s.halted = false) (fits : base + 2 * count < 2 ^ width)
    (room : s.heap.size + count ≤ 2 ^ width)
    (block : BlockAt program base (code value count)) :
    ∃ final, Execution program s final (2 * count) (s.liveWords + count) ∧
      final.heap = s.heap ++ (List.replicate count value).toArray ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 2 * count) ∧ final.halted = false := by
  induction count generalizing s base with
  | zero =>
    refine ⟨s, ?_, ?_, rfl, rfl, ?_, running⟩
    · simpa using Execution.refl (p := program) s
    · simp
    · simpa using pc
  | succ count ih =>
    have head := BlockAt.prefix program base (cell value) (code value count) block
    obtain ⟨middle, first, heap, stack, output, position, active⟩ :=
      cell_execution program s value base pc running (by omega) (by omega) head
    have tail : BlockAt program (base + 2) (code value count) := by
      simpa [cell] using BlockAt.suffix program base (cell value) (code value count) block
    obtain ⟨final, rest, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
      ih middle (base + 2) position active (by omega)
        (by rw [heap]; simp only [Array.size_push]; omega) tail
    have middleLive : middle.liveWords = s.liveWords + 1 := by
      simp only [State.liveWords, heap, stack, output, Array.size_push]; omega
    refine ⟨final, ?_, ?_, finalStack.trans stack, finalOutput.trans output, ?_, finalRunning⟩
    · have trace := first.append rest
      rw [middleLive] at trace
      convert trace using 1 <;> omega
    · rw [finalHeap, heap]
      apply Array.toList_inj.mp
      simp [List.replicate_succ, List.append_assoc]
    · simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC

def program (value : Word width) (count : Nat) : Program width 4 :=
  (code value count).toArray

@[simp] theorem programWords_eq (value : Word width) (count : Nat) :
    programWords (program value count) = 8 * count := by
  simp [programWords, program]; omega

/-- The freshly stored initializer includes its resident instruction storage. -/
theorem stored_execution (s : State width 4) (value : Word width) (count : Nat)
    (pc : s.pc = word width 0) (running : s.halted = false)
    (fits : 2 * count < 2 ^ width) (room : s.heap.size + count ≤ 2 ^ width) :
    ∃ final, Execution (program value count) s final (2 * count) (s.liveWords + count) ∧
      final.heap = s.heap ++ (List.replicate count value).toArray ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      programWords (program value count) + (s.liveWords + count) = s.liveWords + 9 * count := by
  have block : BlockAt (program value count) 0 (code value count) := by
    intro offset bound
    simp [program, List.getElem?_toArray, List.getElem?_eq_getElem bound]
  obtain ⟨final, trace, heap, stack, output, _, _⟩ :=
    code_execution (program value count) s value 0 count pc running (by simpa using fits) room block
  exact ⟨final, trace, heap, stack, output, by rw [programWords_eq]; omega⟩

end Controller.Cost.Initialize
