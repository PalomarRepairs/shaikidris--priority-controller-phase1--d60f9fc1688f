module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Initialize

@[expose] public section

/-! Fetched loading of supplied input words from a stack into fresh heap cells.
The input words are already represented; parsing external bytes is separate.
Every pop and allocation is charged, and the input storage is included in peak. -/
namespace Controller.Cost.InputLoad
open Controller.Cost.GateProgram
abbrev Code (width : Nat) := List (Instruction width 4)
def cell : Code width := [.pop 0, .allocate 0]
def code : Nat → Code width
  | 0 => []
  | count + 1 => cell ++ code count
@[simp] theorem code_length (count : Nat) : (code (width := width) count).length = 2 * count := by
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

/-- Loading transfers a represented word rather than creating another live word. -/
theorem cell_execution (program : Program width 4) (s : State width 4)
    (value : Word width) (rest : List (Word width)) (base : Nat)
    (pc : s.pc = word width base) (running : s.halted = false)
    (input : s.stack = value :: rest) (fits : base + 2 < 2 ^ width)
    (room : s.heap.size < 2 ^ width) (block : BlockAt program base cell) :
    ∃ final, Execution program s final 2 s.liveWords ∧
      final.heap = s.heap.push value ∧ final.stack = rest ∧
      final.output = s.output ∧ final.pc = word width (base + 2) ∧
      final.halted = false := by
  let middle := { s.advance.put 0 value with stack := rest }
  let final := { middle.advance with heap := s.heap.push value }
  have middlePC : middle.pc = word width (base + 1) := advance s base pc (by omega)
  have first : programStep program s = some middle := by
    rw [fetched program s base (.pop 0) pc (by omega)
      (by simpa [cell] using block 0 (by simp [cell]))]
    simp [step, running, input, middle]
  have second : programStep program middle = some final := by
    rw [fetched program middle (base + 1) (.allocate 0) middlePC (by omega)
      (by simpa [cell] using block 1 (by simp [cell]))]
    simp [step, middle, final, State.put, State.advance, running, room]
  have middleLive : middle.liveWords + 1 = s.liveWords := by
    simp [middle, State.liveWords, State.put, State.advance, input]; omega
  have finalLive : final.liveWords = s.liveWords := by
    simp [final, middle, State.liveWords, State.put, State.advance, input]; omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, running⟩
  · have trace := Execution.cons first (Execution.cons second (Execution.refl final))
    convert trace using 1 <;> omega
  · change middle.advance.pc = word width (base + 2)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using advance middle (base + 1) middlePC (by omega)

/-- Arbitrary supplied words are loaded in order, preserving the retained suffix. -/
theorem code_execution (program : Program width 4) (s : State width 4)
    (values suffix : List (Word width)) (base : Nat)
    (pc : s.pc = word width base) (running : s.halted = false)
    (input : s.stack = values ++ suffix)
    (fits : base + 2 * values.length < 2 ^ width)
    (room : s.heap.size + values.length ≤ 2 ^ width)
    (block : BlockAt program base (code values.length)) :
    ∃ final, Execution program s final (2 * values.length) s.liveWords ∧
      final.heap = s.heap ++ values.toArray ∧ final.stack = suffix ∧
      final.output = s.output ∧ final.pc = word width (base + 2 * values.length) ∧
      final.halted = false := by
  induction values generalizing s base with
  | nil =>
    refine ⟨s, ?_, ?_, ?_, rfl, ?_, running⟩
    · simpa using Execution.refl (p := program) s
    · simp
    · simpa using input
    · simpa using pc
  | cons value values ih =>
    have head := BlockAt.prefix program base cell (code values.length) block
    obtain ⟨middle, first, heap, stack, output, position, active⟩ :=
      cell_execution program s value (values ++ suffix) base pc running input
        (by simp only [List.length_cons] at fits; omega)
        (by simp only [List.length_cons] at room; omega) head
    have tail : BlockAt program (base + 2) (code values.length) := by
      simpa [cell] using BlockAt.suffix program base cell (code values.length) block
    obtain ⟨final, rest, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
      ih middle (base + 2) position active stack
        (by simp only [List.length_cons] at fits; omega)
        (by rw [heap]; simp only [Array.size_push]; simp only [List.length_cons] at room; omega) tail
    have middleLive : middle.liveWords = s.liveWords := by
      simp only [State.liveWords, heap, stack, input, Array.size_push, output,
        List.length_append, List.length_cons]; omega
    refine ⟨final, ?_, ?_, finalStack, finalOutput.trans output, ?_, finalRunning⟩
    · have trace := first.append rest
      rw [middleLive] at trace
      convert trace using 1 <;> (try simp only [List.length_cons]) <;> omega
    · rw [finalHeap, heap]
      apply Array.toList_inj.mp
      simp [List.append_assoc]
    · exact finalPC.trans (congrArg (word width) (by
        simp only [List.length_cons]
        omega))

def program (width count : Nat) : Program width 4 := (code count).toArray
@[simp] theorem programWords_eq (count : Nat) : programWords (program width count) = 8 * count := by
  simp [programWords, program]; omega

/-- Resident instructions are charged in addition to the initial input stack. -/
theorem stored_execution (s : State width 4) (values suffix : List (Word width))
    (pc : s.pc = word width 0) (running : s.halted = false)
    (input : s.stack = values ++ suffix)
    (fits : 2 * values.length < 2 ^ width)
    (room : s.heap.size + values.length ≤ 2 ^ width) :
    ∃ final, Execution (program width values.length) s final (2 * values.length) s.liveWords ∧
      final.heap = s.heap ++ values.toArray ∧ final.stack = suffix ∧
      final.output = s.output ∧
      programWords (program width values.length) + s.liveWords = 8 * values.length + s.liveWords := by
  have block : BlockAt (program width values.length) 0 (code values.length) := by
    intro offset bound
    simp [program, List.getElem?_toArray, List.getElem?_eq_getElem bound]
  obtain ⟨final, trace, heap, stack, output, _, _⟩ :=
    code_execution (program width values.length) s values suffix 0 pc running input
      (by simpa using fits) room block
  exact ⟨final, trace, heap, stack, output, by rw [programWords_eq]⟩
end Controller.Cost.InputLoad
