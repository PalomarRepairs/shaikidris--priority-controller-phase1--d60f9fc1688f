module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.TrackedAllocate

@[expose] public section

/-! Fetched loading of supplied input words from a stack into fresh heap cells.
The input words are already represented; parsing external bytes is separate.
Every pop and allocation is charged, and the input storage is included in peak. -/
namespace Controller.Horn.TrackedInput
open Controller.Cost
abbrev Code (width : Nat) := List (Instruction width 8)
def cell : Code width := [.pop 0, .allocate 0, .add 7 7 5]
def code : Nat → Code width
  | 0 => []
  | count + 1 => cell ++ code count
@[simp] theorem code_length (count : Nat) : (code (width := width) count).length = 3 * count := by
  induction count with
  | zero => simp [code]
  | succ count ih => simp [code, cell, ih]; omega

/-- A stored instruction block, for the common eight-register machine. -/
def BlockAt (program : Program width 8) (base : Nat) (instructions : Code width) : Prop :=
  ∀ offset, offset < instructions.length → program[base + offset]? = instructions[offset]?

theorem BlockAt.prefix (program : Program width 8) (base : Nat)
    (first rest : Code width) (stored : BlockAt program base (first ++ rest)) :
    BlockAt program base first := by
  intro offset bound
  have whole := stored offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left bound] at whole
  exact whole

theorem BlockAt.suffix (program : Program width 8) (base : Nat)
    (first rest : Code width) (stored : BlockAt program base (first ++ rest)) :
    BlockAt program (base + first.length) rest := by
  intro offset bound
  have whole := stored (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at whole
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using whole

private theorem fetched (program : Program width 8) (s : State width 8)
    (base : Nat) (instruction : Instruction width 8)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl
private theorem advance (s : State width 8) (base : Nat)
    (pc : s.pc = word width base) (fits : base < 2 ^ width) :
    s.advance.pc = word width (base + 1) := by
  simp only [State.advance, pc]
  rw [show (word width base).val = base from Nat.mod_eq_of_lt fits]

/-- Three actual instructions move one supplied word into the heap and
advance the heap-end register. Input stack storage remains charged. -/
theorem cell_execution (program : Program width 8) (s : State width 8)
    (value : Word width) (rest : List (Word width)) (base : Nat)
    (pc : s.pc = word width base) (running : s.halted = false)
    (input : s.stack = value :: rest) (fits : base + 3 < 2 ^ width)
    (room : s.heap.size + 1 < 2 ^ width)
    (pointer : s.reg 7 = word width s.heap.size) (one : s.reg 5 = word width 1)
    (block : BlockAt program base cell) :
    ∃ final, Execution program s final 3 s.liveWords ∧
      final.heap = s.heap.push value ∧ final.stack = rest ∧
      final.output = s.output ∧ final.pc = word width (base + 3) ∧
      final.halted = false ∧ final.reg 7 = word width final.heap.size ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 7 →
        final.reg register = s.reg register) := by
  let popped := { s.advance.put 0 value with stack := rest }
  let allocated := { popped.advance with heap := s.heap.push value }
  let final := allocated.advance.put 7 (word width (s.heap.size + 1))
  have poppedPC : popped.pc = word width (base + 1) := advance s base pc (by omega)
  have allocatedPC : allocated.pc = word width (base + 2) := by
    exact advance popped (base + 1) poppedPC (by omega)
  have first : programStep program s = some popped := by
    rw [fetched program s base (.pop 0) pc (by omega)
      (by simpa [cell] using block 0 (by simp [cell]))]
    simp [step, running, input, popped]
  have second : programStep program popped = some allocated := by
    rw [fetched program popped (base + 1) (.allocate 0) poppedPC (by omega)
      (by simpa [cell] using block 1 (by simp [cell]))]
    simp [step, popped, allocated, State.put, State.advance, running, show s.heap.size < 2 ^ width by omega]
  have third : programStep program allocated = some final := by
    rw [fetched program allocated (base + 2) (.add 7 7 5) allocatedPC (by omega)
      (by simpa [cell] using block 2 (by simp [cell]))]
    have pointerValue : (word width s.heap.size).val = s.heap.size := Nat.mod_eq_of_lt (by omega)
    have oneValue : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
    simp [step, final, allocated, popped, State.put, State.advance, running,
      pointer, one, pointerValue, oneValue]
  have poppedLive : popped.liveWords + 1 = s.liveWords := by
    simp [popped, State.liveWords, State.put, State.advance, input]; omega
  have allocatedLive : allocated.liveWords = s.liveWords := by
    simp [allocated, popped, State.liveWords, State.put, State.advance, input]; omega
  have finalLive : final.liveWords = s.liveWords := by
    simp [final, allocated, popped, State.liveWords, State.put, State.advance, input]; omega
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, running, ?_, ?_⟩
  · have trace := Execution.cons first (Execution.cons second
      (Execution.cons third (Execution.refl final)))
    convert trace using 1 <;> omega
  · change allocated.advance.pc = word width (base + 3)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      advance allocated (base + 2) allocatedPC (by omega)
  · simp [final, allocated, State.put, State.advance]
  · intro register notZero notPointer
    simp [final, allocated, popped, State.put, State.advance, notZero, notPointer]

/-- Arbitrary supplied words are loaded in order, preserving the retained suffix. -/
theorem code_execution (program : Program width 8) (s : State width 8)
    (values suffix : List (Word width)) (base : Nat)
    (pc : s.pc = word width base) (running : s.halted = false)
    (input : s.stack = values ++ suffix)
    (fits : base + 3 * values.length < 2 ^ width)
    (room : s.heap.size + values.length < 2 ^ width)
    (pointer : s.reg 7 = word width s.heap.size) (one : s.reg 5 = word width 1)
    (block : BlockAt program base (code values.length)) :
    ∃ final, Execution program s final (3 * values.length) s.liveWords ∧
      final.heap = s.heap ++ values.toArray ∧ final.stack = suffix ∧
      final.output = s.output ∧ final.pc = word width (base + 3 * values.length) ∧
      final.halted = false ∧ final.reg 7 = word width final.heap.size ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 7 → final.reg register = s.reg register) := by
  induction values generalizing s base with
  | nil =>
    refine ⟨s, ?_, ?_, ?_, rfl, ?_, running, pointer, by intros; rfl⟩
    · simpa using Execution.refl (p := program) s
    · simp
    · simpa using input
    · simpa using pc
  | cons value values ih =>
    have head := BlockAt.prefix program base cell (code values.length) block
    obtain ⟨middle, first, heap, stack, output, position, active, middlePointer, middleFrame⟩ :=
      cell_execution program s value (values ++ suffix) base pc running input
        (by simp only [List.length_cons] at fits; omega)
        (by simp only [List.length_cons] at room; omega) pointer one head
    have tail : BlockAt program (base + 3) (code values.length) := by
      simpa [cell] using BlockAt.suffix program base cell (code values.length) block
    obtain ⟨final, rest, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalPointer, finalFrame⟩ :=
      ih middle (base + 3) position active stack
        (by simp only [List.length_cons] at fits; omega)
        (by rw [heap]; simp only [Array.size_push]; simp only [List.length_cons] at room; omega) middlePointer
        (by rw [middleFrame 5 (by decide) (by decide)]; exact one) tail
    have middleLive : middle.liveWords = s.liveWords := by
      simp only [State.liveWords, heap, stack, input, Array.size_push, output,
        List.length_append, List.length_cons]; omega
    refine ⟨final, ?_, ?_, finalStack, finalOutput.trans output, ?_, finalRunning, finalPointer, ?_⟩
    · have trace := first.append rest
      rw [middleLive] at trace
      convert trace using 1 <;> (try simp only [List.length_cons]) <;> omega
    · rw [finalHeap, heap]
      apply Array.toList_inj.mp
      simp [List.append_assoc]
    · exact finalPC.trans (congrArg (word width) (by
        simp only [List.length_cons]
        omega))
    · intro register notZero notPointer
      exact (finalFrame register notZero notPointer).trans (middleFrame register notZero notPointer)

/-- A cold loader obtains its endpoint register from a fetched constant.
The empty heap is the actual starting heap, with the input words on the stack. -/
theorem seed_pointer (program : Program width 8) (state : State width 8)
    (empty : state.heap = #[]) (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.constant 7 (word width 0))) :
    Execution program state (state.advance.put 7 (word width 0)) 1 state.liveWords ∧
    (state.advance.put 7 (word width 0)).reg 7 =
      word width (state.advance.put 7 (word width 0)).heap.size := by
  have transition : programStep program state = some (state.advance.put 7 (word width 0)) := by
    unfold programStep
    rw [fetched]
    simp [step, running]
  constructor
  · simpa [State.liveWords, State.advance, State.put] using
      Execution.cons transition (Execution.refl (state.advance.put 7 (word width 0)))
  · simp [State.advance, State.put, empty]

/-- Program storage for this supplied-input loader is charged explicitly. -/
def program (width count : Nat) : Program width 8 := (code count).toArray
@[simp] theorem programWords_eq (count : Nat) : programWords (program width count) = 12 * count := by
  simp [programWords, program]; omega

end Controller.Horn.TrackedInput
