module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Initialize
public import Controller.Cost.InstructionEncoding

@[expose] public section

/-! Fetched storage of instruction fields from registers. The fixed allocation
kernel stores four words and preserves the old heap, stack, output and fields.
Computing the fields from a represented source gate remains separate. -/
namespace Controller.Cost.InstructionRecordStore
open Controller.Cost.GateProgram

def code (registers : List (Fin 4)) : Code width := registers.map Instruction.allocate

@[simp] theorem code_length (registers : List (Fin 4)) :
    (code (width := width) registers).length = registers.length := by simp [code]

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

/-- One actual allocation writes the supplied register and retains its value. -/
theorem cell_execution (program : Program width 4) (s : State width 4)
    (register : Fin 4) (base : Nat) (pc : s.pc = word width base)
    (running : s.halted = false) (fits : base + 1 < 2 ^ width)
    (room : s.heap.size < 2 ^ width)
    (block : BlockAt program base [.allocate register]) :
    ∃ final, Execution program s final 1 (s.liveWords + 1) ∧
      final.heap = s.heap.push (s.reg register) ∧ final.reg = s.reg ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 1) ∧ final.halted = false := by
  let final := { s.advance with heap := s.heap.push (s.reg register) }
  have transition : programStep program s = some final := by
    rw [fetched program s base (.allocate register) pc (by omega)
      (by simpa using block 0 (by simp))]
    simp [step, running, room, final]
  have live : final.liveWords = s.liveWords + 1 := by
    simp [final, State.advance, State.liveWords]; omega
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, advance s base pc (by omega), running⟩
  have trace := Execution.cons transition (Execution.refl final)
  simpa only [live, Nat.zero_add, show max s.liveWords (s.liveWords + 1) = s.liveWords + 1 by omega] using trace

/-- A fixed allocation sequence stores current register values in order. -/
theorem code_execution (program : Program width 4) (s : State width 4)
    (registers : List (Fin 4)) (base : Nat) (pc : s.pc = word width base)
    (running : s.halted = false) (fits : base + registers.length < 2 ^ width)
    (room : s.heap.size + registers.length ≤ 2 ^ width)
    (block : BlockAt program base (code registers)) :
    ∃ final, Execution program s final registers.length (s.liveWords + registers.length) ∧
      final.heap = s.heap ++ (registers.map s.reg).toArray ∧ final.reg = s.reg ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + registers.length) ∧ final.halted = false := by
  induction registers generalizing s base with
  | nil =>
    refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_, running⟩
    · simpa using Execution.refl (p := program) s
    · simp
    · simpa using pc
  | cons register rest ih =>
    have head : BlockAt program base [.allocate register] := by
      apply BlockAt.prefix program base [.allocate register] (code rest)
      simpa [code] using block
    have tail : BlockAt program (base + 1) (code rest) := by
      simpa using BlockAt.suffix program base [.allocate register] (code rest) (by simpa [code] using block)
    obtain ⟨middle, first, heap, reg, stack, output, position, active⟩ :=
      cell_execution program s register base pc running (by simp at fits; omega) (by simp at room; omega) head
    have middleRoom : middle.heap.size + rest.length ≤ 2 ^ width := by simp [heap] at *; omega
    obtain ⟨final, next, finalHeap, finalReg, finalStack, finalOutput, finalPC, finalActive⟩ :=
      ih middle (base + 1) position active (by simp at fits; omega) middleRoom tail
    have middleLive : middle.liveWords = s.liveWords + 1 := by
      simp [State.liveWords, heap, stack, output]; omega
    refine ⟨final, ?_, ?_, finalReg.trans reg, finalStack.trans stack,
      finalOutput.trans output, ?_, finalActive⟩
    · have trace := first.append next
      rw [middleLive] at trace
      convert trace using 1 <;> simp only [List.length_cons] <;> omega
    · rw [finalHeap, heap, reg]
      apply Array.toList_inj.mp
      simp [List.append_assoc]
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC

/-- Four physical words constitute the represented instruction record. -/
def recordCode : Code width := code [0, 1, 2, 3]

@[simp] theorem recordCode_length : (recordCode (width := width)).length = 4 := rfl

/-- The four fetched allocations store exactly one already-computed encoded
instruction. The representation premise concerns registers, not a prebuilt heap. -/
theorem record_execution (program : Program width 4) (s : State width 4)
    (instruction : Instruction width 4) (base : Nat)
    (represented : [s.reg 0, s.reg 1, s.reg 2, s.reg 3] = InstructionEncoding.encode instruction)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 4 < 2 ^ width) (room : s.heap.size + 4 ≤ 2 ^ width)
    (block : BlockAt program base recordCode) :
    ∃ final, Execution program s final 4 (s.liveWords + 4) ∧
      final.heap = s.heap ++ (InstructionEncoding.encode instruction).toArray ∧
      final.reg = s.reg ∧ final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 4) ∧ final.halted = false := by
  obtain ⟨final, trace, heap, reg, stack, output, position, active⟩ :=
    code_execution program s [0, 1, 2, 3] base pc running fits room block
  simp only [List.map_cons, List.map_nil] at heap
  rw [represented] at heap
  exact ⟨final, trace, heap, reg, stack, output, position, active⟩

/-- The uniform record-store kernel occupies sixteen stored program words. -/
theorem record_program_words :
    programWords ((recordCode (width := width)).toArray) = 16 := by
  simp [programWords]

end Controller.Cost.InstructionRecordStore
