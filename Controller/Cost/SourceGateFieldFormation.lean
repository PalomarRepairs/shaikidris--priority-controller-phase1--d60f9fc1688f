module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.InstructionRecordStore

@[expose] public section

/-! Fetched formation of the first instruction of a represented input gate.
A fixed kernel reads the raw channel identifier from source memory, forms the
opcode, destination and padding fields, and allocates the four-word record.
Source serialization/loading and the whole source compiler have separate costs. -/
namespace Controller.Cost.SourceGateFieldFormation
open Controller.Decoder Controller.Cost.GateProgram

/-- Source-address register 3 supplies the only dynamic input to this template. -/
def fieldCode (width : ℕ) : Code width :=
  [.load 2 3, .constant 0 (word width 0), .constant 1 (word width 0),
    .constant 3 (word width 0)]

def code (width : ℕ) : Code width := fieldCode width ++ InstructionRecordStore.recordCode

@[simp] theorem fieldCode_length : (fieldCode width).length = 4 := rfl
@[simp] theorem code_length : (code width).length = 8 := rfl

def program (width : ℕ) : Program width 4 := (code width).toArray

@[simp] theorem program_words : programWords (program width) = 32 := by
  simp [program, programWords]

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance (s : State width 4) (base : ℕ)
    (pc : s.pc = word width base) (fits : base < 2 ^ width) :
    s.advance.pc = word width (base + 1) := by
  simp only [State.advance, pc]
  rw [show (word width base).val = base from Nat.mod_eq_of_lt fits]

/-- Four fetched operations compute all encoded fields; no register-encoding
premise is supplied by the caller. Existing heap, stack and output are frames. -/
theorem fields_execution (program : Program width 4) (s : State width 4)
    (channel : Channel n) (sourceAddress base : ℕ)
    (address : s.reg 3 = word width sourceAddress)
    (sourceBound : sourceAddress < s.heap.size)
    (sourceFits : sourceAddress < 2 ^ width)
    (source : s.heap[sourceAddress]'sourceBound = word width channel.val)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 4 < 2 ^ width) (block : BlockAt program base (fieldCode width)) :
    ∃ ready, Execution program s ready 4 s.liveWords ∧
      [ready.reg 0, ready.reg 1, ready.reg 2, ready.reg 3] =
        InstructionEncoding.encode (.constant 0 (word width channel.val) : Instruction width 4) ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 4) ∧ ready.halted = false := by
  let loaded := s.advance.put 2 (word width channel.val)
  let opcode := loaded.advance.put 0 (word width 0)
  let destination := opcode.advance.put 1 (word width 0)
  let ready := destination.advance.put 3 (word width 0)
  have loadedPC : loaded.pc = word width (base + 1) := advance s base pc (by omega)
  have opcodePC : opcode.pc = word width (base + 2) := by
    simpa [opcode, State.put, Nat.add_assoc] using advance loaded (base + 1) loadedPC (by omega)
  have destinationPC : destination.pc = word width (base + 3) := by
    simpa [destination, State.put, Nat.add_assoc] using advance opcode (base + 2) opcodePC (by omega)
  have readyPC : ready.pc = word width (base + 4) := by
    simpa [ready, State.put, Nat.add_assoc] using advance destination (base + 3) destinationPC (by omega)
  have first : programStep program s = some loaded := by
    rw [fetched program s base (.load 2 3) pc (by omega)
      (by simpa [fieldCode] using block 0 (by simp [fieldCode]))]
    have addressVal : (word width sourceAddress).val = sourceAddress := Nat.mod_eq_of_lt sourceFits
    simp [step, running, address, addressVal, sourceBound, source, loaded]
  have second : programStep program loaded = some opcode := by
    rw [fetched program loaded (base + 1) (.constant 0 (word width 0)) loadedPC (by omega)
      (by simpa [fieldCode] using block 1 (by simp [fieldCode]))]
    simp [step, loaded, opcode, State.advance, State.put, running]
  have third : programStep program opcode = some destination := by
    rw [fetched program opcode (base + 2) (.constant 1 (word width 0)) opcodePC (by omega)
      (by simpa [fieldCode] using block 2 (by simp [fieldCode]))]
    simp [step, loaded, opcode, destination, State.advance, State.put, running]
  have fourth : programStep program destination = some ready := by
    rw [fetched program destination (base + 3) (.constant 3 (word width 0)) destinationPC (by omega)
      (by simpa [fieldCode] using block 3 (by simp [fieldCode]))]
    simp [step, loaded, opcode, destination, ready, State.advance, State.put, running]
  have loadedLive : loaded.liveWords = s.liveWords := rfl
  have opcodeLive : opcode.liveWords = s.liveWords := rfl
  have destinationLive : destination.liveWords = s.liveWords := rfl
  have readyLive : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, rfl, rfl, rfl, readyPC, running⟩
  · have trace := Execution.cons first (Execution.cons second
      (Execution.cons third (Execution.cons fourth (Execution.refl ready))))
    simpa [loadedLive, opcodeLive, destinationLive, readyLive] using trace
  · simp [ready, destination, opcode, loaded, State.put, State.advance,
      InstructionEncoding.encode, InstructionEncoding.fields, word, Nat.mod_mod]

/-- The fixed eight-transition kernel forms and stores the exact instruction
record from the represented source channel. Its peak adds only four heap words. -/
theorem inputConstant_execution (program : Program width 4) (s : State width 4)
    (channel : Channel n) (sourceAddress base : ℕ)
    (address : s.reg 3 = word width sourceAddress)
    (sourceBound : sourceAddress < s.heap.size)
    (source : s.heap[sourceAddress]'sourceBound = word width channel.val)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 8 < 2 ^ width) (room : s.heap.size + 4 ≤ 2 ^ width)
    (block : BlockAt program base (code width)) :
    ∃ final, Execution program s final 8 (s.liveWords + 4) ∧
      final.heap = s.heap ++ (InstructionEncoding.encode
        (.constant 0 (word width channel.val) : Instruction width 4)).toArray ∧
      [final.reg 0, final.reg 1, final.reg 2, final.reg 3] =
        InstructionEncoding.encode (.constant 0 (word width channel.val) : Instruction width 4) ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 8) ∧ final.halted = false := by
  have headBlock := BlockAt.prefix program base (fieldCode width) InstructionRecordStore.recordCode block
  obtain ⟨ready, formed, encoded, heap, stack, output, position, active⟩ :=
    fields_execution program s channel sourceAddress base address sourceBound (by omega)
      source pc running (by omega) headBlock
  have suffix : BlockAt program (base + 4) InstructionRecordStore.recordCode := by
    simpa using BlockAt.suffix program base (fieldCode width) InstructionRecordStore.recordCode block
  obtain ⟨final, stored, finalHeap, finalReg, finalStack, finalOutput, finalPC, finalActive⟩ :=
    InstructionRecordStore.record_execution program ready (.constant 0 (word width channel.val))
      (base + 4) encoded position active (by omega) (by rw [heap]; exact room) suffix
  have readyLive : ready.liveWords = s.liveWords := by simp [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, ?_, ?_, finalStack.trans stack, finalOutput.trans output, ?_, finalActive⟩
  · have trace := formed.append stored
    rw [readyLive] at trace
    convert trace using 1 <;> omega
  · simpa [heap] using finalHeap
  · simpa only [finalReg] using encoded
  · simpa [Nat.add_assoc] using finalPC

/-- Caller source-memory prefix is retained at every old address. -/
theorem source_prefix_preserved (old : Array (Word width)) (channel : Channel n)
    (final : State width 4)
    (heap : final.heap = old ++ (InstructionEncoding.encode
      (.constant 0 (word width channel.val) : Instruction width 4)).toArray) :
    ∀ index, index < old.size → final.heap[index]? = old[index]? := by
  intro index bound
  rw [heap]
  simp [Array.getElem?_append, bound]

/-- Program storage is fixed independently of the represented decoder graph. -/
theorem stored_inputConstant_execution (s : State width 4) (channel : Channel n)
    (sourceAddress : ℕ) (address : s.reg 3 = word width sourceAddress)
    (sourceBound : sourceAddress < s.heap.size)
    (source : s.heap[sourceAddress]'sourceBound = word width channel.val)
    (pc : s.pc = word width 0) (running : s.halted = false)
    (fits : 8 < 2 ^ width) (room : s.heap.size + 4 ≤ 2 ^ width) :
    ∃ final, Execution (program width) s final 8 (s.liveWords + 4) ∧
      final.heap = s.heap ++ (InstructionEncoding.encode
        (.constant 0 (word width channel.val) : Instruction width 4)).toArray ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.halted = false ∧ residentWords (program width) final = s.liveWords + 36 := by
  have block : BlockAt (program width) 0 (code width) := by
    intro offset bound
    simp [program, List.getElem?_toArray, List.getElem?_eq_getElem bound]
  obtain ⟨final, trace, heap, encoded, stack, output, position, active⟩ :=
    inputConstant_execution (program width) s channel sourceAddress 0 address sourceBound source
      pc running (by simpa using fits) room block
  refine ⟨final, trace, heap, stack, output, active, ?_⟩
  simp [residentWords, program_words, State.liveWords, heap, stack, output]
  omega

end Controller.Cost.SourceGateFieldFormation
