module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SourceGateFieldFormation

@[expose] public section

/-! Fixed fetched templates serialize the remaining two input-gate instructions.
The source-dependent constant record and two fixed records form the complete
three-instruction input gate. Source loading and the whole compiler are separate. -/
namespace Controller.Cost.SourceGateInput
open Controller.Decoder Controller.Cost.GateProgram

def fieldsCode (width a b c d : ℕ) : Code width :=
  [.constant 0 (word width a), .constant 1 (word width b),
   .constant 2 (word width c), .constant 3 (word width d)]
def recordTemplate (width a b c d : ℕ) : Code width :=
  fieldsCode width a b c d ++ InstructionRecordStore.recordCode
def loadCode (width : ℕ) : Code width := recordTemplate width 4 2 0 0
def allocateCode (width : ℕ) : Code width := recordTemplate width 6 2 0 0
def code (width : ℕ) : Code width :=
  SourceGateFieldFormation.code width ++ (loadCode width ++ allocateCode width)
def program (width : ℕ) : Program width 4 := (code width).toArray
@[simp] theorem fieldsCode_length : (fieldsCode width a b c d).length = 4 := rfl
@[simp] theorem recordTemplate_length : (recordTemplate width a b c d).length = 8 := rfl
@[simp] theorem loadCode_length : (loadCode width).length = 8 := rfl
@[simp] theorem allocateCode_length : (allocateCode width).length = 8 := rfl
@[simp] theorem code_length : (code width).length = 24 := rfl
@[simp] theorem program_words : programWords (program width) = 96 := by simp [program, programWords]

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

private theorem fields_execution (program : Program width 4) (s : State width 4)
    (a b c d base : ℕ) (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 4 < 2 ^ width) (block : BlockAt program base (fieldsCode width a b c d)) :
    ∃ ready, Execution program s ready 4 s.liveWords ∧
      [ready.reg 0, ready.reg 1, ready.reg 2, ready.reg 3] =
        [word width a, word width b, word width c, word width d] ∧
      ready.heap = s.heap ∧ ready.stack = s.stack ∧ ready.output = s.output ∧
      ready.pc = word width (base + 4) ∧ ready.halted = false := by
  let loaded := s.advance.put 0 (word width a)
  let opcode := loaded.advance.put 1 (word width b)
  let destination := opcode.advance.put 2 (word width c)
  let ready := destination.advance.put 3 (word width d)
  have loadedPC : loaded.pc = word width (base + 1) := advance s base pc (by omega)
  have opcodePC : opcode.pc = word width (base + 2) := by
    simpa [opcode, State.put, Nat.add_assoc] using advance loaded (base + 1) loadedPC (by omega)
  have destinationPC : destination.pc = word width (base + 3) := by
    simpa [destination, State.put, Nat.add_assoc] using advance opcode (base + 2) opcodePC (by omega)
  have readyPC : ready.pc = word width (base + 4) := by
    simpa [ready, State.put, Nat.add_assoc] using advance destination (base + 3) destinationPC (by omega)
  have first : programStep program s = some loaded := by
    rw [fetched program s base (.constant 0 (word width a)) pc (by omega)
      (by simpa [fieldsCode] using block 0 (by simp [fieldsCode]))]
    simp [step, running, loaded]
  have second : programStep program loaded = some opcode := by
    rw [fetched program loaded (base + 1) (.constant 1 (word width b)) loadedPC (by omega)
      (by simpa [fieldsCode] using block 1 (by simp [fieldsCode]))]
    simp [step, loaded, opcode, State.advance, State.put, running]
  have third : programStep program opcode = some destination := by
    rw [fetched program opcode (base + 2) (.constant 2 (word width c)) opcodePC (by omega)
      (by simpa [fieldsCode] using block 2 (by simp [fieldsCode]))]
    simp [step, loaded, opcode, destination, State.advance, State.put, running]
  have fourth : programStep program destination = some ready := by
    rw [fetched program destination (base + 3) (.constant 3 (word width d)) destinationPC (by omega)
      (by simpa [fieldsCode] using block 3 (by simp [fieldsCode]))]
    simp [step, loaded, opcode, destination, ready, State.advance, State.put, running]
  have loadedLive : loaded.liveWords = s.liveWords := rfl
  have opcodeLive : opcode.liveWords = s.liveWords := rfl
  have destinationLive : destination.liveWords = s.liveWords := rfl
  have readyLive : ready.liveWords = s.liveWords := rfl
  refine ⟨ready, ?_, ?_, rfl, rfl, rfl, readyPC, running⟩
  · have trace := Execution.cons first (Execution.cons second
      (Execution.cons third (Execution.cons fourth (Execution.refl ready))))
    simpa [loadedLive, opcodeLive, destinationLive, readyLive] using trace
  · simp [ready, destination, opcode, loaded, State.put, State.advance]

private theorem template_execution (program : Program width 4) (s : State width 4)
    (instruction : Instruction width 4) (a b c d base : ℕ)
    (fields : InstructionEncoding.encode instruction = [word width a, word width b, word width c, word width d])
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 8 < 2 ^ width) (room : s.heap.size + 4 ≤ 2 ^ width)
    (block : BlockAt program base (recordTemplate width a b c d)) :
    ∃ final, Execution program s final 8 (s.liveWords + 4) ∧
      final.heap = s.heap ++ (InstructionEncoding.encode instruction).toArray ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 8) ∧ final.halted = false := by
  have headBlock := BlockAt.prefix program base (fieldsCode width a b c d) InstructionRecordStore.recordCode block
  obtain ⟨ready, formed, encoded, heap, stack, output, position, active⟩ :=
    fields_execution program s a b c d base pc running (by omega) headBlock
  have tailBlock : BlockAt program (base + 4) InstructionRecordStore.recordCode := by
    simpa using BlockAt.suffix program base (fieldsCode width a b c d) InstructionRecordStore.recordCode block
  obtain ⟨final, stored, finalHeap, finalReg, finalStack, finalOutput, finalPC, finalActive⟩ :=
    InstructionRecordStore.record_execution program ready instruction (base + 4)
      (encoded.trans fields.symm) position active (by omega) (by rw [heap]; exact room) tailBlock
  have readyLive : ready.liveWords = s.liveWords := by simp [State.liveWords, heap, stack, output]
  refine ⟨final, ?_, ?_, finalStack.trans stack, finalOutput.trans output, ?_, finalActive⟩
  · have trace := formed.append stored
    rw [readyLive] at trace
    convert trace using 1 <;> omega
  · simpa [heap] using finalHeap
  · simpa [Nat.add_assoc] using finalPC

/-- Fixed instructions are formed by four fetched constants and four allocations. -/
theorem load_execution (program : Program width 4) (s : State width 4) (base : ℕ)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 8 < 2 ^ width) (room : s.heap.size + 4 ≤ 2 ^ width)
    (block : BlockAt program base (loadCode width)) :
    ∃ final, Execution program s final 8 (s.liveWords + 4) ∧
      final.heap = s.heap ++ (InstructionEncoding.encode (.load 2 0 : Instruction width 4)).toArray ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 8) ∧ final.halted = false := by
  exact template_execution program s (.load 2 0) 4 2 0 0 base rfl pc running fits room block

theorem allocate_execution (program : Program width 4) (s : State width 4) (base : ℕ)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 8 < 2 ^ width) (room : s.heap.size + 4 ≤ 2 ^ width)
    (block : BlockAt program base (allocateCode width)) :
    ∃ final, Execution program s final 8 (s.liveWords + 4) ∧
      final.heap = s.heap ++ (InstructionEncoding.encode (.allocate 2 : Instruction width 4)).toArray ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 8) ∧ final.halted = false := by
  exact template_execution program s (.allocate 2) 6 2 0 0 base rfl pc running fits room block

/-- Ordered physical records for precisely the three target input instructions. -/
def records (width : ℕ) (channel : Channel n) : Array (Word width) :=
  ((gateCode width 0 (.input channel : Gate n 0)).flatMap InstructionEncoding.encode).toArray
@[simp] theorem records_size : (records width channel).size = 12 := by
  simp [records, gateCode, InstructionEncoding.encode, InstructionEncoding.fields]

theorem input_execution (program : Program width 4) (s : State width 4)
    (channel : Channel n) (sourceAddress base : ℕ)
    (address : s.reg 3 = word width sourceAddress) (sourceBound : sourceAddress < s.heap.size)
    (source : s.heap[sourceAddress]'sourceBound = word width channel.val)
    (pc : s.pc = word width base) (running : s.halted = false)
    (fits : base + 24 < 2 ^ width) (room : s.heap.size + 12 ≤ 2 ^ width)
    (block : BlockAt program base (code width)) :
    ∃ final, Execution program s final 24 (s.liveWords + 12) ∧
      final.heap = s.heap ++ records width channel ∧
      final.stack = s.stack ∧ final.output = s.output ∧
      final.pc = word width (base + 24) ∧ final.halted = false := by
  have firstBlock := BlockAt.prefix program base (SourceGateFieldFormation.code width)
    (loadCode width ++ allocateCode width) block
  have restBlock : BlockAt program (base + 8) (loadCode width ++ allocateCode width) := by
    simpa using BlockAt.suffix program base (SourceGateFieldFormation.code width)
      (loadCode width ++ allocateCode width) block
  have secondBlock := BlockAt.prefix program (base + 8) (loadCode width) (allocateCode width) restBlock
  have thirdBlock : BlockAt program (base + 16) (allocateCode width) := by
    simpa [Nat.add_assoc] using BlockAt.suffix program (base + 8) (loadCode width) (allocateCode width) restBlock
  obtain ⟨one, first, heapOne, regOne, stackOne, outputOne, pcOne, activeOne⟩ :=
    SourceGateFieldFormation.inputConstant_execution program s channel sourceAddress base address sourceBound source pc running (by omega) (by omega) firstBlock
  have sizeOne : one.heap.size = s.heap.size + 4 := by simp [heapOne, InstructionEncoding.encode]
  obtain ⟨two, second, heapTwo, stackTwo, outputTwo, pcTwo, activeTwo⟩ :=
    load_execution program one (base + 8) pcOne activeOne (by omega) (by omega) secondBlock
  have sizeTwo : two.heap.size = s.heap.size + 8 := by simp [heapTwo, sizeOne, InstructionEncoding.encode]
  obtain ⟨final, third, heapFinal, stackFinal, outputFinal, pcFinal, activeFinal⟩ :=
    allocate_execution program two (base + 16) (by simpa [Nat.add_assoc] using pcTwo) activeTwo (by omega) (by omega) thirdBlock
  have liveOne : one.liveWords = s.liveWords + 4 := by simp [State.liveWords, sizeOne, stackOne, outputOne]; omega
  have liveTwo : two.liveWords = s.liveWords + 8 := by simp [State.liveWords, sizeTwo, stackTwo, stackOne, outputTwo, outputOne]; omega
  refine ⟨final, ?_, ?_, stackFinal.trans (stackTwo.trans stackOne), outputFinal.trans (outputTwo.trans outputOne), ?_, activeFinal⟩
  · have trace := (first.append second).append third
    rw [liveOne, liveTwo] at trace
    convert trace using 1 <;> omega
  · rw [heapFinal, heapTwo, heapOne]
    apply Array.toList_inj.mp
    simp [records, gateCode, List.append_assoc]
  · simpa [Nat.add_assoc] using pcFinal

theorem source_prefix_preserved (old : Array (Word width)) (channel : Channel n)
    (final : State width 4) (heap : final.heap = old ++ records width channel) :
    ∀ index, index < old.size → final.heap[index]? = old[index]? := by
  intro index bound
  rw [heap]
  simp [Array.getElem?_append, bound]

theorem stored_input_execution (s : State width 4) (channel : Channel n)
    (sourceAddress : ℕ) (address : s.reg 3 = word width sourceAddress)
    (sourceBound : sourceAddress < s.heap.size)
    (source : s.heap[sourceAddress]'sourceBound = word width channel.val)
    (pc : s.pc = word width 0) (running : s.halted = false)
    (fits : 24 < 2 ^ width) (room : s.heap.size + 12 ≤ 2 ^ width) :
    ∃ final, Execution (program width) s final 24 (s.liveWords + 12) ∧
      final.heap = s.heap ++ records width channel ∧
      final.stack = s.stack ∧ final.output = s.output ∧ final.halted = false ∧
      residentWords (program width) final = s.liveWords + 108 := by
  have block : BlockAt (program width) 0 (code width) := by
    intro offset bound
    simp [program, List.getElem?_toArray, List.getElem?_eq_getElem bound]
  obtain ⟨final, trace, heap, stack, output, position, active⟩ :=
    input_execution (program width) s channel sourceAddress 0 address sourceBound source pc running (by simpa using fits) room block
  refine ⟨final, trace, heap, stack, output, active, ?_⟩
  simp [residentWords, State.liveWords, heap, stack, output]
  omega
end Controller.Cost.SourceGateInput
