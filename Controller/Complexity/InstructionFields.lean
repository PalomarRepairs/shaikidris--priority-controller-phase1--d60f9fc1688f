module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OpcodeReader
public import Controller.Complexity.WordListTotal

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Operational parsing of an instruction's four-bit tag and framed operand
list. Actual final ports recover every encoded instruction. Opcode, arity and
register validity are observed by the codec here; executing those validity
checks is a separate interpreter stage. -/
namespace Controller.Complexity.InstructionFields
open StackMachine WordReader

def program := GuardedLink.program OpcodeReader.program WordListReader.program none Option.isNone

def tagFrame (frame : Port → List Bool) (opcode : Nat) : Port → List Bool :=
  Function.update frame (some 13) (Encoding.bits 4 opcode).reverse

def resultFrame (frame : Port → List Bool) (opcode count : Nat) : Port → List Bool :=
  Function.update (tagFrame frame opcode) (some 12) (List.replicate count true)

def observe (width registers : Nat) (storage : Port → List Bool) : Option (Controller.Cost.Instruction width registers) := do
  let opcode ← Encoding.decodeWord 4 (storage (some 13)).reverse
  let operands ← Encoding.decodeWords width (storage (some 12) ++ false :: storage (some 11))
  InstructionCodec.readFields registers opcode.val operands

theorem raw_execution (frame : Port → List Bool) (width : Nat) (opcode : Fin 16)
    (operands : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ peak, Execution program ⟨some program.main,bank frame [] (Encoding.bits 4 opcode.val++(Encoding.encodeWords width operands++suffix)) []⟩
      ⟨none,WordListReader.data (resultFrame frame opcode.val operands.length) 0 suffix (Encoding.wordList width operands)⟩
      (operands.length*(22*width+24)+75) peak := by
  obtain ⟨tagPeak,tagRun⟩ := OpcodeReader.encoded_execution frame opcode (Encoding.encodeWords width operands++suffix) tagEmpty
  have widthStored : tagFrame frame opcode.val (some 8)=List.replicate width true := by simpa [tagFrame] using stored
  obtain ⟨listPeak,listRun⟩ := WordListReader.execution (tagFrame frame opcode.val) operands suffix widthStored
    (by simpa [tagFrame] using countEmpty) (by simpa [tagFrame] using bufferEmpty) (by simpa [tagFrame] using savedEmpty)
  have accepted : Option.isNone ((bank (tagFrame frame opcode.val) [] (Encoding.encodeWords width operands++suffix) [] none).head?) = true := by
    simp [bank_counter]
  have trace := GuardedLink.success none Option.isNone tagRun listRun accepted
  have ticks : 59+(operands.length*(22*width+24)+16)=operands.length*(22*width+24)+75 := by omega
  exact ⟨_,by simpa only [program, resultFrame, tagFrame, ticks] using trace⟩

theorem execution (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ peak, Execution program ⟨some program.main,bank frame [] (InstructionCodec.encode bound instruction++suffix) []⟩
      ⟨none,WordListReader.data (resultFrame frame (InstructionCodec.fields bound instruction).1
        (InstructionCodec.fields bound instruction).2.length) 0 suffix
          (Encoding.wordList width (InstructionCodec.fields bound instruction).2)⟩
      ((InstructionCodec.fields bound instruction).2.length*(22*width+24)+75) peak := by
  let opcode : Fin 16 := ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩
  simpa only [InstructionCodec.encode, List.append_assoc, opcode] using
    raw_execution frame width opcode (InstructionCodec.fields bound instruction).2 suffix stored countEmpty bufferEmpty savedEmpty tagEmpty

theorem endpoint_observation (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool) :
    observe width registers (WordListReader.data
      (resultFrame frame (InstructionCodec.fields bound instruction).1 (InstructionCodec.fields bound instruction).2.length)
      0 suffix (Encoding.wordList width (InstructionCodec.fields bound instruction).2)) = some instruction := by
  let opcode : Controller.Cost.Word 4 :=
    ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩
  have tagParsed := (Encoding.wordEncoding 4).decode_encode opcode
  change Encoding.decodeWord 4 (Encoding.bits 4 (InstructionCodec.fields bound instruction).1)=some opcode at tagParsed
  have wordsParsed := (Encoding.wordsEncoding width).decode_encode (InstructionCodec.fields bound instruction).2
  change Encoding.decodeWords width (Encoding.encodeWords width (InstructionCodec.fields bound instruction).2)=some _ at wordsParsed
  simp only [observe]
  simp [WordListReader.data_at, resultFrame, tagFrame, List.reverse_reverse]
  rw [tagParsed]
  simp only [Option.bind]
  have encoded : List.replicate (InstructionCodec.fields bound instruction).2.length true ++
      false :: Encoding.wordList width (InstructionCodec.fields bound instruction).2 =
      Encoding.encodeWords width (InstructionCodec.fields bound instruction).2 := rfl
  rw [encoded, wordsParsed]
  exact InstructionCodec.readFields_fields bound instruction

theorem execution_observes (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] (InstructionCodec.encode bound instruction++suffix) []⟩ final ticks peak ∧
      observe width registers final.stk=some instruction ∧ final.stk (some 0)=suffix ∧
      ticks ≤ 66*width+147 ∧ peak ≤ (InstructionCodec.encode bound instruction++suffix).length+ambientBits frame+(66*width+147) := by
  obtain ⟨peak,trace⟩ := execution frame bound instruction suffix stored countEmpty bufferEmpty savedEmpty tagEmpty
  have operandBound := Nat.mul_le_mul_right (22*width+24) (InstructionCodec.fields_length_le bound instruction)
  have ticks : (InstructionCodec.fields bound instruction).2.length*(22*width+24)+75 ≤ 66*width+147 := by
    calc
      _ ≤ 3*(22*width+24)+75 := by omega
      _ = _ := by ring
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  exact ⟨_,_,peak,trace,endpoint_observation frame bound instruction suffix,by simp [WordListReader.data_at],ticks,by omega⟩

def result (frame : Port → List Bool) (width : Nat) (input : List Bool) : Port → List Bool :=
  if 4 ≤ input.length then WordListTotal.parseResult
    (Function.update frame (some 13) (input.take 4).reverse) width (input.drop 4)
  else OpcodeReader.result frame input

theorem total_resources (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ ⟨none,result frame width input⟩ ticks peak ∧
      ticks ≤ input.length*(16*width+30)+75 ∧ peak ≤ input.length+ambientBits frame+(input.length*(16*width+30)+75) := by
  by_cases enough : 4 ≤ input.length
  · let tagFrame := Function.update frame (some 13) (input.take 4).reverse
    have tagWidth : (input.take 4).length=4 := by simp only [List.length_take, Nat.min_eq_left enough]
    obtain ⟨tagPeak,tagRun⟩ := OpcodeReader.execution frame (input.take 4) (input.drop 4) tagWidth tagEmpty
    rw [List.take_append_drop] at tagRun
    have widthStored : tagFrame (some 8)=List.replicate width true := by simpa [tagFrame] using stored
    obtain ⟨listTicks,listPeak,listRun,listBound,_⟩ := WordListTotal.total_resources tagFrame width (input.drop 4) widthStored
      (by simpa [tagFrame] using countEmpty) (by simpa [tagFrame] using bufferEmpty) (by simpa [tagFrame] using savedEmpty)
    have accepted : Option.isNone ((bank tagFrame [] (input.drop 4) [] none).head?) = true := by simp [bank_counter]
    have trace := GuardedLink.success none Option.isNone tagRun listRun accepted
    have suffixLength : (input.drop 4).length ≤ input.length := by simp only [List.length_drop]; omega
    have product := Nat.mul_le_mul_right (16*width+30) suffixLength
    have timeBound : 59+listTicks ≤ input.length*(16*width+30)+75 := by omega
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    exact ⟨_,_,by simpa only [program, result, ite_eq_left enough, tagFrame] using trace,timeBound,by omega⟩
  · obtain ⟨tagPeak,tagRun⟩ := OpcodeReader.short_execution frame input (by omega)
    have rejected : Option.isNone ((bank frame (false :: List.replicate (3-input.length) true) [] input.reverse none).head?) = false := by
      simp [bank_counter]
    have trace := GuardedLink.failure WordListReader.program none Option.isNone tagRun rejected
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    exact ⟨_,_,by simpa only [program, result, OpcodeReader.result, ite_eq_right enough] using trace,by omega,by omega⟩

theorem total_polynomial (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ ⟨none,result frame width input⟩ ticks peak ∧
      ticks ≤ 16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+75 ∧
      peak ≤ 16*(input.length+ambientBits frame)^2+31*(input.length+ambientBits frame)+75 := by
  obtain ⟨ticks,peak,trace,timeBound,_⟩ := total_resources frame width input stored countEmpty bufferEmpty savedEmpty tagEmpty
  have widthBound : width ≤ input.length+ambientBits frame := by
    have storedSize := WordListTotal.stored_width_le_ambient frame width stored
    omega
  have inputBound : input.length ≤ input.length+ambientBits frame := by omega
  have product := Nat.mul_le_mul inputBound (Nat.add_le_add_right (Nat.mul_le_mul_left 16 widthBound) 30)
  have identity : (input.length+ambientBits frame)*(16*(input.length+ambientBits frame)+30)+75 =
      16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+75 := by ring
  have finalTime : ticks ≤ 16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+75 := by rw [← identity]; omega
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  exact ⟨ticks,peak,trace,finalTime,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 900 := by
  simpa [program, OpcodeReader.program, OpcodeReader.readMachine, OpcodeReader.seed, OpcodeReader.saveMachine,
    WordListReader.program, WordListReader.payloadProgram, WordListReader.restorePayload, WordListReader.loop,
    WordListReader.body, WordListReader.moveWord, WordListReader.restoreMachine, WordListReader.countMachine,
    ColdInput.readSave, ColdInput.headerMachine, CountLoop.program, GuardedLink.program, StackFrames.relocate,
    WidthReader.program, WidthReader.counterMachine, StackCopy.program, WordReader.program,
    WordReader.cursorMachine, WordReader.reverseMachine, StackBlocks.reverseProgram, link] using finiteTM_resident program

end Controller.Complexity.InstructionFields
