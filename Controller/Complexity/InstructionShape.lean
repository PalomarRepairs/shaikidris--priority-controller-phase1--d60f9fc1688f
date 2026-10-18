module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OpcodeArity

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Structural instruction parsing is followed by executed opcode and arity
validation. The checker preserves tag, operands, count and source suffix and
sets the actual status bank on rejection. Register-range validation is separate. -/
namespace Controller.Complexity.InstructionShape
open StackMachine WordReader
open scoped BigOperators

def program := GuardedLink.program InstructionFields.program OpcodeArity.machine none Option.isNone

def fieldsData (frame : Port → List Bool) (opcode : Fin 16)
    (operands : List (Controller.Cost.Word width)) (suffix : List Bool) : Port → List Bool :=
  WordListReader.data (InstructionFields.resultFrame frame opcode.val operands.length) 0 suffix (Encoding.wordList width operands)

theorem tag_stored (frame : Port → List Bool) (opcode : Fin 16) (operands : List (Controller.Cost.Word width)) (suffix : List Bool) :
    fieldsData frame opcode operands suffix (some 13)=(Encoding.bits 4 opcode.val).reverse := by
  simp [fieldsData, WordListReader.data_at, InstructionFields.resultFrame, InstructionFields.tagFrame]

theorem count_stored (frame : Port → List Bool) (opcode : Fin 16) (operands : List (Controller.Cost.Word width)) (suffix : List Bool) :
    fieldsData frame opcode operands suffix (some 12)=List.replicate operands.length true := by
  simp [fieldsData, WordListReader.data_at, InstructionFields.resultFrame]

theorem status_clean (frame : Port → List Bool) (opcode : Fin 16) (operands : List (Controller.Cost.Word width)) (suffix : List Bool) :
    fieldsData frame opcode operands suffix none=[] := by simp [fieldsData, WordListReader.data_guard]

theorem raw_execution (frame : Port → List Bool) (width : Nat) (opcode : Fin 16)
    (operands : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ ticks peak, Execution program
      ⟨some program.main,bank frame [] (Encoding.bits 4 opcode.val++(Encoding.encodeWords width operands++suffix)) []⟩
      ⟨none,Function.update (fieldsData frame opcode operands suffix) none
        (if OpcodeArity.accepts opcode operands.length then [] else [false])⟩ ticks peak ∧
      ticks ≤ operands.length*(22*width+24)+95 := by
  obtain ⟨readPeak,reading⟩ := InstructionFields.raw_execution frame width opcode operands suffix stored countEmpty bufferEmpty savedEmpty tagEmpty
  obtain ⟨checkTicks,checkPeak,checking,bound,_⟩ := OpcodeArity.framed_execution (fieldsData frame opcode operands suffix) opcode operands.length
    (tag_stored frame opcode operands suffix) (count_stored frame opcode operands suffix) (status_clean frame opcode operands suffix)
  have accepted : Option.isNone ((fieldsData frame opcode operands suffix none).head?) = true := by simp [status_clean]
  have trace := GuardedLink.success none Option.isNone reading checking accepted
  exact ⟨_,_,trace,by omega⟩

theorem raw_status (frame : Port → List Bool) (width : Nat) (opcode : Fin 16)
    (operands : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ final ticks peak, Execution program
      ⟨some program.main,bank frame [] (Encoding.bits 4 opcode.val++(Encoding.encodeWords width operands++suffix)) []⟩ final ticks peak ∧
      Option.isNone (final.stk none).head?=OpcodeArity.accepts opcode operands.length ∧
      ticks ≤ operands.length*(22*width+24)+95 := by
  obtain ⟨ticks,peak,trace,bound⟩ := raw_execution frame width opcode operands suffix stored countEmpty bufferEmpty savedEmpty tagEmpty
  refine ⟨_,ticks,peak,trace,?_,bound⟩
  simp only [Function.update_self]
  cases OpcodeArity.accepts opcode operands.length <;> rfl

theorem execution_observes (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] (InstructionCodec.encode bound instruction++suffix) []⟩ final ticks peak ∧
      InstructionFields.observe width registers final.stk=some instruction ∧ final.stk none=[] ∧ final.stk (some 0)=suffix ∧
      ticks ≤ 66*width+167 ∧ peak ≤ (InstructionCodec.encode bound instruction++suffix).length+ambientBits frame+(66*width+167) := by
  let opcode : Fin 16 := ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩
  let operands := (InstructionCodec.fields bound instruction).2
  obtain ⟨ticks,peak,trace,timeBound⟩ := raw_execution frame width opcode operands suffix stored countEmpty bufferEmpty savedEmpty tagEmpty
  have valid : OpcodeArity.accepts opcode operands.length=true := OpcodeArity.accepts_fields bound instruction
  rw [valid, ite_eq_left (show (true : Bool)=true from rfl),
    ColdInput.update_empty _ none (status_clean frame opcode operands suffix)] at trace
  have finalTime : ticks ≤ 66*width+167 := by
    have product := Nat.mul_le_mul_right (22*width+24) (InstructionCodec.fields_length_le bound instruction)
    have identity : 3*(22*width+24)+95=66*width+167 := by ring
    change ticks ≤ _ at timeBound
    dsimp only [operands] at timeBound
    omega
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  have encoded : Encoding.bits 4 opcode.val++(Encoding.encodeWords width operands++suffix) = InstructionCodec.encode bound instruction++suffix := by
    simp only [InstructionCodec.encode, opcode, operands, List.append_assoc]
  rw [encoded] at trace space
  exact ⟨_,ticks,peak,trace,InstructionFields.endpoint_observation frame bound instruction suffix,
    status_clean frame opcode operands suffix,by simp [fieldsData, WordListReader.data_at],finalTime,by omega⟩

theorem success_shape (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (accepted : Option.isNone ((InstructionFields.result frame width input none).head?)=true) :
    ∃ opcode : Fin 16, ∃ count,
      InstructionFields.result frame width input (some 13)=(Encoding.bits 4 opcode.val).reverse ∧
      InstructionFields.result frame width input (some 12)=List.replicate count true ∧
      InstructionFields.result frame width input none=[] := by
  by_cases enough : 4 ≤ input.length
  · have tagWidth : (input.take 4).length=4 := by simp only [List.length_take, Nat.min_eq_left enough]
    obtain ⟨opcode,canonical⟩ := OpcodeArity.four_bit_canonical (input.take 4) tagWidth
    cases header : Encoding.readCount (input.drop 4) with
    | none => simp [InstructionFields.result, enough, WordListTotal.parseResult, header, bank_counter] at accepted
    | some pair =>
      rcases pair with ⟨count,payload⟩
      cases body : WordListTotal.scan width count payload [] with
      | done suffix buffer =>
        refine ⟨opcode,count,?_,?_,?_⟩
        · simpa [InstructionFields.result, enough, WordListTotal.parseResult, header, WordListTotal.afterRestore, body,
            WordListReader.data_at] using congrArg List.reverse canonical.symm
        · simp [InstructionFields.result, enough, WordListTotal.parseResult, header, WordListTotal.afterRestore, body, WordListReader.data_at]
        · simp [InstructionFields.result, enough, WordListTotal.parseResult, header, WordListTotal.afterRestore, body, WordListReader.data_at]
      | short remaining missing fragment buffer =>
        simp [InstructionFields.result, enough, WordListTotal.parseResult, header, WordListTotal.afterRestore,
          WordListTotal.beforeRestore, body, bank_counter] at accepted
  · simp [InstructionFields.result, enough, OpcodeReader.result, bank_counter] at accepted

theorem total_resources (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks peak ∧
      ticks ≤ input.length*(16*width+30)+95 ∧ peak ≤ input.length+ambientBits frame+(input.length*(16*width+30)+95) := by
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := InstructionFields.total_resources frame width input stored countEmpty bufferEmpty savedEmpty tagEmpty
  by_cases accepted : Option.isNone ((InstructionFields.result frame width input none).head?)=true
  · obtain ⟨opcode,count,tagStored,countStored,clean⟩ := success_shape frame width input accepted
    obtain ⟨checkTicks,checkPeak,checking,checkBound,_⟩ := OpcodeArity.framed_execution (InstructionFields.result frame width input)
      opcode count tagStored countStored clean
    have trace := GuardedLink.success none Option.isNone reading checking accepted
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    exact ⟨_,_,_,trace,by omega,by omega⟩
  · have rejected : Option.isNone ((InstructionFields.result frame width input none).head?)=false := by
      exact Bool.eq_false_iff.mpr accepted
    have trace := GuardedLink.failure OpcodeArity.machine none Option.isNone reading rejected
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    exact ⟨_,_,_,trace,by omega,by omega⟩

theorem total_polynomial (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) (tagEmpty : frame (some 13)=[]) :
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks peak ∧
      ticks ≤ 16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+95 ∧
      peak ≤ 16*(input.length+ambientBits frame)^2+31*(input.length+ambientBits frame)+95 := by
  obtain ⟨final,ticks,peak,trace,timeBound,_⟩ := total_resources frame width input stored countEmpty bufferEmpty savedEmpty tagEmpty
  have widthBound : width ≤ input.length+ambientBits frame := by
    have storedSize := WordListTotal.stored_width_le_ambient frame width stored
    omega
  have inputBound : input.length ≤ input.length+ambientBits frame := by omega
  have product := Nat.mul_le_mul inputBound (Nat.add_le_add_right (Nat.mul_le_mul_left 16 widthBound) 30)
  have identity : (input.length+ambientBits frame)*(16*(input.length+ambientBits frame)+30)+95 =
      16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+95 := by ring
  have finalTime : ticks ≤ 16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+95 := by rw [← identity]; omega
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  exact ⟨final,ticks,peak,trace,finalTime,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 4221 := by
  simpa [program, InstructionFields.program, OpcodeReader.program, OpcodeReader.readMachine,
    OpcodeReader.seed, OpcodeReader.saveMachine, WordListReader.program, WordListReader.payloadProgram,
    WordListReader.restorePayload, WordListReader.loop, WordListReader.body, WordListReader.moveWord,
    WordListReader.restoreMachine, WordListReader.countMachine, ColdInput.readSave, ColdInput.headerMachine,
    CountLoop.program, GuardedLink.program, StackFrames.relocate, WidthReader.program, WidthReader.counterMachine,
    StackCopy.program, WordReader.program, WordReader.cursorMachine, WordReader.reverseMachine,
    StackBlocks.reverseProgram, link, OpcodeArity.label_card] using finiteTM_resident program

end Controller.Complexity.InstructionShape
