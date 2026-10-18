module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.InstructionCollect
public import Controller.Complexity.InstructionFrontend

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A finite counted parser validates native instructions and collects their
exact encoded bytes. Every instruction read and every field transfer is
charged. The source suffix and all unselected banks remain available. -/
namespace Controller.Complexity.ProgramReader
open StackMachine WordReader

def fields (frame : Port → List Bool) (count : Nat) (buffer : List Bool) : Port → List Bool :=
  Function.update (Function.update frame (some 14) (List.replicate count true)) (some 19) buffer

def data (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) : Port → List Bool :=
  bank (fields frame count buffer) [] source []

theorem data_at (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) (target : Port) :
    data frame count source buffer target=
      if target=none then [] else if target=some 0 then source else if target=some 1 ∨ target=some 2 then []
      else if target=some 14 then List.replicate count true else if target=some 19 then buffer else frame target := by
  by_cases hc : target=none
  · subst target; simp [data, bank_counter]
  by_cases hs : target=some 0
  · subst target; simp [data, bank_source]
  by_cases hw : target=some 1
  · subst target; simp [data, bank_word]
  by_cases ht : target=some 2
  · subst target; simp [data, bank_scratch]
  have other := bank_other (fields frame count buffer) [] source [] target hc hs hw ht
  simp only [data, other]
  by_cases hn : target=some 14 <;> by_cases hb : target=some 19 <;> simp_all [fields]

theorem data_decrement (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) :
    Function.update (data frame (count+1) source buffer) (some 14) (List.replicate count true)=data frame count source buffer := by
  funext target
  by_cases hn : target=some 14 <;> simp_all [data_at]

theorem collected_data (frame : Port → List Bool) (opcode : Fin 16) (words : List (Controller.Cost.Word width))
    (count : Nat) (suffix oldBuffer newBuffer : List Bool)
    (loopEmpty : frame (some 10)=[]) (payloadEmpty : frame (some 11)=[]) (countEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (temporaryEmpty : frame (some 20)=[]) :
    InstructionCollect.fields (InstructionShape.fieldsData (fields frame count oldBuffer) opcode words suffix)
      [] [] [] newBuffer []=data frame count suffix newBuffer := by
  funext target
  by_cases hp : target=some 11 <;> by_cases hc : target=some 12 <;> by_cases hg : target=some 13 <;>
    by_cases ht : target=some 20 <;> by_cases hl : target=some 10 <;>
    simp_all [InstructionCollect.fields_at, InstructionRange.fields_at, data_at, fields]
  all_goals split_ifs <;> simp_all

def body := GuardedLink.program InstructionRange.program InstructionCollect.program none Option.isNone
def loop := CountLoop.program body (some 14) none Option.isNone

theorem body_execution (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (count : Nat) (suffix buffer : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (loopEmpty : frame (some 10)=[]) (payloadEmpty : frame (some 11)=[]) (countEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (rangeEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) (temporaryEmpty : frame (some 20)=[]) :
    ∃ ticks peak, Execution body
      ⟨some body.main,data frame count (InstructionCodec.encode bound instruction++suffix) buffer⟩
      ⟨none,data frame count suffix ((InstructionCodec.encode bound instruction).reverse++buffer)⟩ ticks peak ∧
      ticks ≤ 12*width*registers+144*width+18*registers+319 := by
  let opcode : Fin 16 := ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩
  let words := (InstructionCodec.fields bound instruction).2
  let parsed := InstructionShape.fieldsData (fields frame count buffer) opcode words suffix
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := InstructionEndpoint.execution (fields frame count buffer) bound instruction suffix
    (by simpa [fields] using stored) (by simpa [fields] using saved) (by simpa [fields] using loopEmpty)
    (by simpa [fields] using payloadEmpty) (by simpa [fields] using countEmpty) (by simpa [fields] using tagEmpty)
    (by simpa [fields] using rangeEmpty) (by simpa [fields] using scratchEmpty) (by simpa [fields] using roleEmpty)
  obtain ⟨collectPeak,collecting⟩ := InstructionCollect.ready_execution parsed opcode words
    (by simp [parsed, InstructionRange.fields_at]) (by simp [parsed, InstructionRange.fields_at])
    (by simp [parsed, InstructionRange.fields_at]) (by simp [parsed, InstructionRange.fields_at, fields, temporaryEmpty])
  have savedBuffer : parsed (some 19)=buffer := by simp [parsed, InstructionRange.fields_at, fields]
  rw [savedBuffer, collected_data frame opcode words count suffix buffer _ loopEmpty payloadEmpty countEmpty tagEmpty temporaryEmpty] at collecting
  have accepted : Option.isNone ((parsed none).head?)=true := by simp [parsed, InstructionRange.fields_at]
  have trace := GuardedLink.success none Option.isNone reading collecting accepted
  have encoded : Encoding.bits 4 opcode.val++Encoding.encodeWords width words=InstructionCodec.encode bound instruction := rfl
  rw [encoded] at trace
  have product := Nat.mul_le_mul_left (2*(width+1)) (InstructionCodec.fields_length_le bound instruction)
  have identity : 12*width*registers+138*width+18*registers+287+(2*(width+1)*3+26)=
      12*width*registers+144*width+18*registers+319 := by ring
  exact ⟨_,_,trace,by dsimp only [words] at *; omega⟩

theorem loop_execution (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix buffer : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (loopEmpty : frame (some 10)=[]) (payloadEmpty : frame (some 11)=[]) (countEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (rangeEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) (temporaryEmpty : frame (some 20)=[]) :
    ∃ ticks peak, Execution loop
      ⟨some loop.main,data frame instructions.length (InstructionCodec.encodeMany bound instructions++suffix) buffer⟩
      ⟨none,data frame 0 suffix ((InstructionCodec.encodeMany bound instructions).reverse++buffer)⟩ ticks peak ∧
      ticks ≤ instructions.length*(12*width*registers+144*width+18*registers+320)+2 := by
  induction instructions generalizing buffer with
  | nil =>
    have trace := CountLoop.empty body (some 14) none Option.isNone (data frame 0 suffix buffer) (by simp [data_at])
    exact ⟨2,_,by simpa only [loop, InstructionCodec.encodeMany, List.flatMap_nil, List.nil_append, List.reverse_nil, List.length_nil] using trace,by simp⟩
  | cons instruction instructions ih =>
    obtain ⟨tailTicks,tailPeak,tailRun,tailBound⟩ := ih ((InstructionCodec.encode bound instruction).reverse++buffer)
    obtain ⟨bodyTicks,bodyPeak,bodyRun,bodyBound⟩ := body_execution frame bound instruction instructions.length
      (InstructionCodec.encodeMany bound instructions++suffix) buffer stored saved loopEmpty payloadEmpty countEmpty tagEmpty rangeEmpty scratchEmpty roleEmpty temporaryEmpty
    have counted : data frame (instructions.length+1)
        (InstructionCodec.encode bound instruction++(InstructionCodec.encodeMany bound instructions++suffix)) buffer (some 14)=
        true :: List.replicate instructions.length true := by simp [data_at, List.replicate_succ]
    have adjusted : Execution body
        ⟨some body.main,Function.update (data frame (instructions.length+1)
          (InstructionCodec.encode bound instruction++(InstructionCodec.encodeMany bound instructions++suffix)) buffer)
          (some 14) (List.replicate instructions.length true)⟩
        ⟨none,data frame instructions.length (InstructionCodec.encodeMany bound instructions++suffix)
          ((InstructionCodec.encode bound instruction).reverse++buffer)⟩ bodyTicks bodyPeak := by
      simpa only [data_decrement] using bodyRun
    obtain ⟨peak,trace⟩ := CountLoop.next (some 14) none Option.isNone counted adjusted (by simp [data_at]) tailRun
    refine ⟨bodyTicks+tailTicks+1,peak,?_,?_⟩
    · simpa only [loop, InstructionCodec.encodeMany, List.flatMap_cons, List.length_cons, List.append_assoc, List.reverse_append] using trace
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def reversePorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 19) none (some 2) (by decide) (by decide) (by decide)

theorem reversePorts_apply (port : Option Bool) : reversePorts port=
    (match port with | none => some 19 | some false => none | some true => some 2) := rfl

theorem reverse_storage (frame : Port → List Bool) (source buffer : List Bool) :
    StackFrames.embedStorage reversePorts (data frame 0 source []) (StackBlocks.layout buffer [] [])=data frame 0 source buffer := by
  funext target
  by_cases hb : target=some 19 <;> by_cases hc : target=none <;> by_cases ht : target=some 2 <;>
    simp_all [StackFrames.embedStorage, reversePorts_apply, StackBlocks.layout, data_at]

def restoreMachine := StackFrames.relocate reversePorts StackBlocks.reverseProgram
def restorePayload := GuardedLink.program loop restoreMachine none Option.isNone

theorem restore_execution (frame : Port → List Bool) (source buffer : List Bool) :
    ∃ peak, Execution restoreMachine ⟨some restoreMachine.main,data frame 0 source buffer⟩
      ⟨none,data frame 0 source buffer.reverse⟩ (6*buffer.length+6) peak := by
  have trace := StackFrames.reversal reversePorts (data frame 0 source []) buffer
  exact ⟨_,by simpa only [restoreMachine, StackFrames.relocate, StackFrames.embedState,
    StackBlocks.initial_layout, StackBlocks.terminal_layout, reverse_storage] using trace⟩

theorem payload_execution (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (loopEmpty : frame (some 10)=[]) (payloadEmpty : frame (some 11)=[]) (countEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (rangeEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) (temporaryEmpty : frame (some 20)=[]) :
    ∃ ticks peak, Execution restorePayload
      ⟨some restorePayload.main,data frame instructions.length (InstructionCodec.encodeMany bound instructions++suffix) []⟩
      ⟨none,data frame 0 suffix (InstructionCodec.encodeMany bound instructions)⟩ ticks peak ∧
      ticks ≤ instructions.length*(12*width*registers+162*width+18*registers+368)+8 := by
  obtain ⟨loopTicks,loopPeak,loopRun,loopBound⟩ := loop_execution frame bound instructions suffix [] stored saved loopEmpty payloadEmpty countEmpty tagEmpty rangeEmpty scratchEmpty roleEmpty temporaryEmpty
  simp only [List.append_nil] at loopRun
  obtain ⟨restorePeak,restoring⟩ := restore_execution frame suffix (InstructionCodec.encodeMany bound instructions).reverse
  simp only [List.reverse_reverse, List.length_reverse] at restoring
  have trace := GuardedLink.success none Option.isNone loopRun restoring (by simp [data_at])
  have product := Nat.mul_le_mul_left 6 (InstructionCodec.encodeMany_length_le bound instructions)
  have identity : instructions.length*(12*width*registers+144*width+18*registers+320)+2+
      (6*((3*width+8)*instructions.length)+6)=instructions.length*(12*width*registers+162*width+18*registers+368)+8 := by ring
  exact ⟨_,_,trace,by omega⟩

def countPorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 14) (some 15) (some 2) (by decide) (by decide) (by decide)

theorem countPorts_apply (port : Option Bool) : countPorts port=
    (match port with | none => some 14 | some false => some 15 | some true => some 2) := rfl

def countMachine := StackFrames.relocate countPorts StackCopy.program
def payloadProgram := link countMachine restorePayload
def program := GuardedLink.program (ColdInput.readSave 14) payloadProgram none Option.isNone

theorem copy_count_execution (frame : Port → List Bool) (count : Nat) (source : List Bool)
    (savedEmpty : frame (some 15)=[]) :
    ∃ peak, Execution countMachine ⟨some countMachine.main,data frame count source []⟩
      ⟨none,data (Function.update frame (some 15) (List.replicate count true)) count source []⟩ (5*count+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution countPorts (data frame count source []) (by simp [countPorts_apply, data_at])
  have output : Function.update (data frame count source []) (countPorts (some false))
      (data frame count source [] (countPorts none)++data frame count source [] (countPorts (some false)))=
      data (Function.update frame (some 15) (List.replicate count true)) count source [] := by
    funext target
    by_cases hd : target=some 15 <;> simp_all [countPorts_apply, data_at]
  rw [output] at trace
  exact ⟨peak,by simpa [countMachine, StackFrames.relocate, countPorts_apply, data_at] using trace⟩

theorem header_data (frame : Port → List Bool) (count : Nat) (source : List Bool) (bufferEmpty : frame (some 19)=[]) :
    bank (Function.update frame (some 14) (List.replicate count true)) [] source []=data frame count source [] := by
  unfold data fields
  rw [ColdInput.update_empty _ (some 19) (by simpa using bufferEmpty)]

theorem execution (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (loopEmpty : frame (some 10)=[]) (payloadEmpty : frame (some 11)=[]) (countEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (workingCountEmpty : frame (some 14)=[]) (savedCountEmpty : frame (some 15)=[])
    (rangeEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[]) (roleEmpty : frame (some 18)=[])
    (bufferEmpty : frame (some 19)=[]) (temporaryEmpty : frame (some 20)=[]) :
    ∃ ticks peak, Execution program
      ⟨some program.main,bank frame [] (Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions++suffix)) []⟩
      ⟨none,data (Function.update frame (some 15) (List.replicate instructions.length true)) 0 suffix (InstructionCodec.encodeMany bound instructions)⟩ ticks peak ∧
      ticks ≤ instructions.length*(12*width*registers+162*width+18*registers+377)+16 ∧
      peak ≤ (Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions++suffix)).length+ambientBits frame+
        (instructions.length*(12*width*registers+162*width+18*registers+377)+16) := by
  let savedFrame := Function.update frame (some 15) (List.replicate instructions.length true)
  have header := ColdInput.read_save_execution frame 14 (by decide) (by decide) (by decide) instructions.length
    (InstructionCodec.encodeMany bound instructions++suffix) [] workingCountEmpty
  rw [header_data frame instructions.length _ bufferEmpty] at header
  obtain ⟨copyPeak,copying⟩ := copy_count_execution frame instructions.length (InstructionCodec.encodeMany bound instructions++suffix) savedCountEmpty
  obtain ⟨payloadTicks,payloadPeak,payloadRun,payloadBound⟩ := payload_execution savedFrame bound instructions suffix
    (by simp [savedFrame, stored]) (by simp [savedFrame, saved]) (by simp [savedFrame, loopEmpty])
    (by simp [savedFrame, payloadEmpty]) (by simp [savedFrame, countEmpty]) (by simp [savedFrame, tagEmpty])
    (by simp [savedFrame, rangeEmpty]) (by simp [savedFrame, scratchEmpty]) (by simp [savedFrame, roleEmpty]) (by simp [savedFrame, temporaryEmpty])
  have tail := copying.link payloadRun
  have trace := GuardedLink.success none Option.isNone header tail (by simp [data_at])
  have identity : (4*instructions.length+4)+(5*instructions.length+4+
      (instructions.length*(12*width*registers+162*width+18*registers+368)+8))=
      instructions.length*(12*width*registers+162*width+18*registers+377)+16 := by ring
  have finalTime : (4*instructions.length+4)+(5*instructions.length+4+payloadTicks) ≤
      instructions.length*(12*width*registers+162*width+18*registers+377)+16 := by rw [← identity]; omega
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  exact ⟨_,_,trace,finalTime,by simp only [List.length_nil, Nat.add_zero]; omega⟩

def observe (width registers : Nat) (storage : Port → List Bool) : Option (Controller.Cost.Program width registers) :=
  InstructionCodec.decodeProgram width registers (storage (some 15)++false :: storage (some 19))

theorem endpoint_observation (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool) :
    observe width registers (data (Function.update frame (some 15) (List.replicate instructions.length true))
      0 suffix (InstructionCodec.encodeMany bound instructions))=some instructions.toArray := by
  simp only [observe]
  simp [data_at]
  change InstructionCodec.decodeProgram width registers
    (Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions))=some instructions.toArray
  simpa [InstructionCodec.encodeProgram] using InstructionCodec.decode_encodeProgram bound instructions.toArray

theorem execution_observes (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (loopEmpty : frame (some 10)=[]) (payloadEmpty : frame (some 11)=[]) (countEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (workingCountEmpty : frame (some 14)=[]) (savedCountEmpty : frame (some 15)=[])
    (rangeEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[]) (roleEmpty : frame (some 18)=[])
    (bufferEmpty : frame (some 19)=[]) (temporaryEmpty : frame (some 20)=[]) :
    ∃ final ticks peak, Execution program
      ⟨some program.main,bank frame [] (Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions++suffix)) []⟩ final ticks peak ∧
      final.pc=none ∧ observe width registers final.stk=some instructions.toArray ∧
      final.stk none=[] ∧ final.stk (some 0)=suffix ∧ final.stk (some 15)=List.replicate instructions.length true ∧
      ticks ≤ instructions.length*(12*width*registers+162*width+18*registers+377)+16 ∧
      peak ≤ (Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions++suffix)).length+ambientBits frame+
        (instructions.length*(12*width*registers+162*width+18*registers+377)+16) := by
  obtain ⟨ticks,peak,trace,timeBound,spaceBound⟩ := execution frame bound instructions suffix stored saved loopEmpty payloadEmpty countEmpty tagEmpty
    workingCountEmpty savedCountEmpty rangeEmpty scratchEmpty roleEmpty bufferEmpty temporaryEmpty
  exact ⟨_,ticks,peak,trace,rfl,endpoint_observation frame bound instructions suffix,by simp [data_at],
    by simp [data_at],by simp [data_at],timeBound,spaceBound⟩

theorem initial_storage_polynomial (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (loopEmpty : frame (some 10)=[]) (payloadEmpty : frame (some 11)=[]) (countEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (workingCountEmpty : frame (some 14)=[]) (savedCountEmpty : frame (some 15)=[])
    (rangeEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[]) (roleEmpty : frame (some 18)=[])
    (bufferEmpty : frame (some 19)=[]) (temporaryEmpty : frame (some 20)=[]) :
    let input := Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions++suffix)
    let size := input.length+ambientBits frame
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks peak ∧ final.pc=none ∧
      observe width registers final.stk=some instructions.toArray ∧ final.stk (some 0)=suffix ∧
      ticks ≤ 12*size^3+180*size^2+377*size+16 ∧ peak ≤ 12*size^3+180*size^2+378*size+16 := by
  let input := Encoding.frameCount instructions.length (InstructionCodec.encodeMany bound instructions++suffix)
  let size := input.length+ambientBits frame
  obtain ⟨final,ticks,peak,trace,halted,observed,_,source,_,timeBound,_⟩ := execution_observes frame bound instructions suffix
    stored saved loopEmpty payloadEmpty countEmpty tagEmpty workingCountEmpty savedCountEmpty rangeEmpty scratchEmpty roleEmpty bufferEmpty temporaryEmpty
  have widthBound : width ≤ size := (WordListTotal.stored_width_le_ambient frame width stored).trans (by dsimp [size]; omega)
  have registerBound : registers ≤ size := (InstructionRange.stored_registers_le_ambient frame registers saved).trans (by dsimp [size]; omega)
  have countBound : instructions.length ≤ size := by dsimp [size, input, Encoding.frameCount]; simp only [List.length_append, List.length_replicate, List.length_cons]; omega
  have wordProduct := Nat.mul_le_mul_left 12 (Nat.mul_le_mul widthBound registerBound)
  have coefficient : 12*width*registers+162*width+18*registers+377 ≤ 12*(size*size)+180*size+377 := by
    rw [Nat.mul_assoc]
    omega
  have product := Nat.mul_le_mul countBound coefficient
  have identity : size*(12*(size*size)+180*size+377)+16=12*size^3+180*size^2+377*size+16 := by ring
  have finalTime : ticks ≤ 12*size^3+180*size^2+377*size+16 :=
    timeBound.trans ((Nat.add_le_add_right product 16).trans_eq identity)
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  change peak ≤ size+ticks at space
  have peakIdentity : size+(12*size^3+180*size^2+377*size+16)=12*size^3+180*size^2+378*size+16 := by ring
  exact ⟨final,ticks,peak,trace,halted,observed,source,finalTime,
    space.trans ((Nat.add_le_add_left finalTime size).trans_eq peakIdentity)⟩

open scoped BigOperators in
theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 7677 := by
  simpa only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin, OpcodeArity.label_card, OpcodeRoles.label_card,
    OperandCheck.Label, RegisterRange.Label, WordBound.Label, WordBound.BodyLabel, Nat.reduceAdd, Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.ProgramReader
