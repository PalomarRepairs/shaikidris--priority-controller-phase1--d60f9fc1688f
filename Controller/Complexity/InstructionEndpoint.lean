module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.InstructionRange

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Successful instruction checking restores a reusable clean workspace.
The exact final bank retains the decoded tag, operand count and payload,
the unread source suffix, both global headers and all ambient data. -/
namespace Controller.Complexity.InstructionEndpoint
open StackMachine WordReader

theorem scan_source (width registers : Nat) (roles source suffix : List Bool)
    (finished : OperandLoop.scan width registers roles source=.done suffix) :
    suffix=source.drop (width*roles.length) := by
  induction roles generalizing source with
  | nil => simpa [OperandLoop.scan] using finished.symm
  | cons bit roles ih =>
    by_cases enough : width ≤ source.length
    · by_cases accepted : OperandLoop.accepts bit (source.take width) registers=true
      · have rest : OperandLoop.scan width registers roles (source.drop width)=.done suffix := by
          simpa only [OperandLoop.scan, ite_eq_left enough, accepted, ite_true] using finished
        rw [ih _ rest, List.drop_drop]
        congr 1
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      · have rejected : OperandLoop.accepts bit (source.take width) registers=false := Bool.eq_false_iff.mpr accepted
        simp [OperandLoop.scan, enough, rejected] at finished
    · simp [OperandLoop.scan, enough] at finished

theorem scan_valid (width registers : Nat) (roles : List Bool) (words : List (Controller.Cost.Word width))
    (suffix : List Bool) (same : roles.length=words.length)
    (valid : InstructionRange.acceptsWords registers roles words=true) :
    OperandLoop.scan width registers roles (Encoding.wordList width words++suffix)=.done suffix := by
  have accepted := InstructionRange.scan_encoded width registers roles words suffix same
  rw [valid] at accepted
  cases result : OperandLoop.scan width registers roles (Encoding.wordList width words++suffix) with
  | done actual =>
    have residual := scan_source width registers roles (Encoding.wordList width words++suffix) actual result
    have count : width*roles.length=(Encoding.wordList width words).length := by simp [same]
    rw [count, List.drop_left] at residual
    exact congrArg OperandLoop.Result.done residual
  | invalid rest source => simp [result, InstructionRange.Result.accepted] at accepted
  | short rest missing fragment => simp [result, InstructionRange.Result.accepted] at accepted

theorem restore_done (frame : Port → List Bool) (roles suffix : List Bool)
    (clean : frame none=[]) (source : frame (some 0)=suffix) (word : frame (some 1)=[])
    (scratch : frame (some 2)=[]) (count : frame (some 10)=[]) (first : frame (some 16)=[])
    (second : frame (some 17)=[]) (role : frame (some 18)=[]) :
    OperandLoop.endpoint (Function.update frame (some 18) roles) (.done suffix)=frame := by
  funext target
  by_cases hc : target=none
  · subst target; simp [OperandLoop.endpoint, OperandLoop.data_at, clean]
  by_cases hs : target=some 0
  · subst target; simp [OperandLoop.endpoint, OperandLoop.data_at, source]
  by_cases hw : target=some 1
  · subst target; simp [OperandLoop.endpoint, OperandLoop.data_at, word]
  by_cases ht : target=some 2
  · subst target; simp [OperandLoop.endpoint, OperandLoop.data_at, scratch]
  by_cases hn : target=some 10
  · subst target; simp [OperandLoop.endpoint, OperandLoop.data_at, count]
  by_cases ha : target=some 16
  · subst target; simp [OperandLoop.endpoint, OperandLoop.data_at, first]
  by_cases hb : target=some 17
  · subst target; simp [OperandLoop.endpoint, OperandLoop.data_at, second]
  by_cases hr : target=some 18
  · subst target; simp [OperandLoop.endpoint, OperandLoop.data_at, role]
  simp [OperandLoop.endpoint, OperandLoop.data_at, hc, hs, hw, ht, hn, ha, hb, hr]

abbrev program := InstructionRange.program

theorem raw_execution (frame : Port → List Bool) (width registers : Nat) (opcode : Fin 16)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (decoderValid : (InstructionCodec.readFields registers opcode.val words).isSome=true)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (boundEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] (Encoding.bits 4 opcode.val++(Encoding.encodeWords width words++suffix)) []⟩
      ⟨none,InstructionShape.fieldsData frame opcode words suffix⟩ ticks peak ∧
      ticks ≤ 12*width*registers+138*width+18*registers+287 ∧
      peak ≤ (Encoding.bits 4 opcode.val++(Encoding.encodeWords width words++suffix)).length+ambientBits frame+
        (12*width*registers+138*width+18*registers+287) := by
  let parsed := InstructionShape.fieldsData frame opcode words suffix
  have accepted : OpcodeArity.accepts opcode words.length=true := by
    cases arity : OpcodeArity.accepts opcode words.length with
    | true => rfl
    | false => have impossible := InstructionRange.wrong_arity opcode words registers arity; rw [decoderValid] at impossible; cases impossible
  obtain ⟨roles,roleDecoded,roleLength⟩ := InstructionRange.roles_of_arity opcode words.length accepted
  have valid : InstructionRange.acceptsWords registers roles words=true := by
    have semantic := InstructionRange.decoder_status opcode registers words
    rw [roleDecoded] at semantic
    simpa only [Option.any_some, decoderValid] using semantic
  have scanned := scan_valid width registers roles words suffix roleLength valid
  obtain ⟨shapeTicks,shapePeak,shapeRun,shapeBound⟩ := InstructionShape.raw_execution frame width opcode words suffix
    stored countEmpty bufferEmpty savedEmpty tagEmpty
  have clean : parsed none=[] := by simp [parsed, InstructionRange.fields_at]
  rw [accepted, ite_eq_left (show (true : Bool)=true from rfl), ColdInput.update_empty _ none clean] at shapeRun
  obtain ⟨operandTicks,operandPeak,operandRun,operandBound⟩ := InstructionOperands.execution parsed width registers opcode roles roleDecoded
    (by simp [parsed, InstructionRange.fields_at]) clean (by simp [parsed, InstructionRange.fields_at])
    (by simp [parsed, InstructionRange.fields_at]) (by simp [parsed, InstructionRange.fields_at])
    (by simp [parsed, InstructionRange.fields_at, boundEmpty]) (by simp [parsed, InstructionRange.fields_at, scratchEmpty])
    (by simp [parsed, InstructionRange.fields_at, roleEmpty]) (by simp [parsed, InstructionRange.fields_at, roleLength])
    (by simp [parsed, InstructionRange.fields_at, stored]) (by simp [parsed, InstructionRange.fields_at, saved])
  have payload : parsed (some 11)++parsed (some 0)=Encoding.wordList width words++suffix := by simp [parsed, InstructionRange.fields_at]
  rw [payload, scanned, restore_done parsed roles suffix clean (by simp [parsed, InstructionRange.fields_at])
    (by simp [parsed, InstructionRange.fields_at]) (by simp [parsed, InstructionRange.fields_at])
    (by simp [parsed, InstructionRange.fields_at]) (by simp [parsed, InstructionRange.fields_at, boundEmpty])
    (by simp [parsed, InstructionRange.fields_at, scratchEmpty]) (by simp [parsed, InstructionRange.fields_at, roleEmpty])] at operandRun
  have trace := GuardedLink.success none Option.isNone shapeRun operandRun (by simp [clean])
  simp [parsed, InstructionRange.fields_at, roleLength] at operandBound
  have combined : shapeTicks+operandTicks ≤ words.length*(width*(4*registers+46)+6*registers+56)+119 := by
    have identity : words.length*(width*(4*registers+46)+6*registers+56)+119=
        (words.length*(22*width+24)+95)+
          (5*(width*words.length)+words.length*(width*(4*registers+19)+6*registers+32)+24) := by ring
    rw [identity]
    omega
  have countBound : words.length ≤ 3 := by
    unfold OpcodeArity.accepts at accepted
    cases arity : OpcodeArity.expectedArity opcode with
    | none => simp [arity] at accepted
    | some value => have same : words.length=value.val := by simpa [arity] using accepted
                    omega
  have product := Nat.mul_le_mul_right (width*(4*registers+46)+6*registers+56) countBound
  have expanded : 3*(width*(4*registers+46)+6*registers+56)+119=12*width*registers+138*width+18*registers+287 := by ring
  have finalTime : shapeTicks+operandTicks ≤ 12*width*registers+138*width+18*registers+287 := by omega
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  exact ⟨_,_,trace,finalTime,by omega⟩

theorem execution (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (boundEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) :
    let opcode : Fin 16 := ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩
    let words := (InstructionCodec.fields bound instruction).2
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] (InstructionCodec.encode bound instruction++suffix) []⟩
      ⟨none,InstructionShape.fieldsData frame opcode words suffix⟩ ticks peak ∧
      ticks ≤ 12*width*registers+138*width+18*registers+287 ∧
      peak ≤ (InstructionCodec.encode bound instruction++suffix).length+ambientBits frame+
        (12*width*registers+138*width+18*registers+287) := by
  let opcode : Fin 16 := ⟨(InstructionCodec.fields bound instruction).1,InstructionCodec.fields_tag_lt bound instruction⟩
  let words := (InstructionCodec.fields bound instruction).2
  have valid : (InstructionCodec.readFields registers opcode.val words).isSome=true := by
    simp only [opcode, words, InstructionCodec.readFields_fields, Option.isSome_some]
  simpa only [InstructionCodec.encode, List.append_assoc, opcode, words] using
    raw_execution frame width registers opcode words suffix valid stored saved countEmpty bufferEmpty savedEmpty tagEmpty boundEmpty scratchEmpty roleEmpty

theorem execution_observes (frame : Port → List Bool) (bound : registers ≤ 2^width)
    (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (boundEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) :
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] (InstructionCodec.encode bound instruction++suffix) []⟩ final ticks peak ∧
      final.pc=none ∧ InstructionFields.observe width registers final.stk=some instruction ∧
      final.stk none=[] ∧ final.stk (some 0)=suffix ∧
      ticks ≤ 12*width*registers+138*width+18*registers+287 ∧
      peak ≤ (InstructionCodec.encode bound instruction++suffix).length+ambientBits frame+
        (12*width*registers+138*width+18*registers+287) := by
  obtain ⟨ticks,peak,trace,timeBound,spaceBound⟩ := execution frame bound instruction suffix stored saved countEmpty bufferEmpty savedEmpty tagEmpty boundEmpty scratchEmpty roleEmpty
  exact ⟨_,ticks,peak,trace,rfl,InstructionFields.endpoint_observation frame bound instruction suffix,
    by simp [InstructionRange.fields_at],by simp [InstructionRange.fields_at],timeBound,spaceBound⟩

end Controller.Complexity.InstructionEndpoint
