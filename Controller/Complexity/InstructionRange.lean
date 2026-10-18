module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.InstructionOperands
public import Controller.Complexity.InstructionShape

public import Mathlib.Tactic.FinCases

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Executed operand roles correspond to the native instruction decoder.
The complete instruction checker guards the operand pass after structural
parsing and opcode/arity checks. -/
namespace Controller.Complexity.InstructionRange
open StackMachine WordReader
open scoped BigOperators

def acceptsWords (registers : Nat) : List Bool → List (Controller.Cost.Word width) → Bool
  | [],[] => true
  | bit :: roles,word :: words => (!bit || decide (word.val < registers)) && acceptsWords registers roles words
  | _,_ => false

def Result.accepted : OperandLoop.Result → Bool
  | .done _ => true
  | _ => false

theorem endpoint_status (frame : Port → List Bool) (result : OperandLoop.Result) :
    Option.isNone ((OperandLoop.endpoint frame result none).head?)=Result.accepted result := by
  cases result <;> simp [OperandLoop.endpoint, OperandLoop.data_at, Result.accepted]

theorem scan_encoded (width registers : Nat) (roles : List Bool) (words : List (Controller.Cost.Word width))
    (suffix : List Bool) (same : roles.length=words.length) :
    Result.accepted (OperandLoop.scan width registers roles (Encoding.wordList width words++suffix))=
      acceptsWords registers roles words := by
  induction roles generalizing words with
  | nil => cases words <;> simp_all [OperandLoop.scan, Result.accepted, acceptsWords]
  | cons bit roles ih =>
    cases words with
    | nil => simp at same
    | cons word words =>
      have tailLength : roles.length=words.length := by simpa using same
      have enough : width ≤ (Encoding.wordList width (word :: words)++suffix).length := by
        simp only [Encoding.wordList_length, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      have head : (Encoding.wordList width (word :: words)++suffix).take width=Encoding.bits width word.val := by
        simp only [Encoding.wordList, List.flatMap_cons, List.append_assoc]
        exact List.take_left' (by simp)
      have tail : (Encoding.wordList width (word :: words)++suffix).drop width=Encoding.wordList width words++suffix := by
        simp only [Encoding.wordList, List.flatMap_cons, List.append_assoc]
        exact List.drop_left' (by simp)
      have decision : OperandLoop.accepts bit (Encoding.bits width word.val) registers=
          (!bit || decide (word.val < registers)) := by
        simp only [OperandLoop.accepts, Encoding.value_bits width word.val word.isLt]
      simp only [OperandLoop.scan, ite_eq_left enough, head, tail, decision, acceptsWords]
      cases (!bit || decide (word.val < registers)) <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Result.accepted, Bool.false_and, Bool.true_and]
      exact ih words tailLength

theorem decoder_status (opcode : Fin 16) (registers : Nat) (words : List (Controller.Cost.Word width)) :
    (OpcodeRoles.roles opcode).any (fun roles => acceptsWords registers roles words)=
      (InstructionCodec.readFields registers opcode.val words).isSome := by
  fin_cases opcode <;>
    rcases words with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
    simp [OpcodeRoles.roles, acceptsWords, InstructionCodec.readFields, InstructionCodec.readRegister] <;>
    split_ifs <;> simp_all [Option.bind]

def program := GuardedLink.program InstructionShape.program InstructionOperands.program none Option.isNone

theorem roles_of_arity (opcode : Fin 16) (count : Nat) (accepted : OpcodeArity.accepts opcode count=true) :
    ∃ roles, OpcodeRoles.roles opcode=some roles ∧ roles.length=count := by
  have same := OpcodeRoles.roles_arity opcode
  cases roleCase : OpcodeRoles.roles opcode with
  | none =>
    rw [roleCase] at same
    cases arityCase : OpcodeArity.expectedArity opcode with
    | none => simp [OpcodeArity.accepts, arityCase] at accepted
    | some arity => simp [arityCase] at same
  | some roles =>
    rw [roleCase] at same
    cases arityCase : OpcodeArity.expectedArity opcode with
    | none => simp [arityCase] at same
    | some arity =>
      simp only [arityCase, Option.map_some, Option.some.injEq] at same
      have counted : count=arity.val := by simpa [OpcodeArity.accepts, arityCase] using accepted
      exact ⟨roles,rfl,same.trans counted.symm⟩

theorem wrong_arity (opcode : Fin 16) (words : List (Controller.Cost.Word width)) (registers : Nat)
    (rejected : OpcodeArity.accepts opcode words.length=false) :
    (InstructionCodec.readFields registers opcode.val words).isSome=false := by
  fin_cases opcode <;>
    rcases words with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
    simp_all [OpcodeArity.accepts, OpcodeArity.expectedArity, InstructionCodec.readFields]

theorem fields_at (frame : Port → List Bool) (opcode : Fin 16)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool) (target : Port) :
    InstructionShape.fieldsData frame opcode words suffix target=
      if target=none then [] else if target=some 0 then suffix else if target=some 1 ∨ target=some 2 ∨ target=some 10 then []
      else if target=some 11 then Encoding.wordList width words else if target=some 12 then List.replicate words.length true
      else if target=some 13 then (Encoding.bits 4 opcode.val).reverse else frame target := by
  by_cases hc : target=none
  · subst target; simp [InstructionShape.fieldsData, WordListReader.data_at]
  by_cases hs : target=some 0
  · subst target; simp [InstructionShape.fieldsData, WordListReader.data_at]
  by_cases hw : target=some 1
  · subst target; simp [InstructionShape.fieldsData, WordListReader.data_at]
  by_cases ht : target=some 2
  · subst target; simp [InstructionShape.fieldsData, WordListReader.data_at]
  by_cases hn : target=some 10
  · subst target; simp [InstructionShape.fieldsData, WordListReader.data_at]
  by_cases hb : target=some 11
  · subst target; simp [InstructionShape.fieldsData, WordListReader.data_at]
  by_cases hd : target=some 12
  · subst target; simp [InstructionShape.fieldsData, WordListReader.data_at, InstructionFields.resultFrame]
  by_cases hg : target=some 13
  · subst target; simp [InstructionShape.fieldsData, WordListReader.data_at, InstructionFields.resultFrame, InstructionFields.tagFrame]
  simp [InstructionShape.fieldsData, WordListReader.data_at, InstructionFields.resultFrame, InstructionFields.tagFrame,
    hc, hs, hw, ht, hn, hb, hd, hg]

theorem raw_status (frame : Port → List Bool) (width registers : Nat) (opcode : Fin 16)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (boundEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) :
    ∃ final ticks peak, Execution program
      ⟨some program.main,bank frame [] (Encoding.bits 4 opcode.val++(Encoding.encodeWords width words++suffix)) []⟩ final ticks peak ∧
      final.pc=none ∧
      Option.isNone (final.stk none).head?=(InstructionCodec.readFields registers opcode.val words).isSome ∧
      ticks ≤ words.length*(width*(4*registers+46)+6*registers+56)+119 := by
  obtain ⟨shapeTicks,shapePeak,shapeRun,shapeBound⟩ := InstructionShape.raw_execution frame width opcode words suffix
    stored countEmpty bufferEmpty savedEmpty tagEmpty
  let parsed := InstructionShape.fieldsData frame opcode words suffix
  have clean : parsed none=[] := by simp [parsed, fields_at]
  by_cases accepted : OpcodeArity.accepts opcode words.length=true
  · rw [accepted, ite_eq_left (show (true : Bool)=true from rfl), ColdInput.update_empty _ none clean] at shapeRun
    obtain ⟨roles,roleDecoded,roleLength⟩ := roles_of_arity opcode words.length accepted
    obtain ⟨operandTicks,operandPeak,operandRun,operandBound⟩ := InstructionOperands.execution parsed width registers opcode roles roleDecoded
      (by simp [parsed, fields_at]) clean (by simp [parsed, fields_at]) (by simp [parsed, fields_at])
      (by simp [parsed, fields_at]) (by simp [parsed, fields_at, boundEmpty]) (by simp [parsed, fields_at, scratchEmpty])
      (by simp [parsed, fields_at, roleEmpty]) (by simp [parsed, fields_at, roleLength])
      (by simp [parsed, fields_at, stored]) (by simp [parsed, fields_at, saved])
    have trace := GuardedLink.success none Option.isNone shapeRun operandRun (by simp [clean])
    refine ⟨_,_,_,trace,rfl,?_,?_⟩
    · rw [endpoint_status]
      simp [parsed, fields_at]
      rw [scan_encoded width registers roles words suffix roleLength]
      have semantic := decoder_status opcode registers words
      simpa only [roleDecoded, Option.any_some] using semantic
    · simp [parsed, fields_at, roleLength] at operandBound
      have identity : words.length*(width*(4*registers+46)+6*registers+56)+119=
          (words.length*(22*width+24)+95)+
            (5*(width*words.length)+words.length*(width*(4*registers+19)+6*registers+32)+24) := by ring
      rw [identity]
      omega
  · have rejected : OpcodeArity.accepts opcode words.length=false := Bool.eq_false_iff.mpr accepted
    rw [rejected, ite_eq_right (by decide : ¬(false : Bool)=true)] at shapeRun
    have trace := GuardedLink.failure InstructionOperands.program none Option.isNone shapeRun (by simp)
    refine ⟨_,_,_,trace,rfl,?_,?_⟩
    · simpa only [Function.update_self, List.head?_cons, Option.isNone_some] using (wrong_arity opcode words registers rejected).symm
    · have coefficient : 22*width+24 ≤ width*(4*registers+46)+6*registers+56 := by
        have positive := Nat.zero_le (width*(4*registers+24))
        have identity : width*(4*registers+46)=22*width+width*(4*registers+24) := by ring
        omega
      have product := Nat.mul_le_mul_left words.length coefficient
      omega

theorem stored_registers_le_ambient (frame : Port → List Bool) (registers : Nat)
    (saved : frame (some 9)=List.replicate registers true) : registers ≤ ambientBits frame := by
  have bound := Finset.single_le_sum (f := fun target : Port => (bank frame [] [] [] target).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 9))
  rw [bank_other frame [] [] [] (some 9) (by decide) (by decide) (by decide) (by decide),
    saved, List.length_replicate] at bound
  have total := bank_live frame (none : Option Unit) [] [] []
  simp only [live, List.length_nil, Nat.zero_add, Nat.add_zero] at total
  exact bound.trans_eq total

theorem raw_polynomial (frame : Port → List Bool) (width registers : Nat) (opcode : Fin 16)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (boundEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) :
    let input := Encoding.bits 4 opcode.val++(Encoding.encodeWords width words++suffix)
    let initialSize := input.length+ambientBits frame
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks peak ∧
      final.pc=none ∧
      Option.isNone (final.stk none).head?=(InstructionCodec.readFields registers opcode.val words).isSome ∧
      ticks ≤ 4*initialSize^3+52*initialSize^2+56*initialSize+119 ∧
      peak ≤ 4*initialSize^3+52*initialSize^2+57*initialSize+119 := by
  let input := Encoding.bits 4 opcode.val++(Encoding.encodeWords width words++suffix)
  let initialSize := input.length+ambientBits frame
  obtain ⟨final,ticks,peak,trace,halted,status,timeBound⟩ := raw_status frame width registers opcode words suffix
    stored saved countEmpty bufferEmpty savedEmpty tagEmpty boundEmpty scratchEmpty roleEmpty
  have widthBound : width ≤ initialSize := (WordListTotal.stored_width_le_ambient frame width stored).trans (by dsimp [initialSize]; omega)
  have registerBound : registers ≤ initialSize := (stored_registers_le_ambient frame registers saved).trans (by dsimp [initialSize]; omega)
  have countBound : words.length ≤ initialSize := by
    have expansion : (width+1)*words.length=width*words.length+words.length := by ring
    dsimp [initialSize, input]
    simp only [List.length_append, Encoding.bits_length, Encoding.encodeWords_length, expansion]
    omega
  have coefficient := Nat.mul_le_mul widthBound
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 registerBound) 46)
  have product := Nat.mul_le_mul countBound (show width*(4*registers+46)+6*registers+56 ≤
      initialSize*(4*initialSize+46)+6*initialSize+56 by omega)
  have identity : initialSize*(initialSize*(4*initialSize+46)+6*initialSize+56)+119=
      4*initialSize^3+52*initialSize^2+56*initialSize+119 := by ring
  have finalTime : ticks ≤ 4*initialSize^3+52*initialSize^2+56*initialSize+119 := by rw [← identity]; omega
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  exact ⟨final,ticks,peak,trace,halted,status,finalTime,by change peak ≤ 4*initialSize^3+52*initialSize^2+57*initialSize+119; dsimp [initialSize, input] at *; omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 7182 := by
  simpa [program, InstructionShape.program, InstructionFields.program, OpcodeReader.program,
    OpcodeReader.readMachine, OpcodeReader.seed, OpcodeReader.saveMachine, WordListReader.program,
    WordListReader.payloadProgram, WordListReader.restorePayload, WordListReader.restoreMachine,
    WordListReader.countMachine, WordListReader.loop, WordListReader.body, WordListReader.moveWord,
    ColdInput.readSave, ColdInput.headerMachine, OperandLoop.program, InstructionOperands.program,
    InstructionOperands.body, InstructionOperands.setup, InstructionOperands.payloadMachine, InstructionOperands.countMachine,
    OpcodeRoles.machine, OperandCheck.reader, OperandCheck.program, WidthReader.program, WidthReader.counterMachine,
    RegisterRange.program, RegisterRange.copyMachine, RegisterRange.coreMachine, RegisterRange.publishMachine,
    StackFrames.relocate, StackCopy.program, WordReader.program, WordReader.cursorMachine, WordReader.reverseMachine,
    StackBlocks.reverseProgram, CountLoop.program, GuardedLink.program, link, OpcodeArity.label_card,
    OpcodeRoles.label_card, OperandCheck.Label, RegisterRange.Label, WordBound.Label, WordBound.BodyLabel] using finiteTM_resident program

end Controller.Complexity.InstructionRange
