module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.InstructionRange
public import Controller.Complexity.InstructionEndpoint

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The finite instruction frontend is related to its prefix decoder on
arbitrary bit strings. Canonical reconstruction retains the unread suffix;
saved header sizes are charged inside the initial physical-bank storage. -/
namespace Controller.Complexity.InstructionFrontend
open StackMachine WordReader

theorem bits_value (digits : List Bool) : Encoding.bits digits.length (Encoding.value digits)=digits := by
  induction digits with
  | nil => rfl
  | cons bit digits ih =>
    cases bit <;> simpa [Encoding.bits, Encoding.value, Nat.add_div, Nat.add_mod, Nat.mul_comm] using ih

theorem word_sound (width : Nat) (digits : List Bool) (word : Controller.Cost.Word width)
    (decoded : Encoding.decodeWord width digits=some word) : Encoding.bits width word.val=digits := by
  unfold Encoding.decodeWord at decoded
  split at decoded
  next same =>
    simp only [Option.some.injEq] at decoded
    have value : word.val=Encoding.value digits := (congrArg Fin.val decoded).symm
    rw [value, ← same]
    exact bits_value digits
  next wrong => simp at decoded

theorem readWords_sound (width count : Nat) (input : List Bool) (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (decoded : Encoding.readWords width count input=some (words,suffix)) :
    words.length=count ∧ input=Encoding.wordList width words++suffix := by
  induction count generalizing input words with
  | zero =>
    simp only [Encoding.readWords, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl,rfl⟩ := decoded
    exact ⟨rfl,rfl⟩
  | succ count ih =>
    cases head : Encoding.decodeWord width (input.take width) with
    | none => simp [Encoding.readWords, head] at decoded
    | some word =>
      cases tail : Encoding.readWords width count (input.drop width) with
      | none => simp [Encoding.readWords, head, tail] at decoded
      | some pair =>
        rcases pair with ⟨rest,remaining⟩
        simp only [Encoding.readWords, head, tail, Bind.bind, Option.bind] at decoded
        obtain ⟨rfl,rfl⟩ := decoded
        obtain ⟨length,body⟩ := ih _ _ tail
        refine ⟨by simp [length],?_⟩
        have headBits := word_sound width (input.take width) word head
        calc
          input = input.take width++input.drop width := (List.take_append_drop width input).symm
          _ = Encoding.bits width word.val++(Encoding.wordList width rest++suffix) := by rw [headBits, body]
          _ = Encoding.wordList width (word :: rest)++suffix := by simp only [Encoding.wordList, List.flatMap_cons, List.append_assoc]; rfl

theorem framed_sound (width : Nat) (input : List Bool) (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (decoded : Encoding.readFramedWords width input=some (words,suffix)) :
    input=Encoding.encodeWords width words++suffix := by
  cases header : Encoding.readCount input with
  | none => simp [Encoding.readFramedWords, header] at decoded
  | some pair =>
    rcases pair with ⟨count,payload⟩
    have parsed : Encoding.readWords width count payload=some (words,suffix) := by
      simpa only [Encoding.readFramedWords, header, Bind.bind, Option.bind] using decoded
    obtain ⟨length,body⟩ := readWords_sound width count payload words suffix parsed
    rw [HeaderParser.readCount_sound header, body, ← length]
    simp only [Encoding.encodeWords, Encoding.frameCount, List.append_assoc, List.cons_append]

def parseSyntax (width : Nat) (input : List Bool) : Option (Fin 16 × List (Controller.Cost.Word width) × List Bool) := do
  let opcode ← Encoding.decodeWord 4 (input.take 4)
  let (words,suffix) ← Encoding.readFramedWords width (input.drop 4)
  return (opcode,words,suffix)

theorem syntax_sound (width : Nat) (input : List Bool) (opcode : Fin 16)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (decoded : parseSyntax width input=some (opcode,words,suffix)) :
    input=Encoding.bits 4 opcode.val++(Encoding.encodeWords width words++suffix) := by
  cases tag : Encoding.decodeWord 4 (input.take 4) with
  | none => simp [parseSyntax, tag] at decoded
  | some value =>
    cases body : Encoding.readFramedWords width (input.drop 4) with
    | none => simp [parseSyntax, tag, body] at decoded
    | some pair =>
      rcases pair with ⟨values,remaining⟩
      simp only [parseSyntax, tag, body, Bind.bind, Option.bind] at decoded
      obtain ⟨rfl,rfl,rfl⟩ := decoded
      have headBits := word_sound 4 (input.take 4) opcode tag
      have payload := framed_sound width (input.drop 4) words suffix body
      calc
        input = input.take 4++input.drop 4 := (List.take_append_drop 4 input).symm
        _ = Encoding.bits 4 opcode.val++(Encoding.encodeWords width words++suffix) := by rw [headBits, payload]

theorem syntax_read (width registers : Nat) (input : List Bool) :
    (InstructionCodec.read width registers input).isSome=
      (parseSyntax width input).any (fun parsed => (InstructionCodec.readFields registers parsed.1.val parsed.2.1).isSome) := by
  cases tag : Encoding.decodeWord 4 (input.take 4) <;>
    cases body : Encoding.readFramedWords width (input.drop 4) <;> simp [parseSyntax, InstructionCodec.read, tag, body]
  next opcode pair => cases pair with | mk words suffix => cases InstructionCodec.readFields registers opcode.val words <;> rfl

theorem syntax_status (frame : Port → List Bool) (width : Nat) (input : List Bool) :
    Option.isNone ((InstructionFields.result frame width input none).head?)=(parseSyntax width input).isSome := by
  by_cases enough : 4 ≤ input.length
  · have length : (input.take 4).length=4 := by simp only [List.length_take, Nat.min_eq_left enough]
    have parsed : Encoding.decodeWord 4 (input.take 4)=some ⟨Encoding.value (input.take 4),by simpa only [length] using Encoding.value_lt (input.take 4)⟩ := by
      simp [Encoding.decodeWord, length]
    have status := WordListTotal.parse_accept (Function.update frame (some 13) (input.take 4).reverse) width (input.drop 4)
    have equality : Option.isNone ((WordListTotal.parseResult (Function.update frame (some 13) (input.take 4).reverse)
        width (input.drop 4) none).head?)=(Encoding.readFramedWords width (input.drop 4)).isSome := Bool.eq_iff_iff.mpr status
    simp only [InstructionFields.result, ite_eq_left enough, parseSyntax, parsed, Bind.bind, Option.bind]
    cases body : Encoding.readFramedWords width (input.drop 4) with
    | none => simpa only [body, Bind.bind, Option.bind, Option.isSome_none] using equality
    | some pair =>
      cases pair
      change _=true
      simpa only [body, Option.isSome_some] using equality
  · have length : (input.take 4).length≠4 := by simp only [List.length_take]; omega
    have rejected := Encoding.decodeWord_wrong_length (input.take 4) length
    simp [InstructionFields.result, enough, OpcodeReader.result, bank_counter, parseSyntax, rejected]

abbrev program := InstructionRange.program

theorem total_resources (frame : Port → List Bool) (width registers : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (boundEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) :
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks peak ∧ final.pc=none ∧
      Option.isNone (final.stk none).head?=(InstructionCodec.read width registers input).isSome ∧
      ticks ≤ 4*(input.length+ambientBits frame)^3+52*(input.length+ambientBits frame)^2+56*(input.length+ambientBits frame)+119 ∧
      peak ≤ 4*(input.length+ambientBits frame)^3+52*(input.length+ambientBits frame)^2+57*(input.length+ambientBits frame)+119 := by
  cases parsed : parseSyntax width input with
  | some fields =>
    rcases fields with ⟨opcode,words,suffix⟩
    have canonical := syntax_sound width input opcode words suffix parsed
    obtain ⟨final,ticks,peak,trace,halted,status,timeBound,spaceBound⟩ := InstructionRange.raw_polynomial frame width registers opcode words suffix
      stored saved countEmpty bufferEmpty savedEmpty tagEmpty boundEmpty scratchEmpty roleEmpty
    rw [← canonical] at trace timeBound spaceBound
    have decoded : (InstructionCodec.read width registers input).isSome=(InstructionCodec.readFields registers opcode.val words).isSome := by
      rw [syntax_read, parsed]; rfl
    exact ⟨final,ticks,peak,trace,halted,status.trans decoded.symm,timeBound,spaceBound⟩
  | none =>
    obtain ⟨ticks,peak,fieldsRun,bound,_⟩ := InstructionFields.total_resources frame width input stored countEmpty bufferEmpty savedEmpty tagEmpty
    have rejected : Option.isNone ((InstructionFields.result frame width input none).head?)=false := by rw [syntax_status, parsed]; rfl
    have shapeRun := GuardedLink.failure OpcodeArity.machine none Option.isNone fieldsRun rejected
    have trace := GuardedLink.failure InstructionOperands.program none Option.isNone shapeRun rejected
    have decoded : (InstructionCodec.read width registers input).isSome=false := by rw [syntax_read, parsed]; rfl
    have widthBound := WordListTotal.stored_width_le_ambient frame width stored
    let size := input.length+ambientBits frame
    have product := Nat.mul_le_mul (show input.length ≤ size by dsimp [size]; omega)
      (show 16*width+30 ≤ 16*size+30 by dsimp [size]; omega)
    have identity : size*(16*size+30)+77=16*size^2+30*size+77 := by ring
    have finalTime : ticks+1+1 ≤ 4*size^3+52*size^2+56*size+119 := by omega
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    exact ⟨_,_,_,trace,rfl,rejected.trans decoded.symm,finalTime,by change peak ≤ 4*size^3+52*size^2+57*size+119; dsimp [size] at *; omega⟩

theorem terminal_unique [Fintype K] [DecidableEq K] {machine : Program K Q}
    {initial leftFinal rightFinal : State K Q} {leftTicks leftPeak rightTicks rightPeak : Nat}
    (left : Execution machine initial leftFinal leftTicks leftPeak)
    (right : Execution machine initial rightFinal rightTicks rightPeak)
    (leftHalted : leftFinal.pc=none) (rightHalted : rightFinal.pc=none) : leftFinal=rightFinal := by
  induction left generalizing rightFinal rightTicks rightPeak with
  | refl state =>
    cases right with
    | refl => rfl
    | cons transition tail => simp [step, leftHalted] at transition
  | cons transition tail ih =>
    cases right with
    | refl => simp [step, rightHalted] at transition
    | cons otherTransition otherTail =>
      have same := Option.some.inj (transition.symm.trans otherTransition)
      cases same
      exact ih otherTail leftHalted rightHalted

theorem fields_observation (frame : Port → List Bool) (opcode : Fin 16)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool) (registers : Nat) :
    InstructionFields.observe width registers (InstructionShape.fieldsData frame opcode words suffix)=
      InstructionCodec.readFields registers opcode.val words := by
  have tagParsed := (Encoding.wordEncoding 4).decode_encode opcode
  have wordsParsed := (Encoding.wordsEncoding width).decode_encode words
  change Encoding.decodeWord 4 (Encoding.bits 4 opcode.val)=some opcode at tagParsed
  change Encoding.decodeWords width (Encoding.encodeWords width words)=some words at wordsParsed
  simp only [InstructionFields.observe]
  simp [InstructionRange.fields_at, List.reverse_reverse]
  rw [tagParsed]
  simp only [Option.bind]
  change (Encoding.decodeWords width (Encoding.encodeWords width words)).bind _=_
  rw [wordsParsed]
  rfl

theorem read_parts (width registers : Nat) (input : List Bool)
    (instruction : Controller.Cost.Instruction width registers) (suffix : List Bool)
    (decoded : InstructionCodec.read width registers input=some (instruction,suffix)) :
    ∃ opcode : Fin 16, ∃ words : List (Controller.Cost.Word width),
      parseSyntax width input=some (opcode,words,suffix) ∧
      InstructionCodec.readFields registers opcode.val words=some instruction := by
  cases tag : Encoding.decodeWord 4 (input.take 4) with
  | none => simp [InstructionCodec.read, tag] at decoded
  | some opcode =>
    cases body : Encoding.readFramedWords width (input.drop 4) with
    | none => simp [InstructionCodec.read, tag, body] at decoded
    | some pair =>
      rcases pair with ⟨words,rest⟩
      cases native : InstructionCodec.readFields registers opcode.val words with
      | none => simp [InstructionCodec.read, tag, body, native] at decoded
      | some value =>
        simp only [InstructionCodec.read, tag, body, native, Bind.bind, Option.bind, Option.pure_def] at decoded
        obtain ⟨rfl,rfl⟩ := decoded
        exact ⟨opcode,words,by simp [parseSyntax, tag, body],native⟩

theorem total_decodes (frame : Port → List Bool) (width registers : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (tagEmpty : frame (some 13)=[]) (boundEmpty : frame (some 16)=[]) (scratchEmpty : frame (some 17)=[])
    (roleEmpty : frame (some 18)=[]) :
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks peak ∧ final.pc=none ∧
      Option.isNone (final.stk none).head?=(InstructionCodec.read width registers input).isSome ∧
      (∀ instruction suffix, InstructionCodec.read width registers input=some (instruction,suffix) →
        InstructionFields.observe width registers final.stk=some instruction ∧ final.stk (some 0)=suffix) ∧
      ticks ≤ 4*(input.length+ambientBits frame)^3+52*(input.length+ambientBits frame)^2+56*(input.length+ambientBits frame)+119 ∧
      peak ≤ 4*(input.length+ambientBits frame)^3+52*(input.length+ambientBits frame)^2+57*(input.length+ambientBits frame)+119 := by
  obtain ⟨final,ticks,peak,trace,halted,status,timeBound,spaceBound⟩ := total_resources frame width registers input
    stored saved countEmpty bufferEmpty savedEmpty tagEmpty boundEmpty scratchEmpty roleEmpty
  refine ⟨final,ticks,peak,trace,halted,status,?_,timeBound,spaceBound⟩
  intro instruction suffix decoded
  obtain ⟨opcode,words,parsed,native⟩ := read_parts width registers input instruction suffix decoded
  have canonical := syntax_sound width input opcode words suffix parsed
  have valid : (InstructionCodec.readFields registers opcode.val words).isSome=true := by rw [native]; rfl
  obtain ⟨otherTicks,otherPeak,other,_,_⟩ := InstructionEndpoint.raw_execution frame width registers opcode words suffix valid
    stored saved countEmpty bufferEmpty savedEmpty tagEmpty boundEmpty scratchEmpty roleEmpty
  rw [← canonical] at other
  have same := terminal_unique trace other halted rfl
  rw [same]
  exact ⟨(fields_observation frame opcode words suffix registers).trans native,by simp [InstructionRange.fields_at]⟩

end Controller.Complexity.InstructionFrontend
