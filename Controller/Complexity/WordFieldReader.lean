module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordFieldStore
public import Controller.Complexity.WordListTotal
public import Controller.Complexity.InstructionFrontend

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A count-framed state field is parsed and moved to a persistent bank.
The five state-field banks have indices 21 through 25. Existing global and
program banks are retained, and the parser workspace is cleared on success. -/
namespace Controller.Complexity.WordFieldReader
open StackMachine WordReader
open scoped BigOperators

def program (slot : Fin 31) :=
  GuardedLink.program WordListReader.program (WordFieldStore.program (some slot)) none Option.isNone

def packet (frame : Port → List Bool) (slot : Fin 31) (width : Nat)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool) : Port → List Bool :=
  bank (Function.update frame (some slot) (Encoding.encodeWords width words)) [] suffix []

theorem packet_at (frame : Port → List Bool) (slot : Fin 31) (high : 21 ≤ slot.val) (width : Nat)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool) (address : Port) :
    packet frame slot width words suffix address=
      if address=none then [] else if address=some 0 then suffix else if address=some 1 then []
      else if address=some 2 then [] else if address=some slot then Encoding.encodeWords width words else frame address := by
  have h₀ : slot ≠ 0 := by intro same; simp [same] at high
  have h₁ : slot ≠ 1 := by intro same; simp [same] at high
  have h₂ : slot ≠ 2 := by intro same; simp [same] at high
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hd : address=some slot <;>
    simp_all [packet,bank,cursorFrame,cursorPorts_apply,StackFrames.embedStorage,StackBlocks.layout]


theorem stored_packet (frame : Port → List Bool) (slot : Fin 31) (high : 21 ≤ slot.val)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (countEmpty : frame (some 10)=[]) (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (temporaryEmpty : frame (some 20)=[]) (targetEmpty : frame (some slot)=[]) :
    let middle := WordListReader.data (Function.update frame (some 12) (List.replicate words.length true)) 0 suffix (Encoding.wordList width words)
    WordFieldStore.fields middle (some slot) [] [] (Encoding.encodeWords width words++middle (some slot)) []=
      packet frame slot width words suffix := by
  have h0 : slot ≠ 0 := by intro same; simp [same] at high
  have h1 : slot ≠ 1 := by intro same; simp [same] at high
  have h2 : slot ≠ 2 := by intro same; simp [same] at high
  have h10 : slot ≠ 10 := by intro same; simp [same] at high
  have h11 : slot ≠ 11 := by intro same; simp [same] at high
  have h12 : slot ≠ 12 := by intro same; simp [same] at high
  have h20 : slot ≠ 20 := by intro same; simp [same] at high
  dsimp only
  funext address
  by_cases k0 : address=none
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high]
  by_cases k1 : address=some 0
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high,Ne.symm h0]
  by_cases k2 : address=some 1
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high,Ne.symm h1]
  by_cases k3 : address=some 2
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high,Ne.symm h2]
  by_cases k4 : address=some 10
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high]
  by_cases k5 : address=some 11
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high]
  by_cases k6 : address=some 12
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high]
  by_cases k7 : address=some 20
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high,Ne.symm h20]
  by_cases k8 : address=some slot
  · simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high]
  simp_all [WordFieldStore.fields_at,WordListReader.data_at,packet_at frame slot high]

theorem execution (frame : Port → List Bool) (slot : Fin 31) (high : 21 ≤ slot.val)
    (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (temporaryEmpty : frame (some 20)=[]) (targetEmpty : frame (some slot)=[]) :
    ∃ peak, Execution (program slot) ⟨some (program slot).main,bank frame [] (Encoding.encodeWords width words++suffix) []⟩
      ⟨none,packet frame slot width words suffix⟩ (words.length*(26*width+28)+26) peak := by
  have h₁₁ : slot ≠ 11 := by intro same; simp [same] at high
  have h₁₂ : slot ≠ 12 := by intro same; simp [same] at high
  have h₂₀ : slot ≠ 20 := by intro same; simp [same] at high
  let middle := WordListReader.data (Function.update frame (some 12) (List.replicate words.length true)) 0 suffix (Encoding.wordList width words)
  obtain ⟨parsePeak,parsing⟩ := WordListReader.execution frame words suffix stored countEmpty bufferEmpty savedEmpty
  obtain ⟨storePeak,storing⟩ := WordFieldStore.ready_execution middle (some slot) words
    (by simpa using h₁₂) (by simpa using h₁₁) (by simpa using h₂₀)
    (by simp [middle,WordListReader.data_at]) (by simp [middle,WordListReader.data_at])
    (by simp [middle,WordListReader.data_at,temporaryEmpty])
  have output := stored_packet frame slot high words suffix countEmpty bufferEmpty savedEmpty temporaryEmpty targetEmpty
  rw [output] at storing
  have trace := GuardedLink.success none Option.isNone parsing storing (by simp [WordListReader.data_at])
  have ticks : words.length*(22*width+24)+16+(4*(width+1)*words.length+10)=words.length*(26*width+28)+26 := by ring
  exact ⟨_,by simpa only [program,ticks] using trace⟩

def result (frame : Port → List Bool) (slot : Fin 31) (width : Nat) (input : List Bool) : Port → List Bool :=
  match Encoding.readFramedWords width input with
  | none => WordListTotal.parseResult frame width input
  | some (words,suffix) => packet frame slot width words suffix

theorem total_execution (frame : Port → List Bool) (slot : Fin 31) (high : 21 ≤ slot.val) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[])
    (temporaryEmpty : frame (some 20)=[]) (targetEmpty : frame (some slot)=[]) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,bank frame [] input []⟩
      ⟨none,result frame slot width input⟩ ticks peak ∧
      ticks ≤ 16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+26 ∧
      peak ≤ 16*(input.length+ambientBits frame)^2+31*(input.length+ambientBits frame)+26 ∧
      Option.isNone ((result frame slot width input none).head?)=(Encoding.readFramedWords width input).isSome := by
  cases decoded : Encoding.readFramedWords width input with
  | none =>
    obtain ⟨ticks,peak,parsing,timeBound,spaceBound⟩ := WordListTotal.total_polynomial frame width input stored countEmpty bufferEmpty savedEmpty
    have rejected : Option.isNone ((WordListTotal.parseResult frame width input none).head?)=false := by
      have accepted := WordListTotal.parse_accept frame width input
      cases flag : Option.isNone ((WordListTotal.parseResult frame width input none).head?) <;> simp_all
    have trace := GuardedLink.failure (WordFieldStore.program (some slot)) none Option.isNone parsing rejected
    refine ⟨ticks+1,peak,?_,by omega,by omega,?_⟩
    · simpa only [program,result,decoded] using trace
    · simpa only [result,decoded,Option.isSome_none] using rejected
  | some pair =>
    rcases pair with ⟨words,suffix⟩
    have shape := InstructionFrontend.framed_sound width input words suffix decoded
    obtain ⟨peak,trace⟩ := execution frame slot high words suffix stored countEmpty bufferEmpty savedEmpty temporaryEmpty targetEmpty
    rw [← shape] at trace
    have length : input.length=(width+1)*words.length+1+suffix.length := by
      rw [shape,List.length_append,Encoding.encodeWords_length]
    have linear : words.length*(26*width+28)+26 ≤ 28*input.length+26 := by
      have identity : words.length*(26*width+28)=26*((width+1)*words.length)+2*words.length := by ring
      have countBound : words.length ≤ (width+1)*words.length := by
        calc
          _ = 1*words.length := (Nat.one_mul _).symm
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      omega
    have timeBound : words.length*(26*width+28)+26 ≤
        16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+26 := by omega
    have space := trace.peak_le
    simp only [bank_live,List.length_nil,Nat.zero_add,Nat.add_zero] at space
    refine ⟨_,peak,?_,timeBound,by omega,?_⟩
    · simpa only [result,decoded] using trace
    · simp [result,decoded,packet_at frame slot high]

theorem ready_bank (input : Port → List Bool) (status : input none=[]) (word : input (some 1)=[]) (scratch : input (some 2)=[]) :
    bank input [] (input (some 0)) []=input := by
  funext address
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;> by_cases ht : address=some 2 <;>
    simp_all [bank,cursorFrame,cursorPorts_apply,StackFrames.embedStorage,StackBlocks.layout]

theorem ready_total_execution (input : Port → List Bool) (slot : Fin 31) (high : 21 ≤ slot.val) (width : Nat)
    (status : input none=[]) (word : input (some 1)=[]) (scratch : input (some 2)=[])
    (stored : input (some 8)=List.replicate width true) (countEmpty : input (some 10)=[])
    (bufferEmpty : input (some 11)=[]) (savedEmpty : input (some 12)=[])
    (temporaryEmpty : input (some 20)=[]) (targetEmpty : input (some slot)=[]) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩
      ⟨none,result input slot width (input (some 0))⟩ ticks peak ∧
      ticks ≤ 16*(∑ port : Port,(input port).length)^2+30*(∑ port : Port,(input port).length)+26 ∧
      peak ≤ 16*(∑ port : Port,(input port).length)^2+31*(∑ port : Port,(input port).length)+26 ∧
      Option.isNone ((result input slot width (input (some 0)) none).head?)=
        (Encoding.readFramedWords width (input (some 0))).isSome := by
  have entry := ready_bank input status word scratch
  obtain ⟨ticks,peak,trace,timeBound,spaceBound,accepted⟩ :=
    total_execution input slot high width (input (some 0)) stored countEmpty bufferEmpty savedEmpty temporaryEmpty targetEmpty
  rw [entry] at trace
  have mass := bank_live input (none : Option Unit) [] (input (some 0)) []
  rw [entry] at mass
  simp only [live,List.length_nil,Nat.zero_add,Nat.add_zero] at mass
  rw [← mass] at timeBound spaceBound
  exact ⟨ticks,peak,trace,timeBound,spaceBound,accepted⟩

theorem resident (slot : Fin 31) : (∑ label, statementSize (tmStatement ((program slot).code label))) ≤ 765 := by
  simpa [program,WordListReader.program,WordListReader.payloadProgram,WordListReader.restorePayload,
    WordListReader.loop,WordListReader.body,WordListReader.moveWord,WordListReader.restoreMachine,WordListReader.countMachine,
    WordFieldStore.program,WordFieldStore.first,WordFieldStore.third,WordFieldStore.last,WordFieldStore.delimiter,
    ColdInput.readSave,ColdInput.headerMachine,CountLoop.program,GuardedLink.program,StackFrames.relocate,
    WidthReader.program,WidthReader.counterMachine,StackCopy.program,WordReader.program,
    WordReader.cursorMachine,WordReader.reverseMachine,StackBlocks.transfer,StackBlocks.reverseProgram,link] using finiteTM_resident (program slot)

end Controller.Complexity.WordFieldReader
