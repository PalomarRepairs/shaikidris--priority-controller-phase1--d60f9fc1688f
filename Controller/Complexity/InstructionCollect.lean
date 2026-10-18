module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.InstructionEndpoint

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Parsed instruction fields are consumed into a reversed program stream.
Two actual transfers preserve the saved tag's order; count, delimiter and
operand payload are then prepended. All frontend field banks are cleared. -/
namespace Controller.Complexity.InstructionCollect
open StackMachine StackBlocks WordReader
open scoped BigOperators

theorem move_execution (input : Port → List Bool) (source destination : Port) (distinct : source ≠ destination) :
    ∃ peak, Execution (transfer source destination) ⟨some 0,input⟩
      ⟨none,Function.update (Function.update input source []) destination ((input source).reverse++input destination)⟩
      (2*(input source).length+2) peak := by
  have trace := transfer_execution input distinct (input source) (input destination)
  have entry : storage input source destination (input source) (input destination)=input := by
    simp only [storage, Function.update_eq_self]
  change Execution (transfer source destination)
    ⟨some 0,storage input source destination (input source) (input destination)⟩
    ⟨none,storage input source destination [] ((input source).reverse++input destination)⟩ _ _ at trace
  rw [entry] at trace
  exact ⟨_,by simpa only [storage] using trace⟩

def pushDelimiter : Program (Fin 31) (Fin 2) where
  main := 0
  code label := if label=0 then .push (some 19) false 1 else .halt

theorem delimiter_execution (input : Port → List Bool) :
    ∃ peak, Execution pushDelimiter ⟨some pushDelimiter.main,input⟩
      ⟨none,Function.update input (some 19) (false :: input (some 19))⟩ 2 peak := by
  have first : step pushDelimiter ⟨some pushDelimiter.main,input⟩=
      some ⟨some 1,Function.update input (some 19) (false :: input (some 19))⟩ := by simp [step, pushDelimiter, instructionStep]
  have last : step pushDelimiter ⟨some 1,Function.update input (some 19) (false :: input (some 19))⟩=
      some ⟨none,Function.update input (some 19) (false :: input (some 19))⟩ := by simp [step, pushDelimiter, instructionStep]
  exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩

def fields (frame : Port → List Bool) (tag count payload buffer temporary : List Bool) : Port → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update frame (some 13) tag)
    (some 12) count) (some 11) payload) (some 19) buffer) (some 20) temporary

theorem fields_at (frame : Port → List Bool) (tag count payload buffer temporary : List Bool) (target : Port) :
    fields frame tag count payload buffer temporary target=
      if target=some 13 then tag else if target=some 12 then count else if target=some 11 then payload
      else if target=some 19 then buffer else if target=some 20 then temporary else frame target := by
  by_cases hg : target=some 13 <;> by_cases hc : target=some 12 <;> by_cases hp : target=some 11 <;>
    by_cases hb : target=some 19 <;> by_cases ht : target=some 20 <;> simp_all [fields]

theorem move_tag_first (frame : Port → List Bool) (tag count payload buffer : List Bool) :
    ∃ peak, Execution (transfer (K := Fin 31) (some 13) (some 20))
      ⟨some 0,fields frame tag count payload buffer []⟩
      ⟨none,fields frame [] count payload buffer tag.reverse⟩ (2*tag.length+2) peak := by
  obtain ⟨peak,trace⟩ := move_execution (fields frame tag count payload buffer []) (some 13) (some 20) (by decide)
  have output : Function.update (Function.update (fields frame tag count payload buffer []) (some 13) [])
      (some 20) ((fields frame tag count payload buffer [] (some 13)).reverse++fields frame tag count payload buffer [] (some 20))=
      fields frame [] count payload buffer tag.reverse := by
    funext target
    by_cases hg : target=some 13 <;> by_cases ht : target=some 20 <;> simp_all [fields_at]
  rw [output] at trace
  exact ⟨_,by simpa [fields_at] using trace⟩

theorem move_tag_second (frame : Port → List Bool) (tag count payload buffer : List Bool) :
    ∃ peak, Execution (transfer (K := Fin 31) (some 20) (some 19))
      ⟨some 0,fields frame [] count payload buffer tag.reverse⟩
      ⟨none,fields frame [] count payload (tag++buffer) []⟩ (2*tag.length+2) peak := by
  obtain ⟨peak,trace⟩ := move_execution (fields frame [] count payload buffer tag.reverse) (some 20) (some 19) (by decide)
  have output : Function.update (Function.update (fields frame [] count payload buffer tag.reverse) (some 20) [])
      (some 19) ((fields frame [] count payload buffer tag.reverse (some 20)).reverse++fields frame [] count payload buffer tag.reverse (some 19))=
      fields frame [] count payload (tag++buffer) [] := by
    funext target
    by_cases ht : target=some 20 <;> by_cases hb : target=some 19 <;> simp_all [fields_at]
  rw [output] at trace
  exact ⟨peak,by simpa [fields_at] using trace⟩

def tagProgram := link (transfer (K := Fin 31) (some 13) (some 20)) (transfer (some 20) (some 19))
def countProgram := transfer (K := Fin 31) (some 12) (some 19)
def payloadProgram := transfer (K := Fin 31) (some 11) (some 19)
def program := link (link (link tagProgram countProgram) pushDelimiter) payloadProgram

theorem count_execution (frame : Port → List Bool) (count : Nat) (payload buffer : List Bool) :
    ∃ peak, Execution countProgram ⟨some countProgram.main,fields frame [] (List.replicate count true) payload buffer []⟩
      ⟨none,fields frame [] [] payload (List.replicate count true++buffer) []⟩ (2*count+2) peak := by
  obtain ⟨peak,trace⟩ := move_execution (fields frame [] (List.replicate count true) payload buffer []) (some 12) (some 19) (by decide)
  have output : Function.update (Function.update (fields frame [] (List.replicate count true) payload buffer []) (some 12) [])
      (some 19) ((fields frame [] (List.replicate count true) payload buffer [] (some 12)).reverse++
        fields frame [] (List.replicate count true) payload buffer [] (some 19))=
      fields frame [] [] payload (List.replicate count true++buffer) [] := by
    funext target
    by_cases hc : target=some 12 <;> by_cases hb : target=some 19 <;> simp_all [fields_at]
  rw [output] at trace
  exact ⟨peak,by simpa [countProgram, transfer, fields_at] using trace⟩

theorem delimiter_fields (frame : Port → List Bool) (payload buffer : List Bool) :
    ∃ peak, Execution pushDelimiter ⟨some pushDelimiter.main,fields frame [] [] payload buffer []⟩
      ⟨none,fields frame [] [] payload (false :: buffer) []⟩ 2 peak := by
  obtain ⟨peak,trace⟩ := delimiter_execution (fields frame [] [] payload buffer [])
  have output : Function.update (fields frame [] [] payload buffer []) (some 19) (false :: fields frame [] [] payload buffer [] (some 19))=
      fields frame [] [] payload (false :: buffer) [] := by
    funext target
    by_cases hb : target=some 19 <;> simp_all [fields_at]
  exact ⟨peak,by simpa only [output] using trace⟩

theorem payload_execution (frame : Port → List Bool) (payload buffer : List Bool) :
    ∃ peak, Execution payloadProgram ⟨some payloadProgram.main,fields frame [] [] payload buffer []⟩
      ⟨none,fields frame [] [] [] (payload.reverse++buffer) []⟩ (2*payload.length+2) peak := by
  obtain ⟨peak,trace⟩ := move_execution (fields frame [] [] payload buffer []) (some 11) (some 19) (by decide)
  have output : Function.update (Function.update (fields frame [] [] payload buffer []) (some 11) [])
      (some 19) ((fields frame [] [] payload buffer [] (some 11)).reverse++fields frame [] [] payload buffer [] (some 19))=
      fields frame [] [] [] (payload.reverse++buffer) [] := by
    funext target
    by_cases hp : target=some 11 <;> by_cases hb : target=some 19 <;> simp_all [fields_at]
  rw [output] at trace
  exact ⟨peak,by simpa [payloadProgram, transfer, fields_at] using trace⟩

theorem execution (frame : Port → List Bool) (opcode : Fin 16) (words : List (Controller.Cost.Word width)) (buffer : List Bool) :
    ∃ peak, Execution program
      ⟨some program.main,fields frame (Encoding.bits 4 opcode.val).reverse (List.replicate words.length true) (Encoding.wordList width words) buffer []⟩
      ⟨none,fields frame [] [] [] ((Encoding.bits 4 opcode.val++Encoding.encodeWords width words).reverse++buffer) []⟩
      (2*(width+1)*words.length+26) peak := by
  obtain ⟨firstPeak,first⟩ := move_tag_first frame (Encoding.bits 4 opcode.val).reverse (List.replicate words.length true) (Encoding.wordList width words) buffer
  obtain ⟨secondPeak,second⟩ := move_tag_second frame (Encoding.bits 4 opcode.val).reverse (List.replicate words.length true) (Encoding.wordList width words) buffer
  obtain ⟨countPeak,counting⟩ := count_execution frame words.length (Encoding.wordList width words) ((Encoding.bits 4 opcode.val).reverse++buffer)
  obtain ⟨delimiterPeak,delimiting⟩ := delimiter_fields frame (Encoding.wordList width words) (List.replicate words.length true++((Encoding.bits 4 opcode.val).reverse++buffer))
  obtain ⟨payloadPeak,payload⟩ := payload_execution frame (Encoding.wordList width words)
    (false :: (List.replicate words.length true++((Encoding.bits 4 opcode.val).reverse++buffer)))
  have trace := (((first.link second).link counting).link delimiting).link payload
  have output : (Encoding.wordList width words).reverse++(false :: (List.replicate words.length true++((Encoding.bits 4 opcode.val).reverse++buffer)))=
      (Encoding.bits 4 opcode.val++Encoding.encodeWords width words).reverse++buffer := by
    simp [Encoding.encodeWords, Encoding.frameCount, List.reverse_append, List.append_assoc]
  have ticks : ((2*((Encoding.bits 4 opcode.val).reverse).length+2)+(2*((Encoding.bits 4 opcode.val).reverse).length+2)+(2*words.length+2))+2+
      (2*(Encoding.wordList width words).length+2)=2*(width+1)*words.length+26 := by simp only [List.length_reverse, Encoding.bits_length, Encoding.wordList_length]; ring
  exact ⟨_,by simpa only [program, tagProgram, countProgram, payloadProgram, output, ticks] using trace⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 162 := by
  simpa [program, tagProgram, countProgram, payloadProgram, pushDelimiter, link] using finiteTM_resident program

theorem fields_self (frame : Port → List Bool) :
    fields frame (frame (some 13)) (frame (some 12)) (frame (some 11)) (frame (some 19)) (frame (some 20))=frame := by
  simp only [fields, Function.update_eq_self]

theorem ready_execution (input : Port → List Bool) (opcode : Fin 16) (words : List (Controller.Cost.Word width))
    (tag : input (some 13)=(Encoding.bits 4 opcode.val).reverse)
    (count : input (some 12)=List.replicate words.length true)
    (payload : input (some 11)=Encoding.wordList width words) (temporary : input (some 20)=[]) :
    ∃ peak, Execution program ⟨some program.main,input⟩
      ⟨none,fields input [] [] [] ((Encoding.bits 4 opcode.val++Encoding.encodeWords width words).reverse++input (some 19)) []⟩
      (2*(width+1)*words.length+26) peak := by
  obtain ⟨peak,trace⟩ := execution input opcode words (input (some 19))
  have entry : fields input (Encoding.bits 4 opcode.val).reverse (List.replicate words.length true)
      (Encoding.wordList width words) (input (some 19)) []=input := by
    simpa only [tag, count, payload, temporary] using fields_self input
  rw [entry] at trace
  exact ⟨peak,trace⟩

end Controller.Complexity.InstructionCollect
