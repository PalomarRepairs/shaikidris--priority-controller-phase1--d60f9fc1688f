module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordPrefix
public import Controller.Complexity.FieldCommit

@[expose] public section

/-! A finite replacement body consumes a prepared traversal counter and
reconstructs a persistent field with one new word. It preserves the replacement
operand, the original index, globals and unrelated instruction/ambient banks. -/
namespace Controller.Complexity.FieldReplace
open StackMachine StackBlocks WordReader
open scoped BigOperators

def copyPorts : Option Bool ↪ Port := StackFrames.threePorts (some 27) (some 1) (some 2) (by decide) (by decide) (by decide)

theorem copyPorts_apply (port : Option Bool) : copyPorts port=(match port with | none => some 27 | some false => some 1 | some true => some 2) := rfl

def copyReplacement := StackFrames.relocate copyPorts StackCopy.program
def replaceWord := link (link WordSkip.body copyReplacement) WordPrefix.moveWord
def moveRest := transfer (K := Fin 31) (some 0) (some 20)
def program (slot : Fin 5) := link (link (link WordPrefix.program replaceWord) moveRest) (FieldCommit.program slot)

theorem prefix_skip (frame : Port → List Bool) (source buffer : List Bool) :
    WordPrefix.data frame 0 source buffer=WordSkip.data (Function.update frame (some 20) buffer) 0 source := by
  funext address
  simp only [WordPrefix.data_at,WordSkip.data_at,Function.update_apply]
  by_cases hn : address=some 4 <;> by_cases hb : address=some 20 <;> simp_all

theorem copy_execution (frame : Port → List Bool) (source buffer replacement : List Bool)
    (stored : frame (some 27)=replacement) :
    ∃ peak, Execution copyReplacement ⟨some copyReplacement.main,WordPrefix.data frame 0 source buffer⟩
      ⟨none,bank (WordPrefix.fields frame 0 buffer) [] source replacement⟩ (5*replacement.length+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution copyPorts (WordPrefix.data frame 0 source buffer) (by simp [copyPorts_apply,WordPrefix.data_at])
  have output : Function.update (WordPrefix.data frame 0 source buffer) (copyPorts (some false))
      (WordPrefix.data frame 0 source buffer (copyPorts none)++WordPrefix.data frame 0 source buffer (copyPorts (some false)))=
      bank (WordPrefix.fields frame 0 buffer) [] source replacement := by
    funext address
    by_cases same : address=some 1 <;> simp_all [copyPorts_apply,WordPrefix.data,WordPrefix.fields,WordSkip.reader_at]
  rw [output] at trace
  exact ⟨peak,by simpa [copyReplacement,StackFrames.relocate,copyPorts_apply,WordPrefix.data_at,stored] using trace⟩

theorem replace_execution (frame : Port → List Bool) (width : Nat) (oldWord suffix buffer replacement : List Bool)
    (stored : frame (some 8)=List.replicate width true) (oldWidth : oldWord.length=width)
    (replacementStored : frame (some 27)=replacement) (replacementWidth : replacement.length=width) :
    ∃ peak, Execution replaceWord ⟨some replaceWord.main,WordPrefix.data frame 0 (oldWord++suffix) buffer⟩
      ⟨none,WordPrefix.data frame 0 suffix (replacement.reverse++buffer)⟩ (22*width+20) peak := by
  obtain ⟨readPeak,reading⟩ := WordSkip.body_execution (Function.update frame (some 20) buffer) 0 oldWord suffix (by simpa [oldWidth] using stored)
  rw [← prefix_skip,← prefix_skip] at reading
  obtain ⟨copyPeak,copying⟩ := copy_execution frame suffix buffer replacement replacementStored
  obtain ⟨movePeak,moving⟩ := WordPrefix.move_word_execution frame 0 suffix replacement buffer
  have ticks : (15*oldWord.length+14)+(5*replacement.length+4)+(2*replacement.length+2)=22*width+20 := by rw [oldWidth,replacementWidth]; omega
  exact ⟨_,by simpa only [replaceWord,ticks] using (reading.link copying).link moving⟩

theorem rest_execution (frame : Port → List Bool) (source buffer : List Bool) :
    ∃ peak, Execution moveRest ⟨some moveRest.main,WordPrefix.data frame 0 source buffer⟩
      ⟨none,WordPrefix.data frame 0 [] (source.reverse++buffer)⟩ (2*source.length+2) peak := by
  obtain ⟨peak,trace⟩ := InstructionCollect.move_execution (WordPrefix.data frame 0 source buffer) (some 0) (some 20) (by decide)
  have output : Function.update (Function.update (WordPrefix.data frame 0 source buffer) (some 0) []) (some 20)
      ((WordPrefix.data frame 0 source buffer (some 0)).reverse++WordPrefix.data frame 0 source buffer (some 20))=
      WordPrefix.data frame 0 [] (source.reverse++buffer) := by
    funext address
    by_cases hs : address=some 0 <;> by_cases hb : address=some 20 <;> simp_all [WordPrefix.data_at]
  rw [output] at trace
  exact ⟨peak,by simpa [moveRest,transfer,WordPrefix.data_at] using trace⟩

def output (frame : Port → List Bool) (slot : Fin 5) (packet : List Bool) : Port → List Bool :=
  Function.update (WordSelect.output (Function.update frame (some 20) []) [] []) (some (FieldGet.field slot)) packet

theorem commit_output (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (buffer : List Bool) :
    FieldCommit.fields (WordPrefix.data frame 0 [] buffer) slot 0 (Encoding.frameCount count buffer.reverse) []=
      output frame slot (Encoding.frameCount count buffer.reverse) := by
  funext address
  have outside (work : Fin 31) (small : work.val<21) := FieldGet.field_ne slot work small
  by_cases ht : address=some (FieldGet.field slot) <;> by_cases hn : address=some 10 <;> by_cases hb : address=some 20 <;>
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases hk : address=some 2 <;> by_cases hi : address=some 4 <;>
      simp_all [FieldCommit.fields_at,output,WordSelect.output,WordSkip.reader_at,WordPrefix.data_at,
        outside 0 (by decide),outside 1 (by decide),outside 2 (by decide),outside 4 (by decide),outside 10 (by decide),outside 20 (by decide)]

theorem execution (frame : Port → List Bool) (slot : Fin 5) (width count : Nat)
    (left : List (List Bool)) (oldWord replacement : List Bool) (right : List (List Bool))
    (stored : frame (some 8)=List.replicate width true) (countStored : frame (some 10)=List.replicate count true)
    (replacementStored : frame (some 27)=replacement) (widths : ∀ word ∈ left, word.length=width)
    (oldWidth : oldWord.length=width) (replacementWidth : replacement.length=width) :
    ∃ peak, Execution (program slot)
      ⟨some (program slot).main,WordPrefix.data frame left.length (left.flatten++(oldWord++right.flatten)) []⟩
      ⟨none,output frame slot (Encoding.frameCount count (left.flatten++(replacement++right.flatten)))⟩
      (left.length*(16*width+15)+22*width+2*right.flatten.length+
        (frame (some (FieldGet.field slot))).length+2*(left.flatten++(replacement++right.flatten)).length+2*count+32) peak := by
  obtain ⟨prefixPeak,prefixRun⟩ := WordPrefix.execution frame width left (oldWord++right.flatten) [] stored widths
  simp only [List.append_nil] at prefixRun
  obtain ⟨replacePeak,replacing⟩ := replace_execution frame width oldWord right.flatten left.flatten.reverse replacement stored oldWidth replacementStored replacementWidth
  obtain ⟨restPeak,moving⟩ := rest_execution frame right.flatten (replacement.reverse++left.flatten.reverse)
  let buffer := right.flatten.reverse++(replacement.reverse++left.flatten.reverse)
  have reversed : buffer.reverse=left.flatten++(replacement++right.flatten) := by simp [buffer,List.reverse_append,List.append_assoc]
  have length : buffer.length=(left.flatten++(replacement++right.flatten)).length := by rw [← reversed,List.length_reverse]
  obtain ⟨commitPeak,committing⟩ := FieldCommit.ready_execution (WordPrefix.data frame 0 [] buffer) slot count buffer
    (by simpa [WordPrefix.data_at] using countStored) (by simp [WordPrefix.data_at])
  have oldLength : (WordPrefix.data frame 0 [] buffer (some (FieldGet.field slot))).length=(frame (some (FieldGet.field slot))).length := by
    simp [WordPrefix.data_at,FieldGet.field_ne slot 0 (by decide),FieldGet.field_ne slot 1 (by decide),
      FieldGet.field_ne slot 2 (by decide),FieldGet.field_ne slot 4 (by decide),FieldGet.field_ne slot 20 (by decide)]
  rw [oldLength,commit_output,reversed] at committing
  have trace := ((prefixRun.link replacing).link moving).link committing
  have ticks : ((left.length*(16*width+15)+2)+(22*width+20))+(2*right.flatten.length+2)+
      ((frame (some (FieldGet.field slot))).length+2*buffer.length+2*count+8)=
      left.length*(16*width+15)+22*width+2*right.flatten.length+(frame (some (FieldGet.field slot))).length+
        2*(left.flatten++(replacement++right.flatten)).length+2*count+32 := by rw [length]; omega
  exact ⟨_,by simpa only [program,ticks] using trace⟩

end Controller.Complexity.FieldReplace
