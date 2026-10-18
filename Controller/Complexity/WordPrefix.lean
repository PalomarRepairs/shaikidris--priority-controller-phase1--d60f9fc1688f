module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordSkip
public import Controller.Complexity.InstructionCollect

@[expose] public section

/-! A counted fixed-width prefix scan saves consumed payload bits in reverse
order for reconstruction. The original list count and instruction fields are
preserved; the traversal counter and per-word scratch are consumed. -/
namespace Controller.Complexity.WordPrefix
open StackMachine StackBlocks WordReader
open scoped BigOperators

def fields (frame : Port → List Bool) (count : Nat) (buffer : List Bool) : Port → List Bool :=
  Function.update (Function.update frame (some 4) (List.replicate count true)) (some 20) buffer

def data (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) : Port → List Bool :=
  bank (fields frame count buffer) [] source []

theorem data_at (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) (address : Port) :
    data frame count source buffer address=
      if address=none then [] else if address=some 0 then source else if address=some 1 then []
      else if address=some 2 then [] else if address=some 20 then buffer
      else if address=some 4 then List.replicate count true else frame address := by
  simp only [data,fields,WordSkip.reader_at,Function.update_apply]

theorem decrement (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) :
    Function.update (data frame (count+1) source buffer) (some 4) (List.replicate count true)=data frame count source buffer := by
  funext address
  by_cases same : address=some 4 <;> simp_all [data_at]

def moveWord := transfer (K := Fin 31) (some 1) (some 20)
def body := link WidthReader.program moveWord
def program := CountLoop.program body (some 4) none Option.isNone

theorem move_word_execution (frame : Port → List Bool) (count : Nat) (source word buffer : List Bool) :
    ∃ peak, Execution moveWord ⟨some moveWord.main,bank (fields frame count buffer) [] source word⟩
      ⟨none,data frame count source (word.reverse++buffer)⟩ (2*word.length+2) peak := by
  obtain ⟨peak,trace⟩ := InstructionCollect.move_execution (bank (fields frame count buffer) [] source word) (some 1) (some 20) (by decide)
  have output : Function.update (Function.update (bank (fields frame count buffer) [] source word) (some 1) []) (some 20)
      ((bank (fields frame count buffer) [] source word (some 1)).reverse++bank (fields frame count buffer) [] source word (some 20))=
      data frame count source (word.reverse++buffer) := by
    funext address
    by_cases hw : address=some 1 <;> by_cases hb : address=some 20 <;>
      simp_all [data,fields,WordSkip.reader_at]
  rw [output] at trace
  exact ⟨peak,by simpa [moveWord,transfer,bank_word] using trace⟩

theorem body_execution (frame : Port → List Bool) (count : Nat) (word suffix buffer : List Bool)
    (stored : frame (some 8)=List.replicate word.length true) :
    ∃ peak, Execution body ⟨some body.main,data frame count (word++suffix) buffer⟩
      ⟨none,data frame count suffix (word.reverse++buffer)⟩ (16*word.length+14) peak := by
  have reading := WidthReader.execution (fields frame count buffer) word suffix (by simpa [fields] using stored)
  obtain ⟨movePeak,moving⟩ := move_word_execution frame count suffix word buffer
  have ticks : (14*word.length+12)+(2*word.length+2)=16*word.length+14 := by omega
  exact ⟨_,by simpa only [body,data,ticks] using reading.link moving⟩

theorem execution (frame : Port → List Bool) (width : Nat) (words : List (List Bool)) (suffix buffer : List Bool)
    (stored : frame (some 8)=List.replicate width true) (widths : ∀ word ∈ words, word.length=width) :
    ∃ peak, Execution program ⟨some program.main,data frame words.length (words.flatten++suffix) buffer⟩
      ⟨none,data frame 0 suffix (words.flatten.reverse++buffer)⟩ (words.length*(16*width+15)+2) peak := by
  induction words generalizing buffer with
  | nil =>
    have trace := CountLoop.empty body (some 4) none Option.isNone (data frame 0 suffix buffer) (by simp [data_at])
    exact ⟨_,by simpa only [program,List.length_nil,List.flatten_nil,List.nil_append,List.reverse_nil,Nat.zero_mul,Nat.zero_add] using trace⟩
  | cons word words ih =>
    have wordWidth := widths word (by simp)
    obtain ⟨tailPeak,tail⟩ := ih (word.reverse++buffer) (by intro item member; exact widths item (by simp [member]))
    obtain ⟨bodyPeak,bodyRun⟩ := body_execution frame words.length word (words.flatten++suffix) buffer (by simpa only [wordWidth] using stored)
    have counted : data frame (words.length+1) (word++(words.flatten++suffix)) buffer (some 4)=true :: List.replicate words.length true := by
      simp [data_at,List.replicate_succ]
    have adjusted : Execution body
        ⟨some body.main,Function.update (data frame (words.length+1) (word++(words.flatten++suffix)) buffer) (some 4) (List.replicate words.length true)⟩
        ⟨none,data frame words.length (words.flatten++suffix) (word.reverse++buffer)⟩ (16*width+14) bodyPeak := by
      simpa only [decrement,wordWidth] using bodyRun
    have accepted : Option.isNone ((data frame words.length (words.flatten++suffix) (word.reverse++buffer) none).head?)=true := by simp [data_at]
    obtain ⟨peak,trace⟩ := CountLoop.next (some 4) none Option.isNone counted adjusted accepted tail
    have ticks : (16*width+14)+(words.length*(16*width+15)+2)+1=(word :: words).length*(16*width+15)+2 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    exact ⟨peak,by simpa only [program,List.length_cons,List.flatten_cons,List.append_assoc,List.reverse_append,ticks] using trace⟩

theorem ready_execution (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (suffix buffer : List Bool)
    (stored : input (some 8)=List.replicate width true) (widths : ∀ word ∈ words, word.length=width)
    (source : input (some 0)=words.flatten++suffix) (counter : input (some 4)=List.replicate words.length true)
    (saved : input (some 20)=buffer) (status : input none=[]) (wordWork : input (some 1)=[]) (scratch : input (some 2)=[]) :
    ∃ peak, Execution program ⟨some program.main,input⟩
      ⟨none,Function.update (Function.update (Function.update input (some 0) suffix) (some 4) []) (some 20) (words.flatten.reverse++buffer)⟩
      (words.length*(16*width+15)+2) peak := by
  have entry : data input words.length (words.flatten++suffix) buffer=input := by
    funext address
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 20 <;> simp_all [data_at]
  have output : data input 0 suffix (words.flatten.reverse++buffer)=
      Function.update (Function.update (Function.update input (some 0) suffix) (some 4) []) (some 20) (words.flatten.reverse++buffer) := by
    funext address
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 20 <;> simp_all [data_at]
  simpa only [entry,output] using execution input width words suffix buffer stored widths

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 324 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.WordPrefix
