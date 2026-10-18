module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WidthReader
public import Controller.Complexity.CountLoop
public import Controller.Complexity.StackClear

@[expose] public section

/-! A unary-counted scan discards a prefix of fixed-width words. Reads and
erasure are executed by finite programs; the source suffix and all unselected
banks are preserved. The count is word cardinality even when the width is zero. -/
namespace Controller.Complexity.WordSkip
open StackMachine WordReader
open scoped BigOperators

def data (frame : Port → List Bool) (count : Nat) (source : List Bool) : Port → List Bool :=
  bank (Function.update frame (some 4) (List.replicate count true)) [] source []

theorem reader_at (frame : Port → List Bool) (status source word : List Bool) (address : Port) :
    bank frame status source word address=
      if address=none then status else if address=some 0 then source else if address=some 1 then word
      else if address=some 2 then [] else frame address := by
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;> by_cases ht : address=some 2 <;>
    simp_all [bank,StackFrames.embedStorage,cursorPorts_apply,cursorFrame,StackBlocks.layout]

theorem data_at (frame : Port → List Bool) (count : Nat) (source : List Bool) (address : Port) :
    data frame count source address=
      if address=none then [] else if address=some 0 then source else if address=some 1 then []
      else if address=some 2 then [] else if address=some 4 then List.replicate count true else frame address := by
  simp only [data,reader_at,Function.update_apply]

theorem decrement (frame : Port → List Bool) (count : Nat) (source : List Bool) :
    Function.update (data frame (count+1) source) (some 4) (List.replicate count true)=data frame count source := by
  funext address
  by_cases same : address=some 4 <;> simp_all [data_at]

def body := link WidthReader.program (StackClear.program (some 1 : Port))
def program := CountLoop.program body (some 4) none Option.isNone

theorem body_execution (frame : Port → List Bool) (count : Nat) (word suffix : List Bool)
    (stored : frame (some 8)=List.replicate word.length true) :
    ∃ peak, Execution body ⟨some body.main,data frame count (word++suffix)⟩
      ⟨none,data frame count suffix⟩ (15*word.length+14) peak := by
  have reading := WidthReader.execution (Function.update frame (some 4) (List.replicate count true)) word suffix
    (by simpa using stored)
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (bank (Function.update frame (some 4) (List.replicate count true)) [] suffix word) (some 1)
  have output : Function.update (bank (Function.update frame (some 4) (List.replicate count true)) [] suffix word) (some 1) []=data frame count suffix := by
    funext address
    by_cases same : address=some 1 <;> simp_all [data,reader_at]
  rw [output] at clearing
  simp only [bank_word] at clearing
  have trace := reading.link clearing
  have ticks : (14*word.length+12)+(word.length+2)=15*word.length+14 := by omega
  exact ⟨_,by simpa only [body,data,ticks] using trace⟩

theorem execution (frame : Port → List Bool) (width : Nat) (words : List (List Bool)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (widths : ∀ word ∈ words, word.length=width) :
    ∃ peak, Execution program ⟨some program.main,data frame words.length (words.flatten++suffix)⟩
      ⟨none,data frame 0 suffix⟩ (words.length*(15*width+15)+2) peak := by
  induction words with
  | nil =>
    have trace := CountLoop.empty body (some 4) none Option.isNone (data frame 0 suffix) (by simp [data_at])
    exact ⟨_,by simpa only [program,List.length_nil,List.flatten_nil,List.nil_append,Nat.zero_mul,Nat.zero_add] using trace⟩
  | cons word words ih =>
    have wordWidth := widths word (by simp)
    obtain ⟨tailPeak,tail⟩ := ih (by intro item member; exact widths item (by simp [member]))
    obtain ⟨bodyPeak,bodyRun⟩ := body_execution frame words.length word (words.flatten++suffix) (by simpa only [wordWidth] using stored)
    have counted : data frame (words.length+1) (word++(words.flatten++suffix)) (some 4)=true :: List.replicate words.length true := by
      simp [data_at,List.replicate_succ]
    have adjusted : Execution body
        ⟨some body.main,Function.update (data frame (words.length+1) (word++(words.flatten++suffix))) (some 4) (List.replicate words.length true)⟩
        ⟨none,data frame words.length (words.flatten++suffix)⟩ (15*width+14) bodyPeak := by
      simpa only [decrement,wordWidth] using bodyRun
    have accepted : Option.isNone ((data frame words.length (words.flatten++suffix) none).head?)=true := by simp [data_at]
    obtain ⟨peak,trace⟩ := CountLoop.next (some 4) none Option.isNone counted adjusted accepted tail
    have ticks : (15*width+14)+(words.length*(15*width+15)+2)+1=(word :: words).length*(15*width+15)+2 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    exact ⟨peak,by simpa only [program,List.length_cons,List.flatten_cons,List.append_assoc,ticks] using trace⟩

theorem ready_execution (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (suffix : List Bool)
    (stored : input (some 8)=List.replicate width true) (widths : ∀ word ∈ words, word.length=width)
    (source : input (some 0)=words.flatten++suffix) (counter : input (some 4)=List.replicate words.length true)
    (status : input none=[]) (wordWork : input (some 1)=[]) (scratch : input (some 2)=[]) :
    ∃ peak, Execution program ⟨some program.main,input⟩
      ⟨none,Function.update (Function.update input (some 0) suffix) (some 4) []⟩ (words.length*(15*width+15)+2) peak := by
  have entry : data input words.length (words.flatten++suffix)=input := by
    funext address
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> simp_all [data_at]
  have output : data input 0 suffix=Function.update (Function.update input (some 0) suffix) (some 4) [] := by
    funext address
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> simp_all [data_at]
  simpa only [entry,output] using execution input width words suffix stored widths

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 306 := by
  simpa [program,body,WidthReader.program,WidthReader.counterMachine,StackFrames.relocate,StackCopy.program,
    WordReader.program,WordReader.cursorMachine,WordReader.reverseMachine,GuardedLink.program,link,StackBlocks.reverseProgram] using finiteTM_resident program

end Controller.Complexity.WordSkip
