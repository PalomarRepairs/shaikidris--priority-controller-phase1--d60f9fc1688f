module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.DynamicFields

@[expose] public section

/-! An executed first-word pop returns the removed word and shrinks the actual
framed count. Empty fields reject without changing the persistent field. Both
branches clear copied source/count storage and preserve unrelated banks. -/
namespace Controller.Complexity.FieldPop
open StackMachine WordReader
open scoped BigOperators

def data (input : Port → List Bool) (source word buffer : List Bool) := bank (WordPrefix.fields input 0 buffer) [] source word

theorem data_at (input : Port → List Bool) (source word buffer : List Bool) (address : Port) :
    data input source word buffer address=
      if address=none then [] else if address=some 0 then source else if address=some 1 then word
      else if address=some 2 then [] else if address=some 20 then buffer else if address=some 4 then [] else input address := by
  simp only [data,WordPrefix.fields,WordSkip.reader_at,Function.update_apply,List.replicate_zero]

def moveRest := FieldReplace.moveRest

theorem move_execution (input : Port → List Bool) (source word : List Bool) :
    ∃ peak, Execution moveRest ⟨some moveRest.main,data input source word []⟩
      ⟨none,data input [] word source.reverse⟩ (2*source.length+2) peak := by
  obtain ⟨peak,trace⟩ := InstructionCollect.move_execution (data input source word []) (some 0) (some 20) (by decide)
  have output : Function.update (Function.update (data input source word []) (some 0) []) (some 20)
      ((data input source word [] (some 0)).reverse++data input source word [] (some 20))=data input [] word source.reverse := by
    funext address
    by_cases hs : address=some 0 <;> by_cases hb : address=some 20 <;> simp_all [data_at]
  rw [output] at trace
  exact ⟨peak,by simpa [moveRest,FieldReplace.moveRest,StackBlocks.transfer,data_at] using trace⟩

def output (input : Port → List Bool) (slot : Fin 5) (packet word : List Bool) :=
  Function.update (FieldReplace.output input slot packet) (some 1) word

theorem commit_output (input : Port → List Bool) (slot : Fin 5) (count : Nat) (word buffer : List Bool) :
    FieldCommit.fields (data input [] word buffer) slot 0 (Encoding.frameCount count buffer.reverse) []=
      output input slot (Encoding.frameCount count buffer.reverse) word := by
  have equal : FieldCommit.fields (data input [] word buffer) slot 0 (Encoding.frameCount count buffer.reverse) []=
      Function.update (FieldCommit.fields (WordPrefix.data input 0 [] buffer) slot 0 (Encoding.frameCount count buffer.reverse) []) (some 1) word := by
    funext address
    by_cases hw : address=some 1
    · subst address
      simp [FieldCommit.fields_at,data_at,Ne.symm (FieldGet.field_ne slot 1 (by decide))]
    · simp [FieldCommit.fields_at,data_at,WordPrefix.data_at,hw]
  rw [equal,FieldReplace.commit_output]
  rfl

theorem output_count (input : Port → List Bool) (slot : Fin 5) (count packet word : List Bool) :
    output (Function.update input (some 10) count) slot packet word=output input slot packet word :=
by
  unfold output
  rw [FieldPrepare.output_count]

theorem output_frame (input : Port → List Bool) (slot : Fin 5) (words : List (List Bool)) (packet word : List Bool) :
    output (FieldPrepare.frame input words) slot packet word=output input slot packet word :=
by
  unfold output
  rw [FieldPrepare.frame_output]


def body (slot : Fin 5) := link (link WidthReader.program moveRest) (FieldCommit.program slot)
def guarded (slot : Fin 5) := GuardedLink.program UnaryAdjust.decrement (body slot) none Option.isNone
def program (slot : Fin 5) := link (link (FieldPrepare.program slot) (guarded slot)) WordSelect.cleanup

theorem body_execution (input : Port → List Bool) (slot : Fin 5) (count : Nat) (word suffix : List Bool)
    (widthStored : input (some 8)=List.replicate word.length true) (countStored : input (some 10)=List.replicate count true) :
    ∃ peak, Execution (body slot) ⟨some (body slot).main,WordPrefix.data input 0 (word++suffix) []⟩
      ⟨none,output input slot (Encoding.frameCount count suffix) word⟩
      ((input (some (FieldGet.field slot))).length+14*word.length+4*suffix.length+2*count+22) peak := by
  have reading := WidthReader.execution (WordPrefix.fields input 0 []) word suffix (by simpa [WordPrefix.fields] using widthStored)
  obtain ⟨movePeak,moving⟩ := move_execution input suffix word
  obtain ⟨commitPeak,committing⟩ := FieldCommit.ready_execution (data input [] word suffix.reverse) slot count suffix.reverse
    (by simpa [data_at] using countStored) (by simp [data_at])
  rw [commit_output,List.reverse_reverse] at committing
  have oldLength : (data input [] word suffix.reverse (some (FieldGet.field slot))).length=(input (some (FieldGet.field slot))).length := by
    simp [data_at,FieldGet.field_ne slot 0 (by decide),FieldGet.field_ne slot 1 (by decide),FieldGet.field_ne slot 2 (by decide),
      FieldGet.field_ne slot 4 (by decide),FieldGet.field_ne slot 20 (by decide)]
  rw [oldLength,List.length_reverse] at committing
  have trace := (reading.link moving).link committing
  have ticks : (14*word.length+12)+(2*suffix.length+2)+((input (some (FieldGet.field slot))).length+2*suffix.length+2*count+8)=
      (input (some (FieldGet.field slot))).length+14*word.length+4*suffix.length+2*count+22 := by omega
  exact ⟨_,by simpa only [body,data,WordPrefix.data,ticks] using trace⟩

theorem clean_output (input : Port → List Bool) (slot : Fin 5) (packet word : List Bool) :
    Function.update (Function.update (output input slot packet word) (some 0) []) (some 10) []=output input slot packet word := by
  funext address
  by_cases hs : address=some 0 <;> by_cases hn : address=some 10 <;>
    simp_all [output,FieldReplace.output,WordSelect.output,WordSkip.reader_at,
      Ne.symm (FieldGet.field_ne slot 0 (by decide)),Ne.symm (FieldGet.field_ne slot 10 (by decide))]

def result (slot : Fin 5) (input : Port → List Bool) : List (List Bool) → Port → List Bool
  | [] => WordSelect.output input [false] []
  | word :: rest => output input slot (Encoding.frameCount rest.length rest.flatten) word

theorem execution (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool))
    (ready : FieldPrepare.Ready slot input width words) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩ ⟨none,result slot input words⟩ ticks peak ∧
      ticks ≤ 6*(Encoding.frameCount words.length words.flatten).length+6*words.length+14*width+4*words.flatten.length+34 := by
  obtain ⟨preparePeak,preparing⟩ := FieldPrepare.execution slot input width words ready
  rw [FieldPrepare.prefix_ready slot input width words ready] at preparing
  cases words with
  | nil =>
    obtain ⟨dropPeak,dropping⟩ := UnaryAdjust.decrement_empty (WordPrefix.data (FieldPrepare.frame input []) 0 [] []) (by simp [WordPrefix.data_at,FieldSet.frame])
    have rejected : Function.update (WordPrefix.data (FieldPrepare.frame input []) 0 [] []) none
        (false :: WordPrefix.data (FieldPrepare.frame input []) 0 [] [] none)=bank (Function.update (FieldPrepare.frame input []) (some 4) []) [false] [] [] := by
      funext address
      by_cases hc : address=none <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 20 <;>
        simp_all [WordPrefix.data_at,WordSkip.reader_at,FieldSet.frame,ready.clear (some 20) (by simp [FieldSet.work])]
    rw [rejected] at dropping
    have failed := GuardedLink.failure (body slot) none Option.isNone dropping (by simp [bank_counter])
    obtain ⟨clearPeak,clearing⟩ := WordSelect.cleanup_execution (bank (Function.update (FieldPrepare.frame input []) (some 4) []) [false] [] [])
    rw [WordSelect.clean_output,FieldPrepare.saved_output] at clearing
    simp only [WordSkip.reader_at] at clearing
    simp [FieldSet.frame] at clearing
    have trace := (preparing.link failed).link clearing
    refine ⟨21,max (max preparePeak dropPeak) clearPeak,?_,?_⟩
    · simpa [program,guarded,result,Encoding.frameCount,WordPrefix.data] using trace
    · simp [Encoding.frameCount]
  | cons word rest =>
    have wordWidth := ready.widths word (by simp)
    obtain ⟨dropPeak,dropping⟩ := UnaryAdjust.decrement_success
      (WordPrefix.data (FieldPrepare.frame input (word :: rest)) 0 (word++rest.flatten) []) rest.length
      (by simp [WordPrefix.data_at,FieldSet.frame,List.replicate_succ])
    rw [FieldPrepare.count_update] at dropping
    let changed := Function.update (FieldPrepare.frame input (word :: rest)) (some 10) (List.replicate rest.length true)
    obtain ⟨bodyPeak,working⟩ := body_execution changed slot rest.length word rest.flatten
      (by simpa [changed,FieldSet.frame,wordWidth] using ready.widthStored) (by simp [changed])
    rw [output_count,output_frame] at working
    have oldLength : (changed (some (FieldGet.field slot))).length=(Encoding.frameCount (word :: rest).length (word :: rest).flatten).length := by
      simp [changed,FieldSet.frame,FieldGet.field_ne slot 10 (by decide),ready.packet]
    rw [oldLength,wordWidth] at working
    have joined := GuardedLink.success none Option.isNone dropping working (by simp [WordPrefix.data_at])
    obtain ⟨clearPeak,clearing⟩ := WordSelect.cleanup_execution (output input slot (Encoding.frameCount rest.length rest.flatten) word)
    rw [clean_output] at clearing
    have sourceEmpty : output input slot (Encoding.frameCount rest.length rest.flatten) word (some 0)=[] := by
      simp [output,FieldReplace.output,WordSelect.output,bank_source,Ne.symm (FieldGet.field_ne slot 0 (by decide))]
    have countEmpty : output input slot (Encoding.frameCount rest.length rest.flatten) word (some 10)=[] := by
      simp [output,FieldReplace.output,WordSelect.output,WordSkip.reader_at,Ne.symm (FieldGet.field_ne slot 10 (by decide))]
    simp only [sourceEmpty,countEmpty,List.length_nil,Nat.zero_add] at clearing
    simp only [List.length_cons,List.flatten_cons] at preparing
    have trace := (preparing.link joined).link clearing
    refine ⟨_,_,trace,?_⟩
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    omega

theorem total_resources (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool))
    (ready : FieldPrepare.Ready slot input width words) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩ ⟨none,result slot input words⟩ ticks peak ∧
      ticks ≤ 30*FieldGrowth.size input+34 ∧ peak ≤ 31*FieldGrowth.size input+34 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution slot input width words ready
  have cell (port : Port) : (input port).length ≤ FieldGrowth.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have packetBound : (Encoding.frameCount words.length words.flatten).length ≤ FieldGrowth.size input := by simpa only [ready.packet] using cell (some (FieldGet.field slot))
  have wBound : width ≤ FieldGrowth.size input := by simpa only [ready.widthStored,List.length_replicate] using cell (some 8)
  have packetLength : (Encoding.frameCount words.length words.flatten).length=words.length+1+words.flatten.length := by
    simp only [Encoding.frameCount,List.length_append,List.length_replicate,List.length_cons]; omega
  have bounded : ticks ≤ 30*FieldGrowth.size input+34 := by omega
  have space := trace.peak_le
  change peak ≤ FieldGrowth.size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident (slot : Fin 5) : (∑ label, statementSize (tmStatement ((program slot).code label))) ≤ 648 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (program slot)

end Controller.Complexity.FieldPop
