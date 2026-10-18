module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.DynamicFields

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Executed last-word removal from the persistent heap. The actual count is
checked and decremented; a preserved traversal count retains exactly the prefix.
An empty heap rejects with the original field and all copied work cleared. -/
namespace Controller.Complexity.HeapRelease
open StackMachine WordReader
open scoped BigOperators

def body := link (link (link UnaryAdjust.copyCounter WordPrefix.program) WordSkip.body) (FieldCommit.program (1 : Fin 5))
def guarded := GuardedLink.program UnaryAdjust.decrement body none Option.isNone
def program := link (link (FieldPrepare.program (1 : Fin 5)) guarded) WordSelect.cleanup

theorem traverse_update (input : Port → List Bool) (count : Nat) (source buffer : List Bool) :
    Function.update (WordPrefix.data input 0 source buffer) (some 4) (List.replicate count true)=WordPrefix.data input count source buffer := by
  funext address
  by_cases same : address=some 4 <;> simp_all [WordPrefix.data_at]

theorem body_execution (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (last : List Bool)
    (stored : input (some 8)=List.replicate width true) (countStored : input (some 10)=List.replicate words.length true)
    (widths : ∀ word ∈ words, word.length=width) (lastWidth : last.length=width) :
    ∃ peak, Execution body ⟨some body.main,WordPrefix.data input 0 (words.flatten++last) []⟩
      ⟨none,FieldReplace.output input 1 (Encoding.frameCount words.length words.flatten)⟩
      ((input (some (FieldGet.field 1))).length+words.length*(16*width+22)+15*width+2*words.flatten.length+28) peak := by
  obtain ⟨copyPeak,copying⟩ := UnaryAdjust.copy_execution (WordPrefix.data input 0 (words.flatten++last) []) words.length
    (by simpa [WordPrefix.data_at] using countStored) (by simp [WordPrefix.data_at]) (by simp [WordPrefix.data_at])
  rw [traverse_update] at copying
  obtain ⟨prefixPeak,prefixRun⟩ := WordPrefix.execution input width words last [] stored widths
  simp only [List.append_nil] at prefixRun
  obtain ⟨discardPeak,discarding⟩ := WordSkip.body_execution (Function.update input (some 20) words.flatten.reverse) 0 last []
    (by simpa [lastWidth] using stored)
  rw [← FieldReplace.prefix_skip,← FieldReplace.prefix_skip] at discarding
  simp only [List.append_nil] at discarding
  obtain ⟨commitPeak,committing⟩ := FieldCommit.ready_execution (WordPrefix.data input 0 [] words.flatten.reverse) 1 words.length words.flatten.reverse
    (by simpa [WordPrefix.data_at] using countStored) (by simp [WordPrefix.data_at])
  rw [FieldReplace.commit_output,List.reverse_reverse] at committing
  have oldLength : (WordPrefix.data input 0 [] words.flatten.reverse (some (FieldGet.field 1))).length=(input (some (FieldGet.field 1))).length := by
    simp [WordPrefix.data_at,FieldGet.field_ne 1 0 (by decide),FieldGet.field_ne 1 1 (by decide),FieldGet.field_ne 1 2 (by decide),FieldGet.field_ne 1 4 (by decide),FieldGet.field_ne 1 20 (by decide)]
  rw [oldLength,List.length_reverse] at committing
  have trace := ((copying.link prefixRun).link discarding).link committing
  have ticks : ((5*words.length+4)+(words.length*(16*width+15)+2))+(15*last.length+14)+
      ((input (some (FieldGet.field 1))).length+2*words.flatten.length+2*words.length+8)=
      (input (some (FieldGet.field 1))).length+words.length*(16*width+22)+15*width+2*words.flatten.length+28 := by rw [lastWidth]; ring
  exact ⟨_,by simpa only [body,ticks] using trace⟩

def result (input : Port → List Bool) (words : List (List Bool)) : Port → List Bool :=
  if words=[] then WordSelect.output input [false] [] else FieldReplace.output input 1 (Encoding.frameCount words.dropLast.length words.dropLast.flatten)

theorem execution (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (ready : FieldPrepare.Ready 1 input width words) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,result input words⟩ ticks peak ∧
      ticks ≤ 6*(Encoding.frameCount words.length words.flatten).length+words.length*(16*width+26)+15*width+2*words.flatten.length+50 := by
  obtain ⟨preparePeak,preparing⟩ := FieldPrepare.execution 1 input width words ready
  rw [FieldPrepare.prefix_ready 1 input width words ready] at preparing
  cases words with
  | nil =>
    obtain ⟨dropPeak,dropping⟩ := UnaryAdjust.decrement_empty (WordPrefix.data (FieldPrepare.frame input []) 0 [] []) (by simp [WordPrefix.data_at,FieldSet.frame])
    have rejected : Function.update (WordPrefix.data (FieldPrepare.frame input []) 0 [] []) none
        (false :: WordPrefix.data (FieldPrepare.frame input []) 0 [] [] none)=bank (Function.update (FieldPrepare.frame input []) (some 4) []) [false] [] [] := by
      funext address
      by_cases hc : address=none <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 20 <;>
        simp_all [WordPrefix.data_at,WordSkip.reader_at,FieldSet.frame,ready.clear (some 20) (by simp [FieldSet.work])]
    rw [rejected] at dropping
    have failed := GuardedLink.failure body none Option.isNone dropping (by simp [bank_counter])
    obtain ⟨clearPeak,clearing⟩ := WordSelect.cleanup_execution (bank (Function.update (FieldPrepare.frame input []) (some 4) []) [false] [] [])
    rw [WordSelect.clean_output,FieldPrepare.saved_output] at clearing
    simp only [WordSkip.reader_at] at clearing
    simp [FieldSet.frame] at clearing
    have trace := (preparing.link failed).link clearing
    refine ⟨21,max (max preparePeak dropPeak) clearPeak,?_,?_⟩
    · simpa [program,guarded,result,Encoding.frameCount,WordPrefix.data] using trace
    · simp [Encoding.frameCount]
  | cons word rest =>
    let words := word :: rest
    let prior := words.dropLast
    let last := words.getLast (by simp [words])
    have split : prior++[last]=words := List.dropLast_concat_getLast (by simp [words])
    have priorLength : prior.length=rest.length := by simp [prior,words]
    have source : words.flatten=prior.flatten++last := by rw [← split,List.flatten_append]; simp
    have widths : ∀ item ∈ prior, item.length=width := by
      intro item member
      exact ready.widths item ((List.dropLast_sublist words).subset member)
    have lastWidth : last.length=width := ready.widths last (List.getLast_mem (by simp))
    obtain ⟨dropPeak,dropping⟩ := UnaryAdjust.decrement_success (WordPrefix.data (FieldPrepare.frame input words) 0 words.flatten []) rest.length
      (by simp [WordPrefix.data_at,FieldSet.frame,words,List.replicate_succ])
    rw [← priorLength,FieldPrepare.count_update] at dropping
    let changed := Function.update (FieldPrepare.frame input words) (some 10) (List.replicate prior.length true)
    obtain ⟨bodyPeak,working⟩ := body_execution changed width prior last
      (by simpa [changed,FieldSet.frame] using ready.widthStored) (by simp [changed]) widths lastWidth
    rw [← source,FieldPrepare.output_count,FieldPrepare.frame_output] at working
    have oldLength : (changed (some (FieldGet.field 1))).length=(Encoding.frameCount words.length words.flatten).length := by
      simp [changed,words,FieldSet.frame,FieldGet.field_ne 1 10 (by decide),ready.packet]
    rw [oldLength] at working
    have joined := GuardedLink.success none Option.isNone dropping working (by simp [WordPrefix.data_at])
    obtain ⟨clearPeak,clearing⟩ := WordSelect.cleanup_execution (FieldReplace.output input 1 (Encoding.frameCount prior.length prior.flatten))
    rw [FieldSet.clean_replacement] at clearing
    have sourceEmpty : FieldReplace.output input 1 (Encoding.frameCount prior.length prior.flatten) (some 0)=[] := by
      simp [FieldReplace.output,WordSelect.output,bank_source,Ne.symm (FieldGet.field_ne 1 0 (by decide))]
    have countEmpty : FieldReplace.output input 1 (Encoding.frameCount prior.length prior.flatten) (some 10)=[] := by
      simp [FieldReplace.output,WordSelect.output,WordSkip.reader_at,Ne.symm (FieldGet.field_ne 1 10 (by decide))]
    simp only [sourceEmpty,countEmpty,List.length_nil,Nat.zero_add] at clearing
    have trace := (preparing.link joined).link clearing
    have final : result input words=FieldReplace.output input 1 (Encoding.frameCount prior.length prior.flatten) := by simp [result,words,prior]
    rw [← final] at trace
    have countBound : prior.length ≤ words.length := by simp [prior]
    have payloadBound : prior.flatten.length ≤ words.flatten.length := by
      have equation := congrArg List.length source
      simp only [List.length_append] at equation
      omega
    have product := Nat.mul_le_mul_right (16*width+22) countBound
    have identity : 4*words.length+words.length*(16*width+22)=words.length*(16*width+26) := by ring
    refine ⟨_,_,trace,?_⟩
    dsimp only [words] at *
    omega

theorem total_polynomial (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (ready : FieldPrepare.Ready 1 input width words) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,result input words⟩ ticks peak ∧
      ticks ≤ 16*(FieldGrowth.size input)^2+49*FieldGrowth.size input+50 ∧ peak ≤ 16*(FieldGrowth.size input)^2+50*FieldGrowth.size input+50 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution input width words ready
  have cell (port : Port) : (input port).length ≤ FieldGrowth.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have packetBound : (Encoding.frameCount words.length words.flatten).length ≤ FieldGrowth.size input := by simpa only [ready.packet] using cell (some (FieldGet.field 1))
  have wBound : width ≤ FieldGrowth.size input := by simpa only [ready.widthStored,List.length_replicate] using cell (some 8)
  have packetLength : (Encoding.frameCount words.length words.flatten).length=words.length+1+words.flatten.length := by
    simp only [Encoding.frameCount,List.length_append,List.length_replicate,List.length_cons]; omega
  have nBound : words.length ≤ FieldGrowth.size input := by omega
  have product := Nat.mul_le_mul nBound (Nat.add_le_add_right (Nat.mul_le_mul_left 16 wBound) 26)
  have identity : 6*FieldGrowth.size input+FieldGrowth.size input*(16*FieldGrowth.size input+26)+15*FieldGrowth.size input+2*FieldGrowth.size input+50=
      16*(FieldGrowth.size input)^2+49*FieldGrowth.size input+50 := by ring
  have bounded : ticks ≤ 16*(FieldGrowth.size input)^2+49*FieldGrowth.size input+50 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ FieldGrowth.size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 1044 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.HeapRelease
