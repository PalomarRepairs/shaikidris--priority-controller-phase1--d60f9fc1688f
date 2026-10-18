module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FieldReplace

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A binary-indexed update of one persistent fixed-width field. A preserved
copy supplies the count and payload; an actual range check guards reconstruction.
Failure retains the original field, and both branches clear traversal workspace. -/
namespace Controller.Complexity.FieldSet
open StackMachine WordReader
open scoped BigOperators

def work : List Port := [none,some 0,some 1,some 2,some 4,some 5,some 6,some 7,some 10,some 16,some 17,some 20]

structure Ready (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (index replacement : List Bool) : Prop where
  packet : input (some (FieldGet.field slot))=Encoding.frameCount words.length words.flatten
  widthStored : input (some 8)=List.replicate width true
  indexStored : input (some 3)=index
  replacementStored : input (some 27)=replacement
  widths : ∀ word ∈ words, word.length=width
  replacementWidth : replacement.length=width
  clear : ∀ port ∈ work, input port=[]

def frame (input : Port → List Bool) (words : List (List Bool)) : Port → List Bool :=
  Function.update input (some 10) (List.replicate words.length true)

def prepared (input : Port → List Bool) (words : List (List Bool)) := WordSkip.data (frame input words) 0 words.flatten

def prepare (slot : Fin 5) := link (FieldGet.copyMachine slot) (ColdInput.readSave 10)
def updateBody (slot : Fin 5) := GuardedLink.program IndexPlan.program (FieldReplace.program slot) none Option.isNone
def program (slot : Fin 5) := link (link (prepare slot) (updateBody slot)) WordSelect.cleanup

def result (slot : Fin 5) (input : Port → List Bool) (words : List (List Bool)) (index replacement : List Bool) : Port → List Bool :=
  if Encoding.value index<words.length then FieldReplace.output (frame input words) slot
    (Encoding.frameCount words.length ((words.take (Encoding.value index)).flatten++
      (replacement++(words.drop (Encoding.value index+1)).flatten)))
  else WordSelect.output (frame input words) [false] []

theorem prepare_execution (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (index replacement : List Bool)
    (ready : Ready slot input width words index replacement) :
    ∃ peak, Execution (prepare slot) ⟨some (prepare slot).main,input⟩ ⟨none,prepared input words⟩
      (5*(Encoding.frameCount words.length words.flatten).length+4*words.length+8) peak := by
  obtain ⟨copyPeak,copying⟩ := FieldGet.copy_execution slot input _ ready.packet (ready.clear _ (by simp [work])) (ready.clear _ (by simp [work]))
  have reading := ColdInput.read_save_execution input 10 (by decide) (by decide) (by decide) words.length words.flatten [] (ready.clear _ (by simp [work]))
  have entry : bank input [] (Encoding.frameCount words.length words.flatten) []=
      Function.update input (some 0) (Encoding.frameCount words.length words.flatten) := by
    funext address
    have status := ready.clear none (by simp [work])
    have wordClean := ready.clear (some 1) (by simp [work])
    have scratch := ready.clear (some 2) (by simp [work])
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> simp_all [WordSkip.reader_at]
  have next : bank (frame input words) [] words.flatten []=prepared input words := by
    funext address
    have countClean := ready.clear (some 4) (by simp [work])
    by_cases hn : address=some 4 <;> simp_all [prepared,frame,WordSkip.reader_at,WordSkip.data_at]
  change Execution (ColdInput.readSave 10) _ ⟨none,bank (frame input words) [] words.flatten []⟩ _ _ at reading
  rw [entry,next] at reading
  have ticks : (5*(Encoding.frameCount words.length words.flatten).length+4)+(4*words.length+4)=
      5*(Encoding.frameCount words.length words.flatten).length+4*words.length+8 := by omega
  exact ⟨_,by simpa only [prepare,ticks] using copying.link reading⟩

theorem plan_execution (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (index replacement : List Bool)
    (ready : Ready slot input width words index replacement) :
    ∃ ticks peak, Execution IndexPlan.program ⟨some IndexPlan.program.main,prepared input words⟩
      ⟨none,IndexPlan.result (prepared input words) index words.length⟩ ticks peak ∧
      ticks ≤ index.length*(11*words.length+33)+6*words.length+30 := by
  have clean (port : Port) (member : port ∈ work) := ready.clear port member
  apply IndexPlan.execution
  all_goals simp_all [prepared,frame,WordSkip.data_at,work,ready.indexStored]

theorem planned_success (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (index replacement : List Bool)
    (ready : Ready slot input width words index replacement) (valid : Encoding.value index<words.length) :
    IndexPlan.result (prepared input words) index words.length=
      WordPrefix.data (frame input words) (Encoding.value index) words.flatten [] := by
  unfold prepared
  rw [WordSelect.planned_output (frame input words) words.flatten index words.length valid]
  funext address
  have buffer := ready.clear (some 20) (by simp [work])
  by_cases hb : address=some 20 <;> simp_all [WordSkip.data_at,WordPrefix.data_at,frame]

theorem clean_replacement (input : Port → List Bool) (slot : Fin 5) (packet : List Bool) :
    Function.update (Function.update (FieldReplace.output input slot packet) (some 0) []) (some 10) []=
      FieldReplace.output input slot packet := by
  funext address
  by_cases hs : address=some 0 <;> by_cases hn : address=some 10 <;>
    simp_all [FieldReplace.output,WordSelect.output,WordSkip.reader_at,
      Ne.symm (FieldGet.field_ne slot 0 (by decide)),Ne.symm (FieldGet.field_ne slot 10 (by decide))]

theorem execution (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (index replacement : List Bool)
    (ready : Ready slot input width words index replacement) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩
      ⟨none,result slot input words index replacement⟩ ticks peak ∧
      ticks ≤ 6*(Encoding.frameCount words.length words.flatten).length+index.length*(11*words.length+33)+
        words.length*(20*width+27)+22*width+74 := by
  obtain ⟨preparePeak,preparing⟩ := prepare_execution slot input width words index replacement ready
  obtain ⟨planTicks,planPeak,planning,planBound⟩ := plan_execution slot input width words index replacement ready
  by_cases valid : Encoding.value index<words.length
  · let left := words.take (Encoding.value index)
    let right := words.drop (Encoding.value index+1)
    let oldWord := words[Encoding.value index]
    let payload := left.flatten++(replacement++right.flatten)
    have leftLength : left.length=Encoding.value index := by simp [left,Nat.min_eq_left (Nat.le_of_lt valid)]
    have split : words=left++oldWord::right := by
      dsimp [left,oldWord,right]
      rw [← List.drop_eq_getElem_cons valid,List.take_append_drop]
    have cardinality : words.length=left.length+1+right.length := by
      have equality := congrArg List.length split
      simp only [List.length_append,List.length_cons] at equality
      omega
    have source : words.flatten=left.flatten++(oldWord++right.flatten) := by
      conv_lhs => rw [split,List.flatten_append,List.flatten_cons]
    have leftWidths : ∀ word ∈ left, word.length=width := by intro word member; exact ready.widths word (List.mem_of_mem_take member)
    have rightWidths : ∀ word ∈ right, word.length=width := by intro word member; exact ready.widths word (List.mem_of_mem_drop member)
    rw [planned_success slot input width words index replacement ready valid,← leftLength,source] at planning
    obtain ⟨replacePeak,replacing⟩ := FieldReplace.execution (frame input words) slot width words.length left oldWord replacement right
      (by simpa [frame] using ready.widthStored) (by simp [frame]) (by simpa [frame] using ready.replacementStored) leftWidths
      (ready.widths oldWord (List.getElem_mem valid)) ready.replacementWidth
    have packetLength : (frame input words (some (FieldGet.field slot))).length=(Encoding.frameCount words.length words.flatten).length := by
      simp [frame,FieldGet.field_ne slot 10 (by decide),ready.packet]
    rw [packetLength] at replacing
    have updating := GuardedLink.success none Option.isNone planning replacing (by simp [WordPrefix.data_at])
    obtain ⟨clearPeak,clearing⟩ := WordSelect.cleanup_execution (FieldReplace.output (frame input words) slot (Encoding.frameCount words.length payload))
    rw [clean_replacement] at clearing
    have zeroSource : FieldReplace.output (frame input words) slot (Encoding.frameCount words.length payload) (some 0)=[] := by
      simp [FieldReplace.output,WordSelect.output,bank_source,Ne.symm (FieldGet.field_ne slot 0 (by decide))]
    have zeroCount : FieldReplace.output (frame input words) slot (Encoding.frameCount words.length payload) (some 10)=[] := by
      simp [FieldReplace.output,WordSelect.output,WordSkip.reader_at,Ne.symm (FieldGet.field_ne slot 10 (by decide))]
    simp only [zeroSource,zeroCount,List.length_nil,Nat.zero_add] at clearing
    have trace := (preparing.link updating).link clearing
    have final : result slot input words index replacement=FieldReplace.output (frame input words) slot (Encoding.frameCount words.length payload) := by
      simp only [result,ite_eq_left valid]; rfl
    rw [← final] at trace
    have leftMass := WordSelect.flatten_length width left leftWidths
    have rightMass := WordSelect.flatten_length width right rightWidths
    have payloadMass : payload.length=words.length*width := by
      simp only [payload,List.length_append,leftMass,rightMass,ready.replacementWidth]
      rw [cardinality]
      ring
    have leftBound : left.length ≤ words.length := by omega
    have rightBound : right.length ≤ words.length := by omega
    have product := Nat.mul_le_mul_right (16*width+15) leftBound
    have restBound := Nat.mul_le_mul_right width rightBound
    have identity : 4*words.length+6*words.length+words.length*(16*width+15)+22*width+2*(words.length*width)+
        2*(words.length*width)+2*words.length+74=words.length*(20*width+27)+22*width+74 := by ring
    refine ⟨(5*(Encoding.frameCount words.length words.flatten).length+4*words.length+8)+
      (planTicks+(left.length*(16*width+15)+22*width+2*right.flatten.length+(Encoding.frameCount words.length words.flatten).length+2*payload.length+2*words.length+32))+4,_,trace,?_⟩
    omega
  · have rejected : IndexPlan.result (prepared input words) index words.length=
        bank (Function.update (frame input words) (some 4) []) [false] words.flatten [] := by
      funext address
      by_cases hc : address=none <;> by_cases hn : address=some 4 <;>
        simp_all [IndexPlan.result,prepared,WordSkip.data_at,WordSkip.reader_at]
    rw [rejected] at planning
    have updating := GuardedLink.failure (FieldReplace.program slot) none Option.isNone planning (by simp [bank_counter])
    obtain ⟨clearPeak,clearing⟩ := WordSelect.cleanup_execution (bank (Function.update (frame input words) (some 4) []) [false] words.flatten [])
    rw [WordSelect.clean_output] at clearing
    have countLength : (bank (Function.update (frame input words) (some 4) []) [false] words.flatten [] (some 10)).length=words.length := by
      simp [WordSkip.reader_at,frame]
    simp only [bank_source,countLength] at clearing
    have trace := (preparing.link updating).link clearing
    have final : result slot input words index replacement=WordSelect.output (frame input words) [false] [] := by simp only [result,ite_eq_right valid]
    rw [← final] at trace
    have mass : words.flatten.length ≤ (Encoding.frameCount words.length words.flatten).length := by
      simp only [Encoding.frameCount,List.length_append,List.length_replicate,List.length_cons]
      omega
    have product := Nat.mul_le_mul_left words.length (show 11 ≤ 20*width+27 by omega)
    exact ⟨_,_,trace,by omega⟩

def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem total_polynomial (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (index replacement : List Bool)
    (ready : Ready slot input width words index replacement) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩
      ⟨none,result slot input words index replacement⟩ ticks peak ∧
      ticks ≤ 31*(size input)^2+88*size input+74 ∧ peak ≤ 31*(size input)^2+89*size input+74 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution slot input width words index replacement ready
  have cell (port : Port) : (input port).length ≤ size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have packetBound : (Encoding.frameCount words.length words.flatten).length ≤ size input := by simpa only [ready.packet] using cell (some (FieldGet.field slot))
  have countBound : words.length ≤ size input := by
    have framed : words.length ≤ (Encoding.frameCount words.length words.flatten).length := by simp [Encoding.frameCount]
    omega
  have wBound : width ≤ size input := by simpa only [ready.widthStored,List.length_replicate] using cell (some 8)
  have indexBound : index.length ≤ size input := by simpa only [ready.indexStored] using cell (some 3)
  have indexProduct := Nat.mul_le_mul indexBound (Nat.add_le_add_right (Nat.mul_le_mul_left 11 countBound) 33)
  have wordProduct := Nat.mul_le_mul countBound (Nat.add_le_add_right (Nat.mul_le_mul_left 20 wBound) 27)
  have identity : 6*size input+size input*(11*size input+33)+size input*(20*size input+27)+22*size input+74=
      31*(size input)^2+88*size input+74 := by ring
  have bounded : ticks ≤ 31*(size input)^2+88*size input+74 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident (slot : Fin 5) : (∑ label, statementSize (tmStatement ((program slot).code label))) ≤ 1854 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (program slot)

end Controller.Complexity.FieldSet
