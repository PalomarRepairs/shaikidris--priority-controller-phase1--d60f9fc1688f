module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OperandRead
public import Controller.Complexity.WordSuccessor

@[expose] public section

/-! The stored singleton PC is read, incremented modulo its word width and
written back through executed field routines. Temporary value storage is erased;
all other original banks, including fetched instruction fields, are preserved. -/
namespace Controller.Complexity.PcAdvance
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (pc : Controller.Cost.Word width) : Prop where
  stored : input (some 8)=List.replicate width true
  pcStored : input (some (FieldGet.field 4))=Encoding.encodeWords width [pc]
  indexEmpty : input (some 3)=[]
  valueEmpty : input (some 27)=[]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def next (pc : Controller.Cost.Word width) := Controller.Cost.word width (pc.val+1)
def afterAdd (input : Port → List Bool) (pc : Controller.Cost.Word width) := Function.update input (some 27) (Encoding.bits width (next pc).val)
def output (input : Port → List Bool) (pc : Controller.Cost.Word width) := Function.update input (some (FieldGet.field 4)) (Encoding.encodeWords width [next pc])

def successorPorts : Option Bool ↪ Port := StackFrames.threePorts (some 1) (some 27) (some 2) (by decide) (by decide) (by decide)
theorem successorPorts_apply (port : Option Bool) : successorPorts port=(match port with | none => some 1 | some false => some 27 | some true => some 2) := rfl

def GetterLabel : Type := StateReader.LabelsOf (FieldGet.program (4 : Fin 5))
instance getterFintype : Fintype GetterLabel := inferInstanceAs (Fintype (StateReader.LabelsOf (FieldGet.program (4 : Fin 5))))
def SetterLabel : Type := StateReader.LabelsOf (FieldSet.program (4 : Fin 5))
instance setterFintype : Fintype SetterLabel := inferInstanceAs (Fintype (StateReader.LabelsOf (FieldSet.program (4 : Fin 5))))
def SuccessorLabel : Type := Fin 7 ⊕ ((Fin 4 ⊕ Fin 4) ⊕ Fin 4)
instance successorFintype : Fintype SuccessorLabel := inferInstanceAs (Fintype (Fin 7 ⊕ ((Fin 4 ⊕ Fin 4) ⊕ Fin 4)))
def getterProgram : Program (Fin 31) GetterLabel := FieldGet.program 4
def setterProgram : Program (Fin 31) SetterLabel := FieldSet.program 4
def successor : Program (Fin 31) SuccessorLabel := StackFrames.relocate successorPorts WordSuccessor.program
def Label : Type := ((GetterLabel ⊕ SuccessorLabel) ⊕ SetterLabel) ⊕ Fin 2
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (((GetterLabel ⊕ SuccessorLabel) ⊕ SetterLabel) ⊕ Fin 2))
def program : Program (Fin 31) Label := link (link (link getterProgram successor) setterProgram) (StackClear.program (some 27 : Port))

theorem getter_output (input : Port → List Bool) (pc : Controller.Cost.Word width) (ready : Ready input pc) :
    WordSelect.selected input [Encoding.bits width pc.val] []=Function.update input (some 1) (Encoding.bits width pc.val) := by
  funext address
  have status := ready.clear none (by simp [FieldSet.work])
  have source := ready.clear (some 0) (by simp [FieldSet.work])
  have word := ready.clear (some 1) (by simp [FieldSet.work])
  have scratch := ready.clear (some 2) (by simp [FieldSet.work])
  have counter := ready.clear (some 4) (by simp [FieldSet.work])
  have count := ready.clear (some 10) (by simp [FieldSet.work])
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 10 <;>
      simp_all [WordSelect.selected,Encoding.value,WordSelect.output,WordSkip.reader_at]

theorem successor_execution (input : Port → List Bool) (pc : Controller.Cost.Word width) (ready : Ready input pc) :
    ∃ peak, Execution successor ⟨some successor.main,Function.update input (some 1) (Encoding.bits width pc.val)⟩
      ⟨none,afterAdd input pc⟩ (8*width+8) peak := by
  have source (word : List Bool) : StackFrames.embedStorage successorPorts input (StackBlocks.layout word [] [])=Function.update input (some 1) word := by
    funext address
    have scratch := ready.clear (some 2) (by simp [FieldSet.work])
    by_cases hs : address=some 1 <;> by_cases hd : address=some 27 <;> by_cases ht : address=some 2 <;>
      simp_all [StackFrames.embedStorage,successorPorts_apply,StackBlocks.layout,ready.valueEmpty]
  have target (word : List Bool) : StackFrames.embedStorage successorPorts input (StackBlocks.layout [] word [])=Function.update input (some 27) word := by
    funext address
    have empty := ready.clear (some 1) (by simp [FieldSet.work])
    have scratch := ready.clear (some 2) (by simp [FieldSet.work])
    by_cases hs : address=some 1 <;> by_cases hd : address=some 27 <;> by_cases ht : address=some 2 <;>
      simp_all [StackFrames.embedStorage,successorPorts_apply,StackBlocks.layout]
  obtain ⟨peak,trace⟩ := WordSuccessor.encoded_execution width pc.val
  have lifted := StackFrames.execution successorPorts input trace
  exact ⟨peak+StackFrames.frameBits successorPorts input,
    by simpa only [successor,SuccessorLabel,StackFrames.relocate,StackFrames.embedState,source,target,afterAdd,next] using lifted⟩

theorem setter_ready (input : Port → List Bool) (pc : Controller.Cost.Word width) (ready : Ready input pc) :
    FieldSet.Ready 4 (afterAdd input pc) width [Encoding.bits width pc.val] [] (Encoding.bits width (next pc).val) where
  packet := by simpa [afterAdd,Encoding.encodeWords,Encoding.wordList,Encoding.wordEncoding,FieldGet.field] using ready.pcStored
  widthStored := by simpa [afterAdd] using ready.stored
  indexStored := by simp [afterAdd,ready.indexEmpty]
  replacementStored := by simp [afterAdd]
  widths := by intro word member; simp only [List.mem_singleton] at member; subst word; exact Encoding.bits_length width pc.val
  replacementWidth := Encoding.bits_length width (next pc).val
  clear := by
    intro port member
    have outside : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa only [afterAdd,Function.update_of_ne outside] using ready.clear port member

theorem setter_cleanup (input : Port → List Bool) (pc : Controller.Cost.Word width) (ready : Ready input pc) :
    Function.update (FieldSet.result 4 (afterAdd input pc) [Encoding.bits width pc.val] [] (Encoding.bits width (next pc).val)) (some 27) []=output input pc := by
  funext address
  have status := ready.clear none (by simp [FieldSet.work])
  have source := ready.clear (some 0) (by simp [FieldSet.work])
  have word := ready.clear (some 1) (by simp [FieldSet.work])
  have scratch := ready.clear (some 2) (by simp [FieldSet.work])
  have counter := ready.clear (some 4) (by simp [FieldSet.work])
  have count := ready.clear (some 10) (by simp [FieldSet.work])
  have buffer := ready.clear (some 20) (by simp [FieldSet.work])
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 10 <;>
    by_cases hf : address=some 20 <;> by_cases hv : address=some 27 <;> by_cases hp : address=some 25 <;>
      simp_all [FieldSet.result,Encoding.value,FieldReplace.output,WordSelect.output,WordSkip.reader_at,FieldSet.frame,
        afterAdd,output,Encoding.encodeWords,Encoding.wordList,Encoding.wordEncoding,FieldGet.field,ready.valueEmpty]

theorem execution (input : Port → List Bool) (pc : Controller.Cost.Word width) (ready : Ready input pc) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input pc⟩ ticks peak ∧
      ticks ≤ 92*width+215 ∧ peak ≤ FetchSetup.size input+92*width+215 := by
  have packet : input (some (FieldGet.field 4))=Encoding.frameCount [Encoding.bits width pc.val].length [Encoding.bits width pc.val].flatten := by
    simpa [Encoding.encodeWords,Encoding.wordList,Encoding.wordEncoding] using ready.pcStored
  have widths : ∀ word ∈ [Encoding.bits width pc.val], word.length=width := by
    intro word member
    simp only [List.mem_singleton] at member
    subst word
    exact Encoding.bits_length width pc.val
  obtain ⟨getTicks,getPeak,getting,getBound⟩ := FieldGet.execution 4 input width [Encoding.bits width pc.val] [] packet ready.stored ready.indexEmpty widths
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
    (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work])) (ready.clear _ (by simp [FieldSet.work]))
  rw [getter_output input pc ready] at getting
  obtain ⟨addPeak,adding⟩ := successor_execution input pc ready
  obtain ⟨setTicks,setPeak,setting,setBound⟩ := FieldSet.execution 4 (afterAdd input pc) width [Encoding.bits width pc.val] [] (Encoding.bits width (next pc).val) (setter_ready input pc ready)
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (FieldSet.result 4 (afterAdd input pc) [Encoding.bits width pc.val] [] (Encoding.bits width (next pc).val)) (some 27)
  rw [setter_cleanup input pc ready] at clearing
  have valueLength : (FieldSet.result 4 (afterAdd input pc) [Encoding.bits width pc.val] [] (Encoding.bits width (next pc).val) (some 27)).length=width := by
    simp [FieldSet.result,Encoding.value,FieldReplace.output,WordSelect.output,WordSkip.reader_at,FieldSet.frame,afterAdd,FieldGet.field]
  rw [valueLength] at clearing
  have trace := ((getting.link adding).link setting).link clearing
  simp [Encoding.frameCount] at getBound setBound
  have timeBound : getTicks+(8*width+8)+setTicks+(width+2) ≤ 92*width+215 := by omega
  have space := trace.peak_le
  change max (max (max getPeak addPeak) setPeak) clearPeak ≤ FetchSetup.size input+(getTicks+(8*width+8)+setTicks+(width+2)) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem getter_card : Fintype.card GetterLabel=172 := by
  have original : Fintype.card (StateReader.LabelsOf (FieldGet.program (4 : Fin 5)))=172 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card GetterLabel=Fintype.card (StateReader.LabelsOf (FieldGet.program (4 : Fin 5))) :=
    @Fintype.card_congr GetterLabel (StateReader.LabelsOf (FieldGet.program (4 : Fin 5))) _ _ (Equiv.refl _)
  exact same.trans original

theorem setter_card : Fintype.card SetterLabel=206 := by
  have original : Fintype.card (StateReader.LabelsOf (FieldSet.program (4 : Fin 5)))=206 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card SetterLabel=Fintype.card (StateReader.LabelsOf (FieldSet.program (4 : Fin 5))) :=
    @Fintype.card_congr SetterLabel (StateReader.LabelsOf (FieldSet.program (4 : Fin 5))) _ _ (Equiv.refl _)
  exact same.trans original

theorem successor_card : Fintype.card SuccessorLabel=19 := by
  have split : Fintype.card SuccessorLabel=7+((4+4)+4) := by
    change Fintype.card (Fin 7 ⊕ ((Fin 4 ⊕ Fin 4) ⊕ Fin 4))=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  exact split

theorem canonical_card : Fintype.card Label=399 := by
  have split : Fintype.card Label=(Fintype.card GetterLabel+Fintype.card SuccessorLabel)+Fintype.card SetterLabel+2 := by
    change Fintype.card (((GetterLabel ⊕ SuccessorLabel) ⊕ SetterLabel) ⊕ Fin 2)=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [getter_card,successor_card,setter_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 3591 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.PcAdvance
