module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.PcAdvance

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Register operands are read from the fetched instruction, moved into the
binary index bank and looked up through the executed persistent-field reader.
The index and returned value are explicit; all other banks are preserved. -/
namespace Controller.Complexity.RegisterRead
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (operands values : List (Controller.Cost.Word width)) : Prop where
  payload : input (some 11)=Encoding.wordList width operands
  stored : input (some 8)=List.replicate width true
  registersStored : input (some (FieldGet.field 0))=Encoding.encodeWords width values
  clear : ∀ port ∈ FieldSet.work, input port=[]

def addressed (input : Port → List Bool) (index : Controller.Cost.Word width) := Function.update input (some 3) (Encoding.bits width index.val)
def output (input : Port → List Bool) (index value : Controller.Cost.Word width) := Function.update (addressed input index) (some 1) (Encoding.bits width value.val)

def OperandLabel : Type := StateReader.LabelsOf (OperandRead.program 0)
instance operandFintype : Fintype OperandLabel := inferInstanceAs (Fintype (StateReader.LabelsOf (OperandRead.program 0)))
def operandProgram (position : Fin 3) : Program (Fin 31) OperandLabel := OperandRead.program position
def getterProgram : Program (Fin 31) PcAdvance.GetterLabel := FieldGet.program 0
def Label : Type := ((OperandLabel ⊕ Fin 2) ⊕ (Fin 4 ⊕ Fin 4)) ⊕ PcAdvance.GetterLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (((OperandLabel ⊕ Fin 2) ⊕ (Fin 4 ⊕ Fin 4)) ⊕ PcAdvance.GetterLabel))
def program (position : Fin 3) : Program (Fin 31) Label := link (link (link (operandProgram position) (StackClear.program (some 3 : Port)))
  (WordMove.program (some 1) (some 3) (some 2))) getterProgram

theorem move_output (input : Port → List Bool) (index : Controller.Cost.Word width)
    (empty : input (some 1)=[]) :
    Function.update (Function.update (Function.update (Function.update input (some 1) (Encoding.bits width index.val)) (some 3) []) (some 1) [])
      (some 3) (Encoding.bits width index.val)=addressed input index := by
  funext address
  by_cases hw : address=some 1 <;> by_cases hi : address=some 3 <;> simp_all [addressed]

theorem selected_output (input : Port → List Bool) (values : List (Controller.Cost.Word width)) (index : Controller.Cost.Word width)
    (valid : index.val<values.length) (clean : ∀ port ∈ FieldSet.work, input port=[]) :
    WordSelect.selected (addressed input index) (FieldSetNative.bits values) (Encoding.bits width index.val)=output input index values[index.val] := by
  rw [show FieldSetNative.bits values=values.map (fun value => Encoding.bits width value.val) from rfl,FieldGet.native_selected]
  simp only [FieldGet.native_output,dite_eq_left valid]
  funext address
  have status := clean none (by simp [FieldSet.work])
  have source := clean (some 0) (by simp [FieldSet.work])
  have scratch := clean (some 2) (by simp [FieldSet.work])
  have counter := clean (some 4) (by simp [FieldSet.work])
  have count := clean (some 10) (by simp [FieldSet.work])
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 10 <;>
      simp_all [WordSelect.output,WordSkip.reader_at,addressed,output]

theorem execution (input : Port → List Bool) (operands values : List (Controller.Cost.Word width)) (position : Fin 3)
    (validPosition : position.val<operands.length) (validIndex : operands[position.val].val<values.length)
    (ready : Ready input operands values) :
    ∃ ticks peak, Execution (program position) ⟨some (program position).main,input⟩
      ⟨none,output input operands[position.val] values[operands[position.val].val]⟩ ticks peak ∧
      ticks ≤ 27*(FetchSetup.size input)^2+133*FetchSetup.size input+115 ∧
      peak ≤ 27*(FetchSetup.size input)^2+134*FetchSetup.size input+115 := by
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := OperandRead.encoded_total input operands position validPosition ready.payload ready.stored
    (by
      intro port member
      apply ready.clear port
      simp only [OperandRead.work,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl <;> simp [FieldSet.work])
  let index := operands[position.val]
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (Function.update input (some 1) (Encoding.bits width index.val)) (some 3)
  simp only [Function.update_of_ne (show (some 3 : Port) ≠ some 1 by decide)] at clearing
  obtain ⟨movePeak,moving⟩ := WordMove.execution (Function.update (Function.update input (some 1) (Encoding.bits width index.val)) (some 3) [])
    (some 1) (some 3) (some 2) (by decide) (by decide) (by decide)
    (by simpa using ready.clear (some 2) (by simp [FieldSet.work]))
  simp only [Function.update_self,Function.update_of_ne (show (some 1 : Port) ≠ some 3 by decide),List.append_nil,Encoding.bits_length] at moving
  rw [move_output input index (ready.clear _ (by simp [FieldSet.work]))] at moving
  have clean : ∀ port ∈ FieldSet.work, addressed input index port=[] := by
    intro port member
    have outside : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa only [addressed,Function.update_of_ne outside] using ready.clear port member
  have packet : addressed input index (some (FieldGet.field 0))=Encoding.frameCount (FieldSetNative.bits values).length (FieldSetNative.bits values).flatten := by
    simpa [addressed,FieldGet.field,FieldSetNative.bits,FieldGet.mapped_flatten,Encoding.encodeWords] using ready.registersStored
  have widths : ∀ word ∈ FieldSetNative.bits values, word.length=width := by
    intro word member
    obtain ⟨value,_,rfl⟩ := List.mem_map.mp member
    exact Encoding.bits_length width value.val
  obtain ⟨getTicks,getPeak,getting,getBound⟩ := FieldGet.execution 0 (addressed input index) width (FieldSetNative.bits values) (Encoding.bits width index.val)
    packet (by simpa [addressed] using ready.stored) (by simp [addressed]) widths
    (clean _ (by simp [FieldSet.work])) (clean _ (by simp [FieldSet.work])) (clean _ (by simp [FieldSet.work]))
    (clean _ (by simp [FieldSet.work])) (clean _ (by simp [FieldSet.work])) (clean _ (by simp [FieldSet.work]))
    (clean _ (by simp [FieldSet.work])) (clean _ (by simp [FieldSet.work])) (clean _ (by simp [FieldSet.work]))
    (clean _ (by simp [FieldSet.work])) (clean _ (by simp [FieldSet.work]))
  rw [selected_output input values index validIndex ready.clear] at getting
  have trace := ((reading.link clearing).link moving).link getting
  have cell (port : Port) : (input port).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored,List.length_replicate] using cell (some 8)
  have packetBound : (Encoding.frameCount (FieldSetNative.bits values).length (FieldSetNative.bits values).flatten).length ≤ FetchSetup.size input := by
    simpa only [FieldSetNative.bits,List.length_map,FieldGet.mapped_flatten,Encoding.encodeWords,ready.registersStored] using cell (some (FieldGet.field 0))
  have countBound : (FieldSetNative.bits values).length ≤ FetchSetup.size input := by simp [Encoding.frameCount] at packetBound; omega
  have product := Nat.mul_le_mul wBound (Nat.add_le_add_right (Nat.mul_le_mul_left 11 countBound) 33)
  have secondProduct := Nat.mul_le_mul countBound (Nat.add_le_add_right (Nat.mul_le_mul_left 16 wBound) 26)
  simp only [Encoding.bits_length] at getBound
  have getTime : getTicks ≤ 27*(FetchSetup.size input)^2+78*FetchSetup.size input+56 := by
    have identity : 5*FetchSetup.size input+FetchSetup.size input*(11*FetchSetup.size input+33)+
        FetchSetup.size input*(16*FetchSetup.size input+26)+14*FetchSetup.size input+56=
        27*(FetchSetup.size input)^2+78*FetchSetup.size input+56 := by ring
    rw [← identity]
    omega
  change readTicks ≤ 50*FetchSetup.size input+53 at readBound
  have timeBound : ((readTicks+((input (some 3)).length+2))+(4*width+4))+getTicks ≤
      27*(FetchSetup.size input)^2+133*FetchSetup.size input+115 := by have indexBound := cell (some 3); omega
  have space := trace.peak_le
  change max (max (max readPeak clearPeak) movePeak) getPeak ≤ FetchSetup.size input+
    (((readTicks+((input (some 3)).length+2))+(4*width+4))+getTicks) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem operand_card : Fintype.card OperandLabel=78 := by
  have original : Fintype.card (StateReader.LabelsOf (OperandRead.program 0))=78 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card OperandLabel=Fintype.card (StateReader.LabelsOf (OperandRead.program 0)) :=
    @Fintype.card_congr OperandLabel (StateReader.LabelsOf (OperandRead.program 0)) _ _ (Equiv.refl _)
  exact same.trans original

theorem canonical_card : Fintype.card Label=260 := by
  have split : Fintype.card Label=((Fintype.card OperandLabel+2)+(4+4))+Fintype.card PcAdvance.GetterLabel := by
    change Fintype.card (((OperandLabel ⊕ Fin 2) ⊕ (Fin 4 ⊕ Fin 4)) ⊕ PcAdvance.GetterLabel)=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [operand_card,PcAdvance.getter_card] at split
  exact split

theorem resident (position : Fin 3) : (∑ label, statementSize (tmStatement ((program position).code label))) ≤ 2340 := by
  have bound := finiteTM_resident (program position)
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.RegisterRead
