module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.PrependBody

@[expose] public section

/-! A concrete singleton-PC writer uses the empty binary index for zero,
writes the supplied target word and clears replacement27. It performs no
successor operation; this is the taken branch's absolute PC assignment. -/
namespace Controller.Complexity.PcWrite
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (old target : Controller.Cost.Word width) : Prop where
  widthStored : input (some 8)=List.replicate width true
  pcStored : input (some 25)=Encoding.encodeWords width [old]
  indexEmpty : input (some 3)=[]
  valueStored : input (some 27)=Encoding.bits width target.val
  clear : ∀ port ∈ FieldSet.work, input port=[]

def program : Program (Fin 31) (PcAdvance.SetterLabel ⊕ Fin 2) := link PcAdvance.setterProgram (StackClear.program (some 27))
def output (input : Port → List Bool) (target : Controller.Cost.Word width) :=
  Function.update (Function.update input (some 27) []) (some 25) (Encoding.encodeWords width [target])

theorem fields (input : Port → List Bool) (old target : Controller.Cost.Word width) (ready : Ready input old target) :
    FieldSet.Ready 4 input width [Encoding.bits width old.val] [] (Encoding.bits width target.val) where
  packet := by simpa [Encoding.encodeWords,Encoding.wordList,Encoding.wordEncoding,FieldGet.field] using ready.pcStored
  widthStored := ready.widthStored
  indexStored := ready.indexEmpty
  replacementStored := ready.valueStored
  widths := by intro word member; simp only [List.mem_singleton] at member; subst word; exact Encoding.bits_length width old.val
  replacementWidth := Encoding.bits_length width target.val
  clear := ready.clear

theorem set_output (input : Port → List Bool) (old target : Controller.Cost.Word width) (ready : Ready input old target) :
    FieldSet.result 4 input [Encoding.bits width old.val] [] (Encoding.bits width target.val)=
      Function.update input (some 25) (Encoding.encodeWords width [target]) := by
  simp only [FieldSet.result,Encoding.value,List.length_singleton,Nat.zero_lt_one,ite_true,List.take_zero,List.flatten_nil,
    Nat.zero_add,List.drop_one,List.flatten_nil,List.nil_append]
  rw [FieldPrepare.frame_output,NativeFieldUpdate.replacement input 4 _ ready.clear]
  rfl

theorem stored_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (target : Controller.Cost.Word width)
    (stored : NativeStore.Stored input state) : NativeStore.Stored (output input target) { state with pc := target } := by
  have relation := stored.update_other input state (some 27) [] (by decide)
  rcases relation with ⟨hw,hr,hreg,hh,hs,ho,hpc,hhalt⟩
  constructor <;> simp_all [output]

theorem execution (input : Port → List Bool) (old target : Controller.Cost.Word width) (ready : Ready input old target) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input target⟩ ticks peak ∧
      ticks ≤ 31*(FetchSetup.size input)^2+89*FetchSetup.size input+76 ∧
      peak ≤ 31*(FetchSetup.size input)^2+90*FetchSetup.size input+76 := by
  obtain ⟨setTicks,setPeak,setting,setBound,_⟩ := FieldSet.total_polynomial 4 input width [Encoding.bits width old.val] [] (Encoding.bits width target.val) (fields input old target ready)
  rw [set_output input old target ready] at setting
  change setTicks ≤ 31*(FetchSetup.size input)^2+88*FetchSetup.size input+74 at setBound
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (Function.update input (some 25) (Encoding.encodeWords width [target])) (some 27)
  simp only [Function.update_of_ne (show (some 27 : Port) ≠ some 25 by decide),ready.valueStored,Encoding.bits_length] at clearing
  have final : Function.update (Function.update input (some 25) (Encoding.encodeWords width [target])) (some 27) []=output input target := by
    funext port
    by_cases hv : port=some 27 <;> by_cases hp : port=some 25 <;> simp_all [output]
  rw [final] at clearing
  have trace := setting.link clearing
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.widthStored,List.length_replicate] using cell
  have timeBound : setTicks+(width+2) ≤ 31*(FetchSetup.size input)^2+89*FetchSetup.size input+76 := by omega
  have space := trace.peak_le
  exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 1872 := by
  have bound := finiteTM_resident program
  simp only [Fintype.card_sum,Fintype.card_fin,PcAdvance.setter_card,Nat.reduceAdd,Nat.reduceMul] at bound
  exact bound

end Controller.Complexity.PcWrite
