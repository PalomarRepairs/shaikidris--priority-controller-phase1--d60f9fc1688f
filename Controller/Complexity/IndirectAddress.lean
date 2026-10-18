module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.HeapRead

@[expose] public section

/-! A fetched register operand is read from the old register file and moved
into the binary address bank. Replacement27 is consumed and cleared. -/
namespace Controller.Complexity.IndirectAddress
open StackMachine WordReader
open scoped BigOperators

def output (input : Port → List Bool) (value : Controller.Cost.Word width) :=
  Function.update (Function.update input (some 27) []) (some 3) (Encoding.bits width value.val)

def sourceProgram (position : Fin 3) : Program (Fin 31) CopyBody.SourceLabel := RegisterLoad.program position
def Label : Type := (CopyBody.SourceLabel ⊕ Fin 2) ⊕ (Fin 4 ⊕ Fin 4)
instance labelFintype : Fintype Label := inferInstanceAs (Fintype ((CopyBody.SourceLabel ⊕ Fin 2) ⊕ (Fin 4 ⊕ Fin 4)))
def program (position : Fin 3) : Program (Fin 31) Label := link (link (sourceProgram position) (StackClear.program (some 3 : Port)))
  (WordMove.program (some 27) (some 3) (some 2))

theorem stored_output (input : Port → List Bool) (value : Controller.Cost.Word width) (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (output input value) state :=
  (stored.update_other input state (some 27) [] (by decide)).update_other (Function.update input (some 27) []) state (some 3) (Encoding.bits width value.val) (by decide)

theorem clear_output (input : Port → List Bool) (value : Controller.Cost.Word width) (clean : ∀ port ∈ FieldSet.work, input port=[]) :
    ∀ port ∈ FieldSet.work, output input value port=[] := by
  intro port member
  have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  have h3 : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  simpa [output,h27,h3] using clean port member

theorem size_output (input : Port → List Bool) (value : Controller.Cost.Word width) :
    FetchSetup.size (output input value) ≤ FetchSetup.size input+width := by
  have a := OperandLoad.update_size_le input (some 27) []
  have b := OperandLoad.update_size_le (Function.update input (some 27) []) (some 3) (Encoding.bits width value.val)
  simp only [List.length_nil,Nat.add_zero,Encoding.bits_length] at a b
  change FetchSetup.size (output input value) ≤ FetchSetup.size (Function.update input (some 27) [])+width at b
  omega

theorem execution (input : Port → List Bool) (operands values : List (Controller.Cost.Word width)) (position : Fin 3)
    (validPosition : position.val<operands.length) (validIndex : operands[position.val].val<values.length) (ready : RegisterRead.Ready input operands values) :
    ∃ ticks peak, Execution (program position) ⟨some (program position).main,input⟩ ⟨none,output input values[operands[position.val].val]⟩ ticks peak ∧
      ticks ≤ 27*(FetchSetup.size input)^2+143*FetchSetup.size input+127 ∧
      peak ≤ 27*(FetchSetup.size input)^2+144*FetchSetup.size input+127 := by
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := RegisterLoad.execution input operands values position validPosition validIndex ready
  let index := operands[position.val]
  let value := values[index.val]
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (RegisterLoad.output input index value) (some 3)
  simp only [RegisterLoad.output,RegisterRead.addressed,Function.update_of_ne (show (some 3 : Port) ≠ some 27 by decide),Function.update_self,Encoding.bits_length] at clearing
  obtain ⟨movePeak,moving⟩ := WordMove.execution (Function.update (RegisterLoad.output input index value) (some 3) [])
    (some 27) (some 3) (some 2) (by decide) (by decide) (by decide)
    (by simpa [RegisterLoad.output,RegisterRead.addressed] using ready.clear (some 2) (by simp [FieldSet.work]))
  simp only [Function.update_of_ne (show (some 27 : Port) ≠ some 3 by decide),RegisterLoad.output,Function.update_self,List.append_nil,Encoding.bits_length] at moving
  have final : Function.update (Function.update (Function.update (RegisterLoad.output input index value) (some 3) []) (some 27) []) (some 3) (Encoding.bits width value.val)=output input value := by
    funext address
    by_cases h3 : address=some 3 <;> by_cases h27 : address=some 27 <;> simp_all [RegisterLoad.output,RegisterRead.addressed,output]
  rw [show Function.update (Function.update (Function.update (Function.update (RegisterRead.addressed input index) (some 27) (Encoding.bits width value.val)) (some 3) []) (some 27) []) (some 3) (Encoding.bits width value.val)=output input value from final] at moving
  have trace := (reading.link clearing).link moving
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored,List.length_replicate] using cell
  have timeBound : (readTicks+(width+2))+(4*width+4) ≤ 27*(FetchSetup.size input)^2+143*FetchSetup.size input+127 := by omega
  have space := trace.peak_le
  change max (max readPeak clearPeak) movePeak ≤ FetchSetup.size input+((readTicks+(width+2))+(4*width+4)) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem canonical_card : Fintype.card Label=280 := by
  have split : Fintype.card Label=(Fintype.card CopyBody.SourceLabel+2)+(4+4) := by
    change Fintype.card ((CopyBody.SourceLabel ⊕ Fin 2) ⊕ (Fin 4 ⊕ Fin 4))=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [CopyBody.source_card] at split
  exact split

theorem resident (position : Fin 3) : (∑ label, statementSize (tmStatement ((program position).code label))) ≤ 2520 := by
  have bound := finiteTM_resident (program position)
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.IndirectAddress
