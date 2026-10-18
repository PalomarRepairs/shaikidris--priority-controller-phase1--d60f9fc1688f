module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OperandLoad

@[expose] public section

/-! A fetched source register is read and its actual returned value loaded
into replacement27. Source address3 is retained; returned-word1 and scratch2
are cleared. Other state, instruction and ambient banks are preserved. -/
namespace Controller.Complexity.RegisterLoad
open StackMachine WordReader
open scoped BigOperators

def program (position : Fin 3) := link (link (RegisterRead.program position) (StackClear.program (some 27 : Port)))
  (WordMove.program (some 1) (some 27) (some 2))

def output (input : Port → List Bool) (index value : Controller.Cost.Word width) :=
  Function.update (RegisterRead.addressed input index) (some 27) (Encoding.bits width value.val)

theorem clear_output (input : Port → List Bool) (index value : Controller.Cost.Word width)
    (clean : ∀ port ∈ FieldSet.work, input port=[]) : ∀ port ∈ FieldSet.work, output input index value port=[] := by
  intro port member
  have indexOutside : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  have valueOutside : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  simpa [output,RegisterRead.addressed,indexOutside,valueOutside] using clean port member

theorem stored_output (input : Port → List Bool) (index value : Controller.Cost.Word width)
    (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (output input index value) state :=
  (stored.update_other input state (some 3) (Encoding.bits width index.val) (by decide)).update_other
    (RegisterRead.addressed input index) state (some 27) (Encoding.bits width value.val) (by decide)

theorem size_output (input : Port → List Bool) (index value : Controller.Cost.Word width) :
    FetchSetup.size (output input index value) ≤ FetchSetup.size input+2*width := by
  have first := OperandLoad.update_size_le input (some 3) (Encoding.bits width index.val)
  have second := OperandLoad.update_size_le (RegisterRead.addressed input index) (some 27) (Encoding.bits width value.val)
  simp only [Encoding.bits_length] at first second
  change FetchSetup.size (RegisterRead.addressed input index) ≤ FetchSetup.size input+width at first
  change FetchSetup.size (output input index value) ≤ FetchSetup.size (RegisterRead.addressed input index)+width at second
  omega

theorem execution (input : Port → List Bool) (operands values : List (Controller.Cost.Word width)) (position : Fin 3)
    (validPosition : position.val<operands.length) (validIndex : operands[position.val].val<values.length)
    (ready : RegisterRead.Ready input operands values) :
    ∃ ticks peak, Execution (program position) ⟨some (program position).main,input⟩
      ⟨none,output input operands[position.val] values[operands[position.val].val]⟩ ticks peak ∧
      ticks ≤ 27*(FetchSetup.size input)^2+138*FetchSetup.size input+121 ∧
      peak ≤ 27*(FetchSetup.size input)^2+139*FetchSetup.size input+121 := by
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := RegisterRead.execution input operands values position validPosition validIndex ready
  let index := operands[position.val]
  let value := values[index.val]
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (RegisterRead.output input index value) (some 27)
  simp only [RegisterRead.output,RegisterRead.addressed,
    Function.update_of_ne (show (some 27 : Port) ≠ some 1 by decide),Function.update_of_ne (show (some 27 : Port) ≠ some 3 by decide)] at clearing
  obtain ⟨movePeak,moving⟩ := WordMove.execution (Function.update (RegisterRead.output input index value) (some 27) [])
    (some 1) (some 27) (some 2) (by decide) (by decide) (by decide)
    (by simpa [RegisterRead.output,RegisterRead.addressed] using ready.clear (some 2) (by simp [FieldSet.work]))
  simp only [Function.update_of_ne (show (some 1 : Port) ≠ some 27 by decide),RegisterRead.output,
    Function.update_self,List.append_nil,Encoding.bits_length] at moving
  have final : Function.update (Function.update (Function.update (RegisterRead.output input index value) (some 27) []) (some 1) [])
      (some 27) (Encoding.bits width value.val)=output input index value := by
    funext address
    have wordEmpty := ready.clear (some 1) (by simp [FieldSet.work])
    by_cases hw : address=some 1 <;> by_cases hi : address=some 3 <;> by_cases hv : address=some 27 <;>
      simp_all [RegisterRead.output,RegisterRead.addressed,output]
  rw [show Function.update (Function.update (Function.update (Function.update (RegisterRead.addressed input index) (some 1) (Encoding.bits width value.val)) (some 27) []) (some 1) []) (some 27) (Encoding.bits width value.val)=output input index value from final] at moving
  have trace := (reading.link clearing).link moving
  have cell (port : Port) : (input port).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored,List.length_replicate] using cell (some 8)
  have timeBound : (readTicks+((input (some 27)).length+2))+(4*width+4) ≤ 27*(FetchSetup.size input)^2+138*FetchSetup.size input+121 := by
    have valueBound := cell (some 27)
    omega
  have space := trace.peak_le
  change max (max readPeak clearPeak) movePeak ≤ FetchSetup.size input+((readTicks+((input (some 27)).length+2))+(4*width+4)) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem resident (position : Fin 3) : (∑ label, statementSize (tmStatement ((program position).code label))) ≤ 2430 := by
  simpa only [Fintype.card_sum,RegisterRead.canonical_card,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (program position)

end Controller.Complexity.RegisterLoad
