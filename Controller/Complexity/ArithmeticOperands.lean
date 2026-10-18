module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ArithmeticKernel

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Both fetched arithmetic source registers are read from the old native
state. The first value is parked in28 before the second is loaded into27;
register storage is unchanged, including all source/destination aliases. -/
namespace Controller.Complexity.ArithmeticOperands
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (dst left right : Fin registers) : Prop where
  stored : NativeStore.Stored input state
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right]
  clear : ∀ port ∈ FieldSet.work, input port=[]
  bufferEmpty : input (some 28)=[]

def first (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (left : Fin registers) :=
  RegisterLoad.output input (InstructionCodec.registerWord bound left) (state.reg left)
def parked (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (left : Fin registers) :=
  Function.update (Function.update (first input state bound left) (some 27) []) (some 28) (Encoding.bits width (state.reg left).val)
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (left right : Fin registers) :=
  RegisterLoad.output (parked input state bound left) (InstructionCodec.registerWord bound right) (state.reg right)

def sourceProgram (position : Fin 3) : Program (Fin 31) CopyBody.SourceLabel := RegisterLoad.program position
def Label : Type := (CopyBody.SourceLabel ⊕ (Fin 4 ⊕ Fin 4)) ⊕ CopyBody.SourceLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype ((CopyBody.SourceLabel ⊕ (Fin 4 ⊕ Fin 4)) ⊕ CopyBody.SourceLabel))
def program : Program (Fin 31) Label := link (link (sourceProgram 1) (WordMove.program (some 27) (some 28) (some 2))) (sourceProgram 2)

theorem Ready.first (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) :
    RegisterRead.Ready input [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right] (List.ofFn state.reg) where
  payload := ready.payload
  stored := ready.stored.widthStored
  registersStored := by simpa [FieldGet.field] using ready.stored.registersStored
  clear := ready.clear

theorem parked_stored (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (left : Fin registers) (stored : NativeStore.Stored input state) : NativeStore.Stored (parked input state bound left) state :=
  ((RegisterLoad.stored_output input _ _ state stored).update_other (first input state bound left) state (some 27) [] (by decide)).update_other
    (Function.update (first input state bound left) (some 27) []) state (some 28) (Encoding.bits width (state.reg left).val) (by decide)

theorem parked_clear (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (left : Fin registers) (clean : ∀ port ∈ FieldSet.work, input port=[]) : ∀ port ∈ FieldSet.work, parked input state bound left port=[] := by
  intro port member
  have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  have h28 : port ≠ (some 28 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  simpa only [parked,ArithmeticOperands.first,Function.update_of_ne h27,Function.update_of_ne h28]
    using RegisterLoad.clear_output input (InstructionCodec.registerWord bound left) (state.reg left) clean port member

theorem Ready.second (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) :
    RegisterRead.Ready (parked input state bound left)
      [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right] (List.ofFn state.reg) where
  payload := by simpa [parked,ArithmeticOperands.first,RegisterLoad.output,RegisterRead.addressed] using ready.payload
  stored := (parked_stored input state bound left ready.stored).widthStored
  registersStored := by simpa [FieldGet.field] using (parked_stored input state bound left ready.stored).registersStored
  clear := parked_clear input state bound left ready.clear

theorem size_parked (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (left : Fin registers) :
    FetchSetup.size (parked input state bound left) ≤ FetchSetup.size input+3*width := by
  have a := RegisterLoad.size_output input (InstructionCodec.registerWord bound left) (state.reg left)
  have b := OperandLoad.update_size_le (first input state bound left) (some 27) []
  have c := OperandLoad.update_size_le (Function.update (first input state bound left) (some 27) []) (some 28) (Encoding.bits width (state.reg left).val)
  simp only [List.length_nil,Nat.add_zero,Encoding.bits_length] at b c
  change FetchSetup.size (first input state bound left) ≤ FetchSetup.size input+2*width at a
  change FetchSetup.size (parked input state bound left) ≤ FetchSetup.size (Function.update (first input state bound left) (some 27) [])+width at c
  omega

theorem size_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (left right : Fin registers) :
    FetchSetup.size (output input state bound left right) ≤ FetchSetup.size input+5*width := by
  have a := size_parked input state bound left
  have b := RegisterLoad.size_output (parked input state bound left) (InstructionCodec.registerWord bound right) (state.reg right)
  change FetchSetup.size (output input state bound left right) ≤ FetchSetup.size (parked input state bound left)+2*width at b
  omega

theorem stored_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (left right : Fin registers) (stored : NativeStore.Stored input state) : NativeStore.Stored (output input state bound left right) state :=
  RegisterLoad.stored_output (parked input state bound left) _ _ state (parked_stored input state bound left stored)

theorem clear_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (left right : Fin registers) (clean : ∀ port ∈ FieldSet.work, input port=[]) : ∀ port ∈ FieldSet.work, output input state bound left right port=[] :=
  RegisterLoad.clear_output _ _ _ (parked_clear input state bound left clean)

theorem kernel_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) (resultEmpty : input (some 29)=[]) :
    ArithmeticKernel.Ready (output input state bound left right) (state.reg left) (state.reg right) where
  leftStored := by simp [output,RegisterLoad.output,RegisterRead.addressed,parked]
  rightStored := by simp [output,RegisterLoad.output]
  resultEmpty := by simpa [output,RegisterLoad.output,RegisterRead.addressed,parked,first] using resultEmpty
  wordEmpty := clear_output input state bound left right ready.clear _ (by simp [FieldSet.work])
  scratchEmpty := clear_output input state bound left right ready.clear _ (by simp [FieldSet.work])

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state bound left right⟩ ticks peak ∧
      ticks ≤ 459*(FetchSetup.size input)^2+694*FetchSetup.size input+246 ∧
      peak ≤ 459*(FetchSetup.size input)^2+695*FetchSetup.size input+246 := by
  have validLeft : ([InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right][(1 : Fin 3).val]).val<(List.ofFn state.reg).length := by simp [InstructionCodec.registerWord]
  obtain ⟨leftTicks,leftPeak,readingLeft,leftBound,_⟩ := RegisterLoad.execution input
    [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right] (List.ofFn state.reg) 1 (by simp) validLeft (ready.first input state bound dst left right)
  have leftValue : (List.ofFn state.reg)[(InstructionCodec.registerWord bound left).val]=state.reg left := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (RegisterLoad.program 1) _ ⟨none,RegisterLoad.output input (InstructionCodec.registerWord bound left) ((List.ofFn state.reg)[(InstructionCodec.registerWord bound left).val])⟩ _ _ at readingLeft
  rw [leftValue] at readingLeft
  obtain ⟨movePeak,moving⟩ := WordMove.execution (first input state bound left) (some 27) (some 28) (some 2)
    (by decide) (by decide) (by decide) (by simpa [first,RegisterLoad.output,RegisterRead.addressed] using ready.clear (some 2) (by simp [FieldSet.work]))
  simp only [first,RegisterLoad.output,Function.update_self,RegisterRead.addressed,
    Function.update_of_ne (show (some 28 : Port) ≠ some 27 by decide),Function.update_of_ne (show (some 28 : Port) ≠ some 3 by decide),
    ready.bufferEmpty,List.append_nil,Encoding.bits_length] at moving
  have validRight : ([InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right][(2 : Fin 3).val]).val<(List.ofFn state.reg).length := by simp [InstructionCodec.registerWord]
  obtain ⟨rightTicks,rightPeak,readingRight,rightBound,_⟩ := RegisterLoad.execution (parked input state bound left)
    [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right] (List.ofFn state.reg) 2 (by simp) validRight (ready.second input state bound dst left right)
  have rightValue : (List.ofFn state.reg)[(InstructionCodec.registerWord bound right).val]=state.reg right := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (RegisterLoad.program 2) _ ⟨none,RegisterLoad.output (parked input state bound left) (InstructionCodec.registerWord bound right) ((List.ofFn state.reg)[(InstructionCodec.registerWord bound right).val])⟩ _ _ at readingRight
  rw [rightValue] at readingRight
  have trace := (readingLeft.link moving).link readingRight
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have parkedBound : FetchSetup.size (parked input state bound left) ≤ 4*FetchSetup.size input := by have a := size_parked input state bound left; omega
  have product := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_left parkedBound 2)
  have identity : 27*(4*FetchSetup.size input)^2+138*(4*FetchSetup.size input)+121=
      432*(FetchSetup.size input)^2+552*FetchSetup.size input+121 := by ring
  have rightTime : rightTicks ≤ 432*(FetchSetup.size input)^2+552*FetchSetup.size input+121 := by rw [← identity]; omega
  have timeBound : (leftTicks+(4*width+4))+rightTicks ≤ 459*(FetchSetup.size input)^2+694*FetchSetup.size input+246 := by omega
  have space := trace.peak_le
  change max (max leftPeak movePeak) rightPeak ≤ FetchSetup.size input+((leftTicks+(4*width+4))+rightTicks) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem canonical_card : Fintype.card Label=548 := by
  have split : Fintype.card Label=(Fintype.card CopyBody.SourceLabel+(4+4))+Fintype.card CopyBody.SourceLabel := by
    change Fintype.card ((CopyBody.SourceLabel ⊕ (Fin 4 ⊕ Fin 4)) ⊕ CopyBody.SourceLabel)=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [CopyBody.source_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 4932 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.ArithmeticOperands
