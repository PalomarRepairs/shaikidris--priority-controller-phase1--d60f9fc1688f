module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.HeapWrite
public import Controller.Complexity.ArithmeticOperands

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Store prepares its old source value before reading its old address
register. Parking preserves that value across the second register read;
the final operand banks contain the heap address and stored word. -/
namespace Controller.Complexity.StoreOperands
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (address src : Fin registers) : Prop where
  stored : NativeStore.Stored input state
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound address,InstructionCodec.registerWord bound src]
  clear : ∀ port ∈ FieldSet.work, input port=[]
  bufferEmpty : input (some 28)=[]

def parked := @ArithmeticOperands.parked
def addressed (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (address src : Fin registers) :=
  IndirectAddress.output (parked input state bound src) (state.reg address)
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers) :=
  Function.update (Function.update (Function.update input (some 3) (Encoding.bits width (state.reg address).val))
    (some 27) (Encoding.bits width (state.reg src).val)) (some 28) []

def Label : Type := ((CopyBody.SourceLabel ⊕ (Fin 4 ⊕ Fin 4)) ⊕ IndirectAddress.Label) ⊕ (Fin 4 ⊕ Fin 4)
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (((CopyBody.SourceLabel ⊕ (Fin 4 ⊕ Fin 4)) ⊕ IndirectAddress.Label) ⊕ (Fin 4 ⊕ Fin 4)))
def program : Program (Fin 31) Label := link (link (link CopyBody.sourceProgram
  (WordMove.program (some 27) (some 28) (some 2))) (IndirectAddress.program 0)) (WordMove.program (some 28) (some 27) (some 2))

theorem Ready.source (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (address src : Fin registers) (ready : Ready input state bound address src) :
    RegisterRead.Ready input [InstructionCodec.registerWord bound address,InstructionCodec.registerWord bound src] (List.ofFn state.reg) where
  payload := ready.payload
  stored := ready.stored.widthStored
  registersStored := by simpa [FieldGet.field] using ready.stored.registersStored
  clear := ready.clear

theorem Ready.address (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (address src : Fin registers) (ready : Ready input state bound address src) :
    RegisterRead.Ready (parked input state bound src) [InstructionCodec.registerWord bound address,InstructionCodec.registerWord bound src] (List.ofFn state.reg) where
  payload := by simpa [parked,ArithmeticOperands.parked,ArithmeticOperands.first,RegisterLoad.output,RegisterRead.addressed] using ready.payload
  stored := (ArithmeticOperands.parked_stored input state bound src ready.stored).widthStored
  registersStored := by simpa [parked,FieldGet.field] using (ArithmeticOperands.parked_stored input state bound src ready.stored).registersStored
  clear := ArithmeticOperands.parked_clear input state bound src ready.clear

theorem stored_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers)
    (stored : NativeStore.Stored input state) : NativeStore.Stored (output input state address src) state :=
  ((stored.update_other input state (some 3) _ (by decide)).update_other _ state (some 27) _ (by decide)).update_other _ state (some 28) [] (by decide)

theorem clear_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers)
    (clean : ∀ port ∈ FieldSet.work, input port=[]) : ∀ port ∈ FieldSet.work, output input state address src port=[] := by
  intro port member
  have h3 : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  have h27 : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  have h28 : port ≠ (some 28 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
  simpa [output,h3,h27,h28] using clean port member

theorem heap_ready (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers)
    (stored : NativeStore.Stored input state) (clean : ∀ port ∈ FieldSet.work, input port=[]) :
    HeapWrite.Ready (output input state address src) state (state.reg address) (state.reg src) where
  stored := stored_output input state address src stored
  indexStored := by simp [output]
  valueStored := by simp [output]
  clear := clear_output input state address src clean

theorem size_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (address src : Fin registers) :
    FetchSetup.size (output input state address src) ≤ FetchSetup.size input+2*width := by
  have a := OperandLoad.update_size_le input (some 3) (Encoding.bits width (state.reg address).val)
  have b := OperandLoad.update_size_le (Function.update input (some 3) (Encoding.bits width (state.reg address).val)) (some 27) (Encoding.bits width (state.reg src).val)
  have c := OperandLoad.update_size_le (Function.update (Function.update input (some 3) (Encoding.bits width (state.reg address).val)) (some 27) (Encoding.bits width (state.reg src).val)) (some 28) []
  simp only [Encoding.bits_length,List.length_nil,Nat.add_zero] at a b c
  change FetchSetup.size (output input state address src) ≤ _ at c
  omega

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (address src : Fin registers) (ready : Ready input state bound address src) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state address src⟩ ticks peak ∧
      ticks ≤ 459*(FetchSetup.size input)^2+718*FetchSetup.size input+256 ∧
      peak ≤ 459*(FetchSetup.size input)^2+719*FetchSetup.size input+256 := by
  have validSource : ([InstructionCodec.registerWord bound address,InstructionCodec.registerWord bound src][(1 : Fin 3).val]).val<(List.ofFn state.reg).length := by simp [InstructionCodec.registerWord]
  obtain ⟨sourceTicks,sourcePeak,sourcing,sourceBound,_⟩ := RegisterLoad.execution input
    [InstructionCodec.registerWord bound address,InstructionCodec.registerWord bound src] (List.ofFn state.reg) 1 (by simp) validSource (ready.source input state bound address src)
  have sourceValue : (List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val]=state.reg src := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (RegisterLoad.program 1) _ ⟨none,RegisterLoad.output input (InstructionCodec.registerWord bound src) ((List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val])⟩ _ _ at sourcing
  rw [sourceValue] at sourcing
  obtain ⟨parkPeak,parking⟩ := WordMove.execution (ArithmeticOperands.first input state bound src) (some 27) (some 28) (some 2)
    (by decide) (by decide) (by decide) (by simpa [ArithmeticOperands.first,RegisterLoad.output,RegisterRead.addressed] using ready.clear (some 2) (by simp [FieldSet.work]))
  simp only [ArithmeticOperands.first,RegisterLoad.output,Function.update_self,RegisterRead.addressed,
    Function.update_of_ne (show (some 28 : Port) ≠ some 27 by decide),Function.update_of_ne (show (some 28 : Port) ≠ some 3 by decide),
    ready.bufferEmpty,List.append_nil,Encoding.bits_length] at parking
  have validAddress : ([InstructionCodec.registerWord bound address,InstructionCodec.registerWord bound src][(0 : Fin 3).val]).val<(List.ofFn state.reg).length := by simp [InstructionCodec.registerWord]
  obtain ⟨addressTicks,addressPeak,addressing,addressBound,_⟩ := IndirectAddress.execution (parked input state bound src)
    [InstructionCodec.registerWord bound address,InstructionCodec.registerWord bound src] (List.ofFn state.reg) 0 (by simp) validAddress (ready.address input state bound address src)
  have addressValue : (List.ofFn state.reg)[(InstructionCodec.registerWord bound address).val]=state.reg address := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (IndirectAddress.program 0) _ ⟨none,IndirectAddress.output (parked input state bound src) ((List.ofFn state.reg)[(InstructionCodec.registerWord bound address).val])⟩ _ _ at addressing
  rw [addressValue] at addressing
  obtain ⟨movePeak,moving⟩ := WordMove.execution (addressed input state bound address src) (some 28) (some 27) (some 2)
    (by decide) (by decide) (by decide) (by
      simpa [addressed,IndirectAddress.output,parked,ArithmeticOperands.parked,ArithmeticOperands.first,RegisterLoad.output,RegisterRead.addressed] using ready.clear (some 2) (by simp [FieldSet.work]))
  have buffer : addressed input state bound address src (some 28)=Encoding.bits width (state.reg src).val := by
    simp [addressed,IndirectAddress.output,parked,ArithmeticOperands.parked]
  have empty : addressed input state bound address src (some 27)=[] := by simp [addressed,IndirectAddress.output]
  rw [buffer,empty,List.append_nil,Encoding.bits_length] at moving
  have final : Function.update (Function.update (addressed input state bound address src) (some 28) []) (some 27) (Encoding.bits width (state.reg src).val)=output input state address src := by
    funext port
    by_cases h3 : port=some 3 <;> by_cases h27 : port=some 27 <;> by_cases h28 : port=some 28 <;>
      simp_all [addressed,IndirectAddress.output,parked,ArithmeticOperands.parked,ArithmeticOperands.first,RegisterLoad.output,RegisterRead.addressed,output]
  rw [final] at moving
  have trace := ((sourcing.link parking).link addressing).link moving
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun port : Port => (input port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have parkedBound : FetchSetup.size (parked input state bound src) ≤ 4*FetchSetup.size input := by have a := ArithmeticOperands.size_parked input state bound src; change FetchSetup.size (parked input state bound src) ≤ _ at a; omega
  have product := Nat.mul_le_mul_left 27 (Nat.pow_le_pow_left parkedBound 2)
  have identity : 27*(4*FetchSetup.size input)^2+143*(4*FetchSetup.size input)+127=
      432*(FetchSetup.size input)^2+572*FetchSetup.size input+127 := by ring
  have addressTime : addressTicks ≤ 432*(FetchSetup.size input)^2+572*FetchSetup.size input+127 := by rw [← identity]; omega
  have timeBound : ((sourceTicks+(4*width+4))+addressTicks)+(4*width+4) ≤ 459*(FetchSetup.size input)^2+718*FetchSetup.size input+256 := by omega
  have space := trace.peak_le
  exact ⟨_,_,trace,timeBound,by change _ ≤ FetchSetup.size input+_ at space; omega⟩

theorem canonical_card : Fintype.card Label=566 := by
  have split : Fintype.card Label=((Fintype.card CopyBody.SourceLabel+(4+4))+Fintype.card IndirectAddress.Label)+(4+4) := by
    change Fintype.card (((CopyBody.SourceLabel ⊕ (Fin 4 ⊕ Fin 4)) ⊕ IndirectAddress.Label) ⊕ (Fin 4 ⊕ Fin 4))=_
    simp only [Fintype.card_sum,Fintype.card_fin]
  rw [CopyBody.source_card,IndirectAddress.canonical_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 5094 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.StoreOperands
