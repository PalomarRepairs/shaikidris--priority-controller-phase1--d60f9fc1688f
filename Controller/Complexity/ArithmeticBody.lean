module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ArithmeticOperands

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Complete selected add and XOR bodies read both old source registers,
execute the binary kernel, obtain the destination from the fetched payload,
and commit the native register and PC updates. -/
namespace Controller.Complexity.ArithmeticBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (dst left right : Fin registers)
    extends ArithmeticOperands.Ready input state bound dst left right where
  running : state.halted=false
  resultEmpty : input (some 29)=[]

def result (xorMode : Bool) (state : Controller.Cost.State width registers) (left right : Fin registers) :=
  ArithmeticKernel.value xorMode (state.reg left) (state.reg right)
def calculated (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (left right : Fin registers) :=
  ArithmeticKernel.output (ArithmeticOperands.output input state bound left right) xorMode (state.reg left) (state.reg right)
def loaded (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (dst left right : Fin registers) :=
  OperandLoad.output (calculated input xorMode state bound left right) false (InstructionCodec.registerWord bound dst)
def output (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (dst left right : Fin registers) :=
  RegisterWrite.completeOutput (loaded input xorMode state bound dst left right) state dst (result xorMode state left right)
def instruction (xorMode : Bool) (dst left right : Fin registers) : Controller.Cost.Instruction width registers :=
  if xorMode then .xor dst left right else .add dst left right

def KernelLabel (xorMode : Bool) : Type := StateReader.LabelsOf (ArithmeticKernel.program xorMode)
instance kernelFintype (xorMode : Bool) : Fintype (KernelLabel xorMode) := inferInstanceAs (Fintype (StateReader.LabelsOf (ArithmeticKernel.program xorMode)))
def kernelProgram (xorMode : Bool) : Program (Fin 31) (KernelLabel xorMode) := ArithmeticKernel.program xorMode
def indexProgram : Program (Fin 31) ConstantBody.OperandLabel := OperandLoad.program 0 false
def commitProgram : Program (Fin 31) CopyBody.CommitLabel := RegisterWrite.completeProgram
def Label (xorMode : Bool) : Type := ((ArithmeticOperands.Label ⊕ KernelLabel xorMode) ⊕ ConstantBody.OperandLabel) ⊕ CopyBody.CommitLabel
instance labelFintype (xorMode : Bool) : Fintype (Label xorMode) :=
  inferInstanceAs (Fintype (((ArithmeticOperands.Label ⊕ KernelLabel xorMode) ⊕ ConstantBody.OperandLabel) ⊕ CopyBody.CommitLabel))
def program (xorMode : Bool) : Program (Fin 31) (Label xorMode) :=
  link (link (link ArithmeticOperands.program (kernelProgram xorMode)) indexProgram) commitProgram

theorem calculated_stored (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (left right : Fin registers) (stored : NativeStore.Stored input state) : NativeStore.Stored (calculated input xorMode state bound left right) state :=
  ArithmeticKernel.stored_output _ xorMode _ _ state (ArithmeticOperands.stored_output input state bound left right stored)

theorem Ready.index (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) :
    OperandLoad.Ready (calculated input xorMode state bound left right)
      [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right] where
  payload := by simpa [calculated,ArithmeticKernel.output,ArithmeticOperands.output,ArithmeticOperands.parked,ArithmeticOperands.first,
    RegisterLoad.output,RegisterRead.addressed] using ready.payload
  stored := (calculated_stored input xorMode state bound left right ready.stored).widthStored
  clear := ArithmeticKernel.clear_output _ xorMode _ _ (ArithmeticOperands.clear_output input state bound left right ready.clear)

theorem Ready.commit (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) :
    RegisterWrite.Ready (loaded input xorMode state bound dst left right) state bound dst (result xorMode state left right) where
  stored := OperandLoad.stored_output _ false _ state (calculated_stored input xorMode state bound left right ready.stored)
  indexStored := by simp [loaded,OperandLoad.output,OperandLoad.destination,InstructionCodec.registerWord]
  valueStored := by simp [loaded,OperandLoad.output,OperandLoad.destination,calculated,ArithmeticKernel.output,result]
  clear := OperandLoad.clear_output _ false _ ((ready.index input xorMode state bound dst left right).clear)

theorem native_transition (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) :
    StateNative.observe width registers (output input xorMode state bound dst left right)=Controller.Cost.step (instruction xorMode dst left right) state := by
  have stored := RegisterWrite.complete_stored (loaded input xorMode state bound dst left right) state dst (result xorMode state left right)
    (ready.commit input xorMode state bound dst left right).stored
  rw [show output input xorMode state bound dst left right=RegisterWrite.completeOutput (loaded input xorMode state bound dst left right) state dst (result xorMode state left right) from rfl,stored.observation]
  cases xorMode <;> simp [instruction,Controller.Cost.step,ready.running,Controller.Cost.State.put,Controller.Cost.State.advance,result,ArithmeticKernel.value]

theorem output_shape (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) :
    output input xorMode state bound dst left right=RegisterWrite.completeOutput input state dst (result xorMode state left right) := by
  funext address
  by_cases h3 : address=some 3 <;> by_cases h27 : address=some 27 <;> by_cases h28 : address=some 28 <;>
    by_cases h21 : address=some 21 <;> by_cases h25 : address=some 25 <;>
    simp_all [output,loaded,calculated,RegisterWrite.completeOutput,RegisterWrite.output,RegisterWrite.cleared,PcAdvance.output,
      OperandLoad.output,OperandLoad.destination,ArithmeticKernel.output,ArithmeticOperands.output,ArithmeticOperands.parked,
      ArithmeticOperands.first,RegisterLoad.output,RegisterRead.addressed,FieldGet.field,ready.bufferEmpty]

theorem execution (input : Port → List Bool) (xorMode : Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst left right : Fin registers) (ready : Ready input state bound dst left right) :
    ∃ ticks peak, Execution (program xorMode) ⟨some (program xorMode).main,input⟩ ⟨none,output input xorMode state bound dst left right⟩ ticks peak ∧
      ticks ≤ 2443*(FetchSetup.size input)^2+1904*FetchSetup.size input+610 ∧
      peak ≤ 2443*(FetchSetup.size input)^2+1905*FetchSetup.size input+610 := by
  obtain ⟨sourceTicks,sourcePeak,sourcing,sourceBound,_⟩ := ArithmeticOperands.execution input state bound dst left right ready.toReady
  obtain ⟨kernelPeak,calculating⟩ := ArithmeticKernel.execution (ArithmeticOperands.output input state bound left right) xorMode (state.reg left) (state.reg right)
    (ArithmeticOperands.kernel_ready input state bound dst left right ready.toReady ready.resultEmpty)
  obtain ⟨indexTicks,indexPeak,indexing,indexBound,_⟩ := OperandLoad.execution (calculated input xorMode state bound left right)
    [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound left,InstructionCodec.registerWord bound right] 0 false (by simp)
    (ready.index input xorMode state bound dst left right)
  obtain ⟨commitTicks,commitPeak,committing,commitBound,_⟩ := RegisterWrite.complete_execution (loaded input xorMode state bound dst left right) state bound dst (result xorMode state left right)
    (ready.commit input xorMode state bound dst left right)
  have trace := ((sourcing.link calculating).link indexing).link committing
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have gatheredMass := ArithmeticOperands.size_output input state bound left right
  have calculatedMass := ArithmeticKernel.size_output (ArithmeticOperands.output input state bound left right) xorMode (state.reg left) (state.reg right)
  change FetchSetup.size (calculated input xorMode state bound left right) ≤ FetchSetup.size (ArithmeticOperands.output input state bound left right)+width at calculatedMass
  have loadedMass := OperandLoad.update_size_le (calculated input xorMode state bound left right) (some 3) (Encoding.bits width dst.val)
  simp only [Encoding.bits_length] at loadedMass
  change FetchSetup.size (loaded input xorMode state bound dst left right) ≤ FetchSetup.size (calculated input xorMode state bound left right)+width at loadedMass
  have indexMassBound : FetchSetup.size (calculated input xorMode state bound left right) ≤ 7*FetchSetup.size input := by omega
  have commitMassBound : FetchSetup.size (loaded input xorMode state bound dst left right) ≤ 8*FetchSetup.size input := by omega
  have product := Nat.mul_le_mul_left 31 (Nat.pow_le_pow_left commitMassBound 2)
  have identity : 31*(8*FetchSetup.size input)^2+90*(8*FetchSetup.size input)+92*FetchSetup.size input+293=
      1984*(FetchSetup.size input)^2+812*FetchSetup.size input+293 := by ring
  have commitTime : commitTicks ≤ 1984*(FetchSetup.size input)^2+812*FetchSetup.size input+293 := by rw [← identity]; omega
  have timeBound : ((sourceTicks+(13*width+12))+indexTicks)+commitTicks ≤ 2443*(FetchSetup.size input)^2+1904*FetchSetup.size input+610 := by omega
  have space := trace.peak_le
  change max (max (max sourcePeak kernelPeak) indexPeak) commitPeak ≤ FetchSetup.size input+(((sourceTicks+(13*width+12))+indexTicks)+commitTicks) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem kernel_card (xorMode : Bool) : Fintype.card (KernelLabel xorMode)=(if xorMode then 27 else 33) := by
  have same : Fintype.card (KernelLabel xorMode)=Fintype.card (StateReader.LabelsOf (ArithmeticKernel.program xorMode)) :=
    @Fintype.card_congr (KernelLabel xorMode) (StateReader.LabelsOf (ArithmeticKernel.program xorMode)) _ _ (Equiv.refl _)
  exact same.trans (ArithmeticKernel.canonical_card xorMode)

theorem canonical_card (xorMode : Bool) : Fintype.card (Label xorMode)=(if xorMode then 1272 else 1278) := by
  have split : Fintype.card (Label xorMode)=((Fintype.card ArithmeticOperands.Label+Fintype.card (KernelLabel xorMode))+Fintype.card ConstantBody.OperandLabel)+Fintype.card CopyBody.CommitLabel := by
    change Fintype.card (((ArithmeticOperands.Label ⊕ KernelLabel xorMode) ⊕ ConstantBody.OperandLabel) ⊕ CopyBody.CommitLabel)=_
    simp only [Fintype.card_sum]
  rw [ArithmeticOperands.canonical_card,kernel_card,ConstantBody.operand_card,CopyBody.commit_card] at split
  cases xorMode <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.reduceAdd] at split ⊢ <;> exact split

theorem resident (xorMode : Bool) : (∑ label, statementSize (tmStatement ((program xorMode).code label))) ≤ 11502 := by
  have bound := finiteTM_resident (program xorMode)
  have cardBound : Fintype.card (Label xorMode) ≤ 1278 := by rw [canonical_card]; cases xorMode <;> decide
  exact bound.trans (by simpa only [Nat.reduceMul] using Nat.mul_le_mul_left 9 cardBound)

end Controller.Complexity.ArithmeticBody
