module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OperandLoad
public import Controller.Complexity.RegisterWrite

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A constant instruction executes both fetched operand loads, the actual
register update and modular PC advancement. The final physical packets decode
to exactly the native transition, with polynomial original-storage resources. -/
namespace Controller.Complexity.ConstantBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (dst : Fin registers) (value : Controller.Cost.Word width) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound dst,value]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def loaded (input : Port → List Bool) (bound : registers ≤ 2^width) (dst : Fin registers) (value : Controller.Cost.Word width) :=
  OperandLoad.output (OperandLoad.output input true value) false (InstructionCodec.registerWord bound dst)

def written (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (dst : Fin registers) (value : Controller.Cost.Word width) :=
  RegisterWrite.output (loaded input bound dst value) state dst value

def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (dst : Fin registers) (value : Controller.Cost.Word width) :=
  PcAdvance.output (written input state bound dst value) state.pc

def OperandLabel : Type := StateReader.LabelsOf (OperandLoad.program 0 false)
instance operandFintype : Fintype OperandLabel := inferInstanceAs (Fintype (StateReader.LabelsOf (OperandLoad.program 0 false)))
def WriterLabel : Type := StateReader.LabelsOf RegisterWrite.program
instance writerFintype : Fintype WriterLabel := inferInstanceAs (Fintype (StateReader.LabelsOf RegisterWrite.program))
def valueProgram : Program (Fin 31) OperandLabel := OperandLoad.program 1 true
def indexProgram : Program (Fin 31) OperandLabel := OperandLoad.program 0 false
def writerProgram : Program (Fin 31) WriterLabel := RegisterWrite.program
def Label : Type := ((OperandLabel ⊕ OperandLabel) ⊕ WriterLabel) ⊕ PcAdvance.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (((OperandLabel ⊕ OperandLabel) ⊕ WriterLabel) ⊕ PcAdvance.Label))
def program : Program (Fin 31) Label := link (link (link valueProgram indexProgram) writerProgram) PcAdvance.program

theorem Ready.first (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    OperandLoad.Ready input [InstructionCodec.registerWord bound dst,value] where
  payload := ready.payload
  stored := ready.stored.widthStored
  clear := ready.clear

theorem Ready.second (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    OperandLoad.Ready (OperandLoad.output input true value) [InstructionCodec.registerWord bound dst,value] where
  payload := by rw [OperandLoad.payload_output]; exact ready.payload
  stored := by simpa [OperandLoad.output,OperandLoad.destination] using ready.stored.widthStored
  clear := OperandLoad.clear_output input true value ready.clear

theorem Ready.write (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    RegisterWrite.Ready (loaded input bound dst value) state bound dst value where
  stored := OperandLoad.stored_output _ false _ state (OperandLoad.stored_output input true value state ready.stored)
  indexStored := by simp [loaded,OperandLoad.output,OperandLoad.destination,InstructionCodec.registerWord]
  valueStored := by simp [loaded,OperandLoad.output,OperandLoad.destination]
  clear := OperandLoad.clear_output _ false _ (OperandLoad.clear_output input true value ready.clear)

theorem Ready.pc (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    PcAdvance.Ready (written input state bound dst value) state.pc where
  stored := by simpa [written,RegisterWrite.output,RegisterWrite.cleared,loaded,OperandLoad.output,OperandLoad.destination] using ready.stored.widthStored
  pcStored := by simpa [written,RegisterWrite.output,RegisterWrite.cleared,loaded,OperandLoad.output,OperandLoad.destination,FieldGet.field] using ready.stored.pcStored
  indexEmpty := by simp [written,RegisterWrite.output,RegisterWrite.cleared]
  valueEmpty := by simp [written,RegisterWrite.output,RegisterWrite.cleared]
  clear := by
    intro port member
    have indexOutside : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have valueOutside : port ≠ (some 27 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    have registerOutside : port ≠ (some 21 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa [written,RegisterWrite.output,RegisterWrite.cleared,loaded,OperandLoad.output,OperandLoad.destination,
      indexOutside,valueOutside,registerOutside]
      using ready.clear port member

theorem stored_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    NativeStore.Stored (output input state bound dst value) (state.put dst value).advance := by
  have store := (ready.write input state bound dst value).stored
  have writing := RegisterWrite.stored_output (loaded input bound dst value) state dst value store
  exact writing.advance (written input state bound dst value) (state.put dst value)

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    StateNative.observe width registers (output input state bound dst value)=Controller.Cost.step (.constant dst value) state := by
  have same : (state.put dst value).advance=state.advance.put dst value := rfl
  rw [(stored_output input state bound dst value ready).observation, same]
  simp [Controller.Cost.step,ready.running]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst : Fin registers) (value : Controller.Cost.Word width) (ready : Ready input state bound dst value) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state bound dst value⟩ ticks peak ∧
      ticks ≤ 279*(FetchSetup.size input)^2+527*FetchSetup.size input+411 ∧
      peak ≤ 279*(FetchSetup.size input)^2+528*FetchSetup.size input+411 := by
  obtain ⟨valueTicks,valuePeak,valuing,valueBound,_⟩ := OperandLoad.execution input [InstructionCodec.registerWord bound dst,value] 1 true (by simp) (ready.first input state bound dst value)
  obtain ⟨indexTicks,indexPeak,indexing,indexBound,_⟩ := OperandLoad.execution (OperandLoad.output input true value)
    [InstructionCodec.registerWord bound dst,value] 0 false (by simp) (ready.second input state bound dst value)
  obtain ⟨writeTicks,writePeak,writing,writeBound,_⟩ := RegisterWrite.execution (loaded input bound dst value) state bound dst value (ready.write input state bound dst value)
  obtain ⟨pcTicks,pcPeak,advancing,pcBound,_⟩ := PcAdvance.execution (written input state bound dst value) state.pc (ready.pc input state bound dst value)
  have trace := ((valuing.link indexing).link writing).link advancing
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have firstMass := OperandLoad.update_size_le input (some 27) (Encoding.bits width value.val)
  simp only [Encoding.bits_length] at firstMass
  change FetchSetup.size (OperandLoad.output input true value) ≤ FetchSetup.size input+width at firstMass
  have nextMass := OperandLoad.update_size_le (OperandLoad.output input true value) (some 3) (Encoding.bits width dst.val)
  simp only [Encoding.bits_length] at nextMass
  change FetchSetup.size (loaded input bound dst value) ≤ FetchSetup.size (OperandLoad.output input true value)+width at nextMass
  have massBound : FetchSetup.size (loaded input bound dst value) ≤ 3*FetchSetup.size input := by omega
  have squareBound := Nat.pow_le_pow_left massBound 2
  have product := Nat.mul_le_mul_left 31 squareBound
  have identity : 31*(3*FetchSetup.size input)^2+90*(3*FetchSetup.size input)+78=
      279*(FetchSetup.size input)^2+270*FetchSetup.size input+78 := by ring
  have writeTime : writeTicks ≤ 279*(FetchSetup.size input)^2+270*FetchSetup.size input+78 := by rw [← identity]; omega
  have timeBound : ((valueTicks+indexTicks)+writeTicks)+pcTicks ≤ 279*(FetchSetup.size input)^2+527*FetchSetup.size input+411 := by omega
  have space := trace.peak_le
  change max (max (max valuePeak indexPeak) writePeak) pcPeak ≤ FetchSetup.size input+(((valueTicks+indexTicks)+writeTicks)+pcTicks) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem operand_card : Fintype.card OperandLabel=88 := by
  have original : Fintype.card (StateReader.LabelsOf (OperandLoad.program 0 false))=88 := OperandLoad.canonical_card
  have same : Fintype.card OperandLabel=Fintype.card (StateReader.LabelsOf (OperandLoad.program 0 false)) :=
    @Fintype.card_congr OperandLabel (StateReader.LabelsOf (OperandLoad.program 0 false)) _ _ (Equiv.refl _)
  exact same.trans original

theorem writer_card : Fintype.card WriterLabel=210 := by
  have original : Fintype.card (StateReader.LabelsOf RegisterWrite.program)=210 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,PcAdvance.setter_card,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card WriterLabel=Fintype.card (StateReader.LabelsOf RegisterWrite.program) :=
    @Fintype.card_congr WriterLabel (StateReader.LabelsOf RegisterWrite.program) _ _ (Equiv.refl _)
  exact same.trans original

theorem canonical_card : Fintype.card Label=785 := by
  have split : Fintype.card Label=(Fintype.card OperandLabel+Fintype.card OperandLabel)+Fintype.card WriterLabel+Fintype.card PcAdvance.Label := by
    change Fintype.card (((OperandLabel ⊕ OperandLabel) ⊕ WriterLabel) ⊕ PcAdvance.Label)=_
    simp only [Fintype.card_sum]
  rw [operand_card,writer_card,PcAdvance.canonical_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 7065 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.ConstantBody
