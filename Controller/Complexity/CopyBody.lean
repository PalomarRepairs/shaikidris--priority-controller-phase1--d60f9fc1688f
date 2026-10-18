module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.RegisterLoad
public import Controller.Complexity.RegisterWrite
public import Controller.Complexity.ConstantBody

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The native copy body reads the fetched source operand, loads its actual
register value, obtains the fetched destination and executes register/PC
commit. Source/destination aliasing uses the old register value. -/
namespace Controller.Complexity.CopyBody
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (dst src : Fin registers) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  payload : input (some 11)=Encoding.wordList width [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound src]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def sourceLoaded (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (src : Fin registers) :=
  RegisterLoad.output input (InstructionCodec.registerWord bound src) (state.reg src)
def loaded (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (dst src : Fin registers) :=
  OperandLoad.output (sourceLoaded input state bound src) false (InstructionCodec.registerWord bound dst)
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width) (dst src : Fin registers) :=
  RegisterWrite.completeOutput (loaded input state bound dst src) state dst (state.reg src)

def SourceLabel : Type := StateReader.LabelsOf (RegisterLoad.program 1)
instance sourceFintype : Fintype SourceLabel := inferInstanceAs (Fintype (StateReader.LabelsOf (RegisterLoad.program 1)))
def CommitLabel : Type := StateReader.LabelsOf RegisterWrite.completeProgram
instance commitFintype : Fintype CommitLabel := inferInstanceAs (Fintype (StateReader.LabelsOf RegisterWrite.completeProgram))
def sourceProgram : Program (Fin 31) SourceLabel := RegisterLoad.program 1
def indexProgram : Program (Fin 31) ConstantBody.OperandLabel := OperandLoad.program 0 false
def commitProgram : Program (Fin 31) CommitLabel := RegisterWrite.completeProgram
def Label : Type := (SourceLabel ⊕ ConstantBody.OperandLabel) ⊕ CommitLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype ((SourceLabel ⊕ ConstantBody.OperandLabel) ⊕ CommitLabel))
def program : Program (Fin 31) Label := link (link sourceProgram indexProgram) commitProgram

theorem Ready.source (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst src : Fin registers) (ready : Ready input state bound dst src) :
    RegisterRead.Ready input [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound src] (List.ofFn state.reg) where
  payload := ready.payload
  stored := ready.stored.widthStored
  registersStored := by simpa [FieldGet.field] using ready.stored.registersStored
  clear := ready.clear

theorem Ready.index (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst src : Fin registers) (ready : Ready input state bound dst src) :
    OperandLoad.Ready (sourceLoaded input state bound src) [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound src] where
  payload := by simpa [sourceLoaded,RegisterLoad.output,RegisterRead.addressed] using ready.payload
  stored := by simpa [sourceLoaded,RegisterLoad.output,RegisterRead.addressed] using ready.stored.widthStored
  clear := RegisterLoad.clear_output input _ _ ready.clear

theorem Ready.commit (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst src : Fin registers) (ready : Ready input state bound dst src) :
    RegisterWrite.Ready (loaded input state bound dst src) state bound dst (state.reg src) where
  stored := OperandLoad.stored_output _ false _ state (RegisterLoad.stored_output input _ _ state ready.stored)
  indexStored := by simp [loaded,OperandLoad.output,OperandLoad.destination,InstructionCodec.registerWord]
  valueStored := by simp [loaded,sourceLoaded,OperandLoad.output,OperandLoad.destination,RegisterLoad.output]
  clear := OperandLoad.clear_output _ false _ (RegisterLoad.clear_output input _ _ ready.clear)

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst src : Fin registers) (ready : Ready input state bound dst src) :
    StateNative.observe width registers (output input state bound dst src)=Controller.Cost.step (.copy dst src) state := by
  have stored := RegisterWrite.complete_stored (loaded input state bound dst src) state dst (state.reg src) (ready.commit input state bound dst src).stored
  rw [show output input state bound dst src=RegisterWrite.completeOutput (loaded input state bound dst src) state dst (state.reg src) from rfl,stored.observation]
  simp [Controller.Cost.step,ready.running,Controller.Cost.State.put,Controller.Cost.State.advance]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (bound : registers ≤ 2^width)
    (dst src : Fin registers) (ready : Ready input state bound dst src) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state bound dst src⟩ ticks peak ∧
      ticks ≤ 523*(FetchSetup.size input)^2+755*FetchSetup.size input+473 ∧
      peak ≤ 523*(FetchSetup.size input)^2+756*FetchSetup.size input+473 := by
  have validIndex : ([InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound src][(1 : Fin 3).val]).val<(List.ofFn state.reg).length := by
    simp [InstructionCodec.registerWord]
  obtain ⟨sourceTicks,sourcePeak,sourcing,sourceBound,_⟩ := RegisterLoad.execution input
    [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound src] (List.ofFn state.reg) 1 (by simp) validIndex (ready.source input state bound dst src)
  have sourceValue : (List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val]=state.reg src := by simp [InstructionCodec.registerWord,List.getElem_ofFn]
  change Execution (RegisterLoad.program 1) _ ⟨none,RegisterLoad.output input (InstructionCodec.registerWord bound src) ((List.ofFn state.reg)[(InstructionCodec.registerWord bound src).val])⟩ _ _ at sourcing
  rw [sourceValue] at sourcing
  obtain ⟨indexTicks,indexPeak,indexing,indexBound,_⟩ := OperandLoad.execution (sourceLoaded input state bound src)
    [InstructionCodec.registerWord bound dst,InstructionCodec.registerWord bound src] 0 false (by simp) (ready.index input state bound dst src)
  obtain ⟨commitTicks,commitPeak,committing,commitBound,_⟩ := RegisterWrite.complete_execution (loaded input state bound dst src) state bound dst (state.reg src) (ready.commit input state bound dst src)
  have trace := (sourcing.link indexing).link committing
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored.widthStored,List.length_replicate] using cell
  have firstMass := RegisterLoad.size_output input (InstructionCodec.registerWord bound src) (state.reg src)
  change FetchSetup.size (sourceLoaded input state bound src) ≤ FetchSetup.size input+2*width at firstMass
  have nextMass := OperandLoad.update_size_le (sourceLoaded input state bound src) (some 3) (Encoding.bits width dst.val)
  simp only [Encoding.bits_length] at nextMass
  change FetchSetup.size (loaded input state bound dst src) ≤ FetchSetup.size (sourceLoaded input state bound src)+width at nextMass
  have massBound : FetchSetup.size (loaded input state bound dst src) ≤ 4*FetchSetup.size input := by omega
  have product := Nat.mul_le_mul_left 31 (Nat.pow_le_pow_left massBound 2)
  have identity : 31*(4*FetchSetup.size input)^2+90*(4*FetchSetup.size input)+92*FetchSetup.size input+293=
      496*(FetchSetup.size input)^2+452*FetchSetup.size input+293 := by ring
  have commitTime : commitTicks ≤ 496*(FetchSetup.size input)^2+452*FetchSetup.size input+293 := by rw [← identity]; omega
  have timeBound : (sourceTicks+indexTicks)+commitTicks ≤ 523*(FetchSetup.size input)^2+755*FetchSetup.size input+473 := by omega
  have space := trace.peak_le
  change max (max sourcePeak indexPeak) commitPeak ≤ FetchSetup.size input+((sourceTicks+indexTicks)+commitTicks) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem source_card : Fintype.card SourceLabel=270 := by
  have original : Fintype.card (StateReader.LabelsOf (RegisterLoad.program 1))=270 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,RegisterRead.canonical_card,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card SourceLabel=Fintype.card (StateReader.LabelsOf (RegisterLoad.program 1)) :=
    @Fintype.card_congr SourceLabel (StateReader.LabelsOf (RegisterLoad.program 1)) _ _ (Equiv.refl _)
  exact same.trans original

theorem commit_card : Fintype.card CommitLabel=609 := by
  have original : Fintype.card (StateReader.LabelsOf RegisterWrite.completeProgram)=609 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,PcAdvance.setter_card,PcAdvance.canonical_card,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card CommitLabel=Fintype.card (StateReader.LabelsOf RegisterWrite.completeProgram) :=
    @Fintype.card_congr CommitLabel (StateReader.LabelsOf RegisterWrite.completeProgram) _ _ (Equiv.refl _)
  exact same.trans original

theorem canonical_card : Fintype.card Label=967 := by
  have split : Fintype.card Label=(Fintype.card SourceLabel+Fintype.card ConstantBody.OperandLabel)+Fintype.card CommitLabel := by
    change Fintype.card ((SourceLabel ⊕ ConstantBody.OperandLabel) ⊕ CommitLabel)=_
    simp only [Fintype.card_sum]
  rw [source_card,ConstantBody.operand_card,commit_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 8703 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.CopyBody
