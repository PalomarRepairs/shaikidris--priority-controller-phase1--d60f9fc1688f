module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeStore

@[expose] public section

/-! The native halt body clears its temporary fetched index, executes modular
PC advancement and writes the actual halt bit. The resulting physical state
decodes to exactly the native halt transition, with all costs charged. -/
namespace Controller.Complexity.HaltBody
open StackMachine WordReader
open scoped BigOperators

def writeBit : Program (Fin 31) (Fin 2) where
  main := 0
  code label := if label=0 then .push (some 26) true 1 else .halt

def writeHalt := link (StackClear.program (some 26 : Port)) writeBit

theorem write_execution (input : Port → List Bool) :
    ∃ peak, Execution writeHalt ⟨some writeHalt.main,input⟩ ⟨none,NativeStore.haltedOutput input⟩ ((input (some 26)).length+4) peak := by
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution input (some 26)
  have first : step writeBit ⟨some writeBit.main,Function.update input (some 26) []⟩=
      some ⟨some 1,NativeStore.haltedOutput input⟩ := by simp [step,writeBit,instructionStep,NativeStore.haltedOutput]
  have last : step writeBit ⟨some 1,NativeStore.haltedOutput input⟩=some ⟨none,NativeStore.haltedOutput input⟩ := rfl
  have writing := Execution.cons first (Execution.cons last (Execution.refl _))
  have trace := clearing.link writing
  have ticks : ((input (some 26)).length+2)+2=(input (some 26)).length+4 := by omega
  exact ⟨_,by simpa only [writeHalt,ticks] using trace⟩

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  indexStored : input (some 3)=Encoding.bits width state.pc.val
  valueEmpty : input (some 27)=[]
  clear : ∀ port ∈ FieldSet.work, input port=[]

def cleared (input : Port → List Bool) := Function.update input (some 3) []
def output (input : Port → List Bool) (state : Controller.Cost.State width registers) :=
  NativeStore.haltedOutput (PcAdvance.output (cleared input) state.pc)

def program := link (link (StackClear.program (some 3 : Port)) PcAdvance.program) writeHalt

theorem Ready.pc (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    PcAdvance.Ready (cleared input) state.pc where
  stored := by simpa [cleared] using ready.stored.widthStored
  pcStored := by simpa [cleared,FieldGet.field] using ready.stored.pcStored
  indexEmpty := by simp [cleared]
  valueEmpty := by simpa [cleared] using ready.valueEmpty
  clear := by
    intro port member
    have outside : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa only [cleared,Function.update_of_ne outside] using ready.clear port member

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state⟩ ticks peak ∧
      ticks ≤ 93*width+222 ∧ peak ≤ FetchSetup.size input+93*width+222 := by
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution input (some 3)
  simp only [ready.indexStored,Encoding.bits_length] at clearing
  obtain ⟨pcTicks,pcPeak,advancing,pcBound,_⟩ := PcAdvance.execution (cleared input) state.pc (ready.pc input state)
  obtain ⟨writePeak,writing⟩ := write_execution (PcAdvance.output (cleared input) state.pc)
  have flagLength : (PcAdvance.output (cleared input) state.pc (some 26)).length=1 := by
    simp [PcAdvance.output,cleared,FieldGet.field,ready.stored.haltStored,ready.running]
  rw [flagLength] at writing
  have trace := (clearing.link advancing).link writing
  have timeBound : (width+2)+pcTicks+5 ≤ 93*width+222 := by omega
  have space := trace.peak_le
  change max (max clearPeak pcPeak) writePeak ≤ FetchSetup.size input+((width+2)+pcTicks+5) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem stored_output (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    NativeStore.Stored (output input state) { state.advance with halted := true } := by
  have clearedState := ready.stored.update_other input state (some 3) [] (by decide)
  have advanced := clearedState.advance (cleared input) state
  exact advanced.halted (PcAdvance.output (cleared input) state.pc) state.advance

theorem native_transition (input : Port → List Bool) (state : Controller.Cost.State width registers) (ready : Ready input state) :
    Controller.Cost.step .halt state=some { state.advance with halted := true } ∧
    StateNative.observe width registers (output input state)=some { state.advance with halted := true } := by
  constructor
  · simp [Controller.Cost.step,ready.running]
  · exact (stored_output input state ready).observation (output input state) { state.advance with halted := true }

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 3645 := by
  simpa only [Fintype.card_sum,PcAdvance.canonical_card,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.HaltBody
