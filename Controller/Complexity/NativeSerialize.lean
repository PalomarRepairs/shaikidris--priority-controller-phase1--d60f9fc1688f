module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeEnvelope

@[expose] public section

/-! A fixed physical serializer clears its output and scratch banks, then
copies the six native packets in reverse packet order. The output is exactly
the canonical encoded state, while every persistent native packet is retained. -/
namespace Controller.Complexity.NativeSerialize
open StackMachine WordReader
open scoped BigOperators

def field (index : Fin 6) : Fin 31 := ⟨21+index.val,by omega⟩
def ports (index : Fin 6) : Option Bool ↪ Port := StackFrames.threePorts (some (field index)) none (some 2)
  (by simp) (by intro equal; have h := congrArg Fin.val (Option.some.inj equal); dsimp [field] at h; omega) (by simp)
theorem ports_apply (index : Fin 6) (port : Option Bool) : ports index port=
    (match port with | none => some (field index) | some false => none | some true => some 2) := rfl

def CopyLabel : Type := Fin 4 ⊕ Fin 6
instance copyFintype : Fintype CopyLabel := inferInstanceAs (Fintype (Fin 4 ⊕ Fin 6))
def copyProgram (index : Fin 6) : Program (Fin 31) CopyLabel := StackFrames.relocate (ports index) StackCopy.program
def copied (input : Port → List Bool) (index : Fin 6) := Function.update input none (input (some (field index))++input none)
def cleared (input : Port → List Bool) := Function.update (Function.update input none []) (some 2) []
def output (input : Port → List Bool) := Function.update (cleared input) none (StateNative.storedBytes input)

def clearProgram : Program (Fin 31) (Fin 2 ⊕ Fin 2) := link (StackClear.program none) (StackClear.program (some 2))
def prefix5 := link clearProgram (copyProgram 5)
def prefix4 := link prefix5 (copyProgram 4)
def prefix3 := link prefix4 (copyProgram 3)
def prefix2 := link prefix3 (copyProgram 2)
def prefix1 := link prefix2 (copyProgram 1)
def Label : Type := ((((((Fin 2 ⊕ Fin 2) ⊕ CopyLabel) ⊕ CopyLabel) ⊕ CopyLabel) ⊕ CopyLabel) ⊕ CopyLabel) ⊕ CopyLabel
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (((((((Fin 2 ⊕ Fin 2) ⊕ CopyLabel) ⊕ CopyLabel) ⊕ CopyLabel) ⊕ CopyLabel) ⊕ CopyLabel) ⊕ CopyLabel))
def program : Program (Fin 31) Label := link prefix1 (copyProgram 0)

theorem copy_execution (input : Port → List Bool) (index : Fin 6) (clean : input (some 2)=[]) :
    ∃ peak, Execution (copyProgram index) ⟨some (copyProgram index).main,input⟩ ⟨none,copied input index⟩
      (5*(input (some (field index))).length+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution (ports index) input (by simpa only [ports_apply] using clean)
  exact ⟨peak,trace⟩

theorem clear_execution (input : Port → List Bool) :
    ∃ peak, Execution clearProgram ⟨some clearProgram.main,input⟩ ⟨none,cleared input⟩
      ((input none).length+(input (some 2)).length+4) peak := by
  obtain ⟨a,first⟩ := StackClear.ready_execution input none
  obtain ⟨b,second⟩ := StackClear.ready_execution (Function.update input none []) (some 2)
  simp only [Function.update_of_ne (by decide : (some 2 : Port) ≠ none)] at second
  have trace := first.link second
  have time : (input none).length+2+((input (some 2)).length+2)=(input none).length+(input (some 2)).length+4 := by omega
  rw [time] at trace
  exact ⟨_,trace⟩

theorem source_mass (input : Port → List Bool) :
    (StateNative.storedBytes input).length+(input none).length+(input (some 2)).length ≤ FetchSetup.size input := by
  have first := NativeReset.clear_mass input none
  have second := NativeReset.clear_mass (Function.update input none []) (some 2)
  simp only [Function.update_of_ne (by decide : (some 2 : Port) ≠ none)] at second
  have persistent := NativeReset.output_size (cleared input)
  rw [NativeEnvelope.packet_sum] at persistent
  simp [cleared] at persistent
  simp only [StateNative.storedBytes,List.length_append]
  change FetchSetup.size (cleared input)+(input (some 2)).length=FetchSetup.size (Function.update input none []) at second
  dsimp only [cleared] at *
  omega

theorem execution (input : Port → List Bool) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input⟩ ticks peak ∧
      ticks=(input none).length+(input (some 2)).length+5*(StateNative.storedBytes input).length+28 ∧
      ticks ≤ 5*FetchSetup.size input+28 ∧ peak ≤ 6*FetchSetup.size input+28 := by
  let a := copied (cleared input) 5
  let b := copied a 4
  let c := copied b 3
  let d := copied c 2
  let e := copied d 1
  obtain ⟨p0,clearing⟩ := clear_execution input
  obtain ⟨p5,five⟩ := copy_execution (cleared input) 5 (by simp [cleared])
  obtain ⟨p4,four⟩ := copy_execution a 4 (by simp [a,copied,cleared])
  obtain ⟨p3,three⟩ := copy_execution b 3 (by simp [b,a,copied,cleared])
  obtain ⟨p2,two⟩ := copy_execution c 2 (by simp [c,b,a,copied,cleared])
  obtain ⟨p1,one⟩ := copy_execution d 1 (by simp [d,c,b,a,copied,cleared])
  obtain ⟨p,zero⟩ := copy_execution e 0 (by simp [e,d,c,b,a,copied,cleared])
  have trace := (((((clearing.link five).link four).link three).link two).link one).link zero
  have finish : copied e 0=output input := by
    funext port
    by_cases empty : port=none <;> by_cases scratch : port=some 2 <;>
      simp_all [e,d,c,b,a,copied,cleared,output,field,StateNative.storedBytes]
  rw [finish] at trace
  have time : ((input none).length+(input (some 2)).length+4)+
      (5*((cleared input) (some (field 5))).length+4)+
      (5*(a (some (field 4))).length+4)+(5*(b (some (field 3))).length+4)+
      (5*(c (some (field 2))).length+4)+(5*(d (some (field 1))).length+4)+(5*(e (some (field 0))).length+4)=
      (input none).length+(input (some 2)).length+5*(StateNative.storedBytes input).length+28 := by
    simp [e,d,c,b,a,copied,cleared,field,StateNative.storedBytes,List.length_append]
    omega
  rw [time] at trace
  have mass := source_mass input
  have space := trace.peak_le
  change _ ≤ FetchSetup.size input+_ at space
  exact ⟨_,_,trace,rfl,by omega,by omega⟩

theorem canonical_output (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (stored : NativeStore.Stored input state) : output input none=MachineBridge.encodeState state := by
  simpa [output] using stored.bytes input state

theorem stored (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (r : NativeStore.Stored input state) : NativeStore.Stored (output input) state :=
  ((r.update_other input state none [] (by decide)).update_other _ state (some 2) [] (by decide)).update_other _ state none (StateNative.storedBytes input) (by decide)

theorem canonical_card : Fintype.card Label=64 := by decide

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 576 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeSerialize
