module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeBody

@[expose] public section

/-! One fixed machine consumes the fetched opcode, executes its native body
and erases the fetched payload, arity and tag banks. Its budget counts all
physical banks, including the retained input, program and output packets. -/
namespace Controller.Complexity.NativeDispatch
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    extends NativeBody.Ready input state bound instruction where
  tagStored : input (some 13)=(Encoding.bits 4 (BodyTable.nativeTag bound instruction).val).reverse

def bodyInput (input : Port → List Bool) := Function.update input (some 13) []
def cleaned (input : Port → List Bool) :=
  Function.update (Function.update (Function.update input (some 11) []) (some 12) []) (some 13) []
def output (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers) :=
  cleaned (NativeBody.output (bodyInput input) state bound instruction)

def cleanup : Program (Fin 31) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) :=
  link (link (StackClear.program (some 11)) (StackClear.program (some 12))) (StackClear.program (some 13))
def Label : Type := BodyTable.Label ⊕ ((Fin 2 ⊕ Fin 2) ⊕ Fin 2)
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (BodyTable.Label ⊕ ((Fin 2 ⊕ Fin 2) ⊕ Fin 2)))
def program : Program (Fin 31) Label := link BodyTable.program cleanup

theorem Ready.body (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (r : Ready input state bound instruction) : NativeBody.Ready (bodyInput input) state bound instruction where
  stored := r.stored.update_other input state (some 13) [] (by decide)
  running := r.running
  payload := by simpa [bodyInput] using r.payload
  indexStored := by simpa [bodyInput] using r.indexStored
  valueEmpty := by simpa [bodyInput] using r.valueEmpty
  bufferEmpty := by simpa [bodyInput] using r.bufferEmpty
  resultEmpty := by simpa [bodyInput] using r.resultEmpty
  clear := by
    intro port member
    have outside : port ≠ (some 13 : Port) := by intro equal; subst port; simp [FieldSet.work] at member
    simpa only [bodyInput,Function.update_of_ne outside] using r.clear port member

theorem cleanup_execution (input : Port → List Bool) :
    ∃ peak, Execution cleanup ⟨some cleanup.main,input⟩ ⟨none,cleaned input⟩
      ((input (some 11)).length+(input (some 12)).length+(input (some 13)).length+6) peak := by
  obtain ⟨a,first⟩ := StackClear.ready_execution input (some 11)
  obtain ⟨b,second⟩ := StackClear.ready_execution (Function.update input (some 11) []) (some 12)
  obtain ⟨c,third⟩ := StackClear.ready_execution (Function.update (Function.update input (some 11) []) (some 12) []) (some 13)
  simp only [Function.update_of_ne (by decide : (some 12 : Port) ≠ some 11)] at second
  simp only [Function.update_of_ne (by decide : (some 13 : Port) ≠ some 12),
    Function.update_of_ne (by decide : (some 13 : Port) ≠ some 11)] at third
  have trace := (first.link second).link third
  have time : ((input (some 11)).length+2+((input (some 12)).length+2))+((input (some 13)).length+2)=
      (input (some 11)).length+(input (some 12)).length+(input (some 13)).length+6 := by omega
  rw [time] at trace
  exact ⟨_,trace⟩

theorem cleaned_observation (input : Port → List Bool) (width registers : Nat) :
    LoadBody.observation width registers (cleaned input)=LoadBody.observation width registers input := by
  simp [LoadBody.observation,StateNative.observe,StateNative.storedBytes,cleaned]

theorem semantics (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (r : Ready input state bound instruction) :
    LoadBody.observation width registers (output input state bound instruction)=Controller.Cost.step instruction state := by
  rw [output,cleaned_observation]
  exact NativeBody.semantics (bodyInput input) state bound instruction (r.body input state bound instruction)

theorem fields_clear (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers) :
    output input state bound instruction (some 11)=[] ∧
    output input state bound instruction (some 12)=[] ∧
    output input state bound instruction (some 13)=[] := by simp [output,cleaned]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instruction : Controller.Cost.Instruction width registers)
    (r : Ready input state bound instruction) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state bound instruction⟩ ticks peak ∧
      ticks ≤ 12000*(FetchSetup.size input)^2+10003*FetchSetup.size input+4010 ∧
      peak ≤ 12000*(FetchSetup.size input)^2+10004*FetchSetup.size input+4010 := by
  obtain ⟨ticks,peak,body,bodyTime⟩ := NativeBody.execution (bodyInput input) state bound instruction (r.body input state bound instruction)
  obtain ⟨dispatchPeak,dispatch,_⟩ := BodyTable.execution input (NativeBody.output (bodyInput input) state bound instruction)
    (BodyTable.nativeTag bound instruction) r.tagStored body
  obtain ⟨cleanupPeak,clearing⟩ := cleanup_execution (NativeBody.output (bodyInput input) state bound instruction)
  have trace := dispatch.link clearing
  have mass : FetchSetup.size (bodyInput input) ≤ FetchSetup.size input := by
    simpa only [bodyInput,List.length_nil,Nat.add_zero] using OperandLoad.update_size_le input (some 13) []
  have finalMass := body.final_live_le.trans body.peak_le
  change FetchSetup.size (NativeBody.output (bodyInput input) state bound instruction) ≤ FetchSetup.size (bodyInput input)+ticks at finalMass
  have cell (port : Port) : (NativeBody.output (bodyInput input) state bound instruction port).length ≤
      FetchSetup.size (bodyInput input)+ticks :=
    (Finset.single_le_sum (f := fun address : Port => (NativeBody.output (bodyInput input) state bound instruction address).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)).trans finalMass
  have a := cell (some 11)
  have b := cell (some 12)
  have c := cell (some 13)
  have squared : (FetchSetup.size (bodyInput input))^2 ≤ (FetchSetup.size input)^2 := Nat.pow_le_pow_left mass 2
  have timeBound : 4+ticks+((NativeBody.output (bodyInput input) state bound instruction (some 11)).length+
      (NativeBody.output (bodyInput input) state bound instruction (some 12)).length+
      (NativeBody.output (bodyInput input) state bound instruction (some 13)).length+6) ≤
      12000*(FetchSetup.size input)^2+10003*FetchSetup.size input+4010 := by omega
  have space := trace.peak_le
  change _ ≤ FetchSetup.size input+_ at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem canonical_card : Fintype.card Label=11617 := by
  change Fintype.card (BodyTable.Label ⊕ ((Fin 2 ⊕ Fin 2) ⊕ Fin 2))=_
  simp only [Fintype.card_sum,Fintype.card_fin,BodyTable.canonical_card,Nat.reduceAdd]

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 104553 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeDispatch
