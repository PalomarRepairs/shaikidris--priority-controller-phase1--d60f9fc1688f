module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativePreserve
public import Controller.Complexity.NativeEnvelope

@[expose] public section

/-! A complete instruction cycle starts from exact persistent packets and
arbitrary scratch banks. It executes reset before actual-PC fetch and dispatch.
The endpoint preserves the next native state and both program banks. -/
namespace Controller.Complexity.NativeCycle
open StackMachine WordReader
open scoped BigOperators

def Label : Type := NativeReset.Label ⊕ NativeStep.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (NativeReset.Label ⊕ NativeStep.Label))
def program : Program (Fin 31) Label := link NativeReset.program NativeStep.program
def output (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers)) :=
  NativeStep.output (NativeReset.output input) state bound instructions

theorem semantics (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (stored : NativeStore.Stored input state) (running : state.halted=false)
    (code : input (some 19)=InstructionCodec.encodeMany bound instructions)
    (count : input (some 15)=List.replicate instructions.length true) :
    LoadBody.observation width registers (output input state bound instructions)=Controller.Cost.programStep instructions.toArray state :=
  NativeStep.semantics _ state bound instructions (NativeReset.ready input state bound instructions stored running code count)

theorem stored (input : Port → List Bool) (state next : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (r : NativeStore.Stored input state) (running : state.halted=false)
    (code : input (some 19)=InstructionCodec.encodeMany bound instructions)
    (count : input (some 15)=List.replicate instructions.length true)
    (transition : Controller.Cost.programStep instructions.toArray state=some next) :
    NativeStore.Stored (output input state bound instructions) next :=
  NativePreserve.step_success _ state next bound instructions (NativeReset.ready input state bound instructions r running code count) transition

theorem program_banks (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (port : Port) (member : port=some 15 ∨ port=some 19) :
    output input state bound instructions port=input port := by
  rw [output,NativePreserve.step_program _ _ _ _ port member]
  rcases member with rfl | rfl <;> simp [NativeReset.output_at,NativeReset.ports]

theorem status (input : Port → List Bool) (next : Controller.Cost.State width registers)
    (observed : LoadBody.observation width registers input=some next) : input none=[] := by
  cases flag : input none with
  | nil => rfl
  | cons bit rest => simp [LoadBody.observation,flag] at observed

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (stored : NativeStore.Stored input state) (running : state.halted=false)
    (code : input (some 19)=InstructionCodec.encodeMany bound instructions)
    (count : input (some 15)=List.replicate instructions.length true)
    (limit : Nat) (nativeBound : state.liveWords ≤ limit) :
    let envelope := NativeEnvelope.mass width registers instructions.length
      (InstructionCodec.encodeMany bound instructions).length limit
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state bound instructions⟩ ticks peak ∧
      ticks ≤ FetchSetup.size input+45+NativeStep.budget envelope ∧
      peak ≤ max (2*FetchSetup.size input+45) (envelope+NativeStep.budget envelope) ∧
      FetchSetup.size (output input state bound instructions) ≤ envelope+NativeStep.budget envelope := by
  intro envelope
  obtain ⟨resetTicks,resetPeak,reset,resetTime,resetSpace⟩ := NativeReset.execution input
  obtain ⟨stepTicks,stepPeak,stepping,stepTime,stepSpace⟩ := NativeStep.execution (NativeReset.output input) state bound instructions
    (NativeReset.ready input state bound instructions stored running code count)
  have mass : FetchSetup.size (NativeReset.output input) ≤ envelope := by
    rw [NativeEnvelope.size_eq input state bound instructions stored code count]
    exact NativeEnvelope.mass_mono _ _ _ _ nativeBound
  have budgetBound := NativeEnvelope.budget_mono mass
  have time := stepTime.trans budgetBound
  have finalMass := stepping.final_live_le.trans stepping.peak_le
  change FetchSetup.size (output input state bound instructions) ≤ FetchSetup.size (NativeReset.output input)+stepTicks at finalMass
  have boundedPeak : stepPeak ≤ envelope+NativeStep.budget envelope := by omega
  have trace := reset.link stepping
  exact ⟨resetTicks+stepTicks,max resetPeak stepPeak,trace,by omega,
    max_le_max resetSpace boundedPeak,by omega⟩

theorem canonical_card : Fintype.card Label=13558 := by
  change Fintype.card (NativeReset.Label ⊕ NativeStep.Label)=_
  simp only [Fintype.card_sum,NativeReset.canonical_card,NativeStep.canonical_card,Nat.reduceAdd]

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 122022 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeCycle
