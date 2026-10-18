module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeRun
public import Controller.Complexity.NativeReturn

@[expose] public section

/-! Finite halted native executions reach a literal binary-machine terminal
configuration containing their canonical final-state encoding. Every work
stack is erased by an executed finite return routine. -/
namespace Controller.Complexity.NativeDeliver
open StackMachine WordReader
open scoped BigOperators

def Label : Type := NativeRun.Label ⊕ NativeReturn.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (NativeRun.Label ⊕ NativeReturn.Label))
def program : Program (Fin 31) Label := link NativeRun.program NativeReturn.program

theorem finite_execution (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers))
    {state final : Controller.Cost.State width registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution instructions.toArray state final nativeTicks nativePeak)
    (halted : final.halted=true) (input : Port → List Bool)
    (packets : NativeLoop.Packets input state bound instructions) :
    let envelope := NativeEnvelope.mass width registers instructions.length
      (InstructionCodec.encodeMany bound instructions).length nativePeak
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ (StackMachine.terminal (MachineBridge.encodeState final)) ticks peak ∧
      ticks ≤ FetchSetup.size input+nativeTicks*NativeLoop.perStep envelope+11*NativeLoop.space (FetchSetup.size input) envelope+121 ∧
      peak ≤ 12*NativeLoop.space (FetchSetup.size input) envelope+119 := by
  intro envelope
  obtain ⟨middle,runTicks,runPeak,running,encoded,_,runTime,runSpace⟩ :=
    NativeRun.finite_execution bound instructions native halted input packets
  obtain ⟨returnTicks,returnPeak,returning,returnTime,returnSpace⟩ := NativeReturn.execution middle
  have actualReturn : Execution NativeReturn.program ⟨some NativeReturn.program.main,middle⟩
      ⟨none,NativeReturn.output middle⟩ returnTicks returnPeak := by
    rw [NativeReturn.terminal]
    exact returning
  have trace := running.link actualReturn
  have mass := running.final_live_le.trans runSpace
  change FetchSetup.size middle ≤ 6*NativeLoop.space (FetchSetup.size input) envelope+28 at mass
  have finalTime : runTicks+returnTicks ≤ FetchSetup.size input+nativeTicks*NativeLoop.perStep envelope+
      11*NativeLoop.space (FetchSetup.size input) envelope+121 := by dsimp only [envelope] at *; omega
  have finalSpace : max runPeak returnPeak ≤ 12*NativeLoop.space (FetchSetup.size input) envelope+119 := by
    dsimp only [envelope] at *
    omega
  have endpoint : (⟨none,NativeReturn.output middle⟩ : State (Fin 31) Label)=StackMachine.terminal (MachineBridge.encodeState final) := by
    congr 1
    funext port
    cases port <;> simp [NativeReturn.output_at,encoded]
  change Execution program ⟨some program.main,input⟩ ⟨none,NativeReturn.output middle⟩
    (runTicks+returnTicks) (max runPeak returnPeak) at trace
  rw [endpoint] at trace
  exact ⟨runTicks+returnTicks,max runPeak returnPeak,trace,finalTime,finalSpace⟩

theorem canonical_card : Fintype.card Label=13689 := by
  change Fintype.card (NativeRun.Label ⊕ NativeReturn.Label)=_
  simp only [Fintype.card_sum,NativeRun.canonical_card,NativeReturn.canonical_card,Nat.reduceAdd]

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 123201 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeDeliver
