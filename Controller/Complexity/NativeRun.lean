module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeLoop
public import Controller.Complexity.NativeSerialize

@[expose] public section

/-! The fixed interpreter and a physical halted-state guard feed canonical
state serialization. Finite halted native executions produce literal encoded
state bytes, with explicit time, live-bit and resident-code bounds. -/
namespace Controller.Complexity.NativeRun
open StackMachine WordReader
open scoped BigOperators

def accept (flag : Option Bool) : Bool := flag==some true
def Label : Type := NativeLoop.Label ⊕ Option NativeSerialize.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (NativeLoop.Label ⊕ Option NativeSerialize.Label))
def program : Program (Fin 31) Label := GuardedLink.program NativeLoop.program NativeSerialize.program (some 26) accept

theorem finite_execution (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers))
    {state final : Controller.Cost.State width registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution instructions.toArray state final nativeTicks nativePeak)
    (halted : final.halted=true) (input : Port → List Bool)
    (packets : NativeLoop.Packets input state bound instructions) :
    let envelope := NativeEnvelope.mass width registers instructions.length
      (InstructionCodec.encodeMany bound instructions).length nativePeak
    ∃ output ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output⟩ ticks peak ∧
      output none=MachineBridge.encodeState final ∧ NativeStore.Stored output final ∧
      ticks ≤ FetchSetup.size input+nativeTicks*NativeLoop.perStep envelope+5*NativeLoop.space (FetchSetup.size input) envelope+30 ∧
      peak ≤ 6*NativeLoop.space (FetchSetup.size input) envelope+28 := by
  intro envelope
  obtain ⟨middle,loopTicks,loopPeak,loop,finalPackets,loopTime,loopSpace⟩ :=
    NativeLoop.finite_execution bound instructions native halted nativePeak (Nat.le_refl _) input packets
  obtain ⟨serializeTicks,serializePeak,serialize,_,serializeTime,serializeSpace⟩ := NativeSerialize.execution middle
  have flag : middle (some 26)=[true] := finalPackets.stored.haltStored.trans (congrArg List.singleton halted)
  have accepted : accept ((middle (some 26)).head?)=true := by simp [accept,flag]
  have trace := GuardedLink.success (some 26) accept loop serialize accepted
  have mass := loop.final_live_le.trans loopSpace
  change FetchSetup.size middle ≤ NativeLoop.space (FetchSetup.size input) envelope at mass
  have finalTime : loopTicks+serializeTicks ≤ FetchSetup.size input+nativeTicks*NativeLoop.perStep envelope+
      5*NativeLoop.space (FetchSetup.size input) envelope+30 := by
    dsimp only [envelope] at *
    omega
  have finalSpace : max loopPeak serializePeak ≤ 6*NativeLoop.space (FetchSetup.size input) envelope+28 := by
    dsimp only [envelope] at *
    omega
  exact ⟨NativeSerialize.output middle,loopTicks+serializeTicks,max loopPeak serializePeak,trace,
    NativeSerialize.canonical_output middle final finalPackets.stored,NativeSerialize.stored middle final finalPackets.stored,
    finalTime,finalSpace⟩

theorem canonical_card : Fintype.card Label=13626 := by
  change Fintype.card (NativeLoop.Label ⊕ Option NativeSerialize.Label)=_
  simp only [Fintype.card_sum,Fintype.card_option,NativeLoop.canonical_card,NativeSerialize.canonical_card,Nat.reduceAdd]

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 122634 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeRun
