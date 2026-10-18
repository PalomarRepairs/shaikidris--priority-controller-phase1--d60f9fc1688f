module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ColdPackets
public import Controller.Complexity.GuardedChoice
public import Controller.Complexity.ColdResources

@[expose] public section

/-! One fixed binary machine starts from an input-only encoded native image.
It executes validation, native interpretation, canonical serialization and
terminal cleanup. Malformed images instead execute a fixed rejection return. -/
namespace Controller.Complexity.ColdInterpreter
open StackMachine WordReader
open scoped BigOperators

def ParserLabel : Type := StateReader.LabelsOf ImageReader.program
instance parserFintype : Fintype ParserLabel := inferInstanceAs (Fintype (StateReader.LabelsOf ImageReader.program))
def parserProgram : Program (Fin 31) ParserLabel := ImageReader.program
def mark : Program (Fin 31) (Fin 2) where
  main := 0
  code label := if label=0 then .push none false 1 else .halt
def reject : Program (Fin 31) (Fin 2 ⊕ Fin 2) := link (StackClear.program none) mark
def rejected (input : Port → List Bool) := Function.update input none [false]

def BodyLabel : Type := ParserLabel ⊕ (NativeRun.Label ⊕ (Fin 2 ⊕ Fin 2))
instance bodyFintype : Fintype BodyLabel := inferInstanceAs (Fintype (ParserLabel ⊕ (NativeRun.Label ⊕ (Fin 2 ⊕ Fin 2))))
def bodyProgram : Program (Fin 31) BodyLabel := GuardedChoice.program parserProgram NativeRun.program reject none Option.isNone
def Label : Type := BodyLabel ⊕ NativeReturn.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (BodyLabel ⊕ NativeReturn.Label))
def program : Program (Fin 31) Label := link bodyProgram NativeReturn.program

theorem reject_execution (input : Port → List Bool) :
    ∃ peak, Execution reject ⟨some reject.main,input⟩ ⟨none,rejected input⟩ ((input none).length+4) peak := by
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution input none
  have first : step mark ⟨some mark.main,Function.update input none []⟩=some ⟨some 1,rejected input⟩ := by
    change some (instructionStep (.push none false (1 : Fin 2)) ⟨some mark.main,Function.update input none []⟩)=_
    simp [instructionStep,rejected]
  have last : step mark ⟨some 1,rejected input⟩=some ⟨none,rejected input⟩ := rfl
  have marked := Execution.cons first (Execution.cons last (Execution.refl _))
  have trace := clearing.link marked
  have time : (input none).length+2+(0+1+1)=(input none).length+4 := by omega
  rw [time] at trace
  exact ⟨_,trace⟩

theorem rejection_size (input : Port → List Bool) : FetchSetup.size (rejected input) ≤ FetchSetup.size input+1 := by
  simpa only [rejected,List.length_cons,List.length_nil,Nat.zero_add] using OperandLoad.update_size_le input none [false]

theorem rejection_decode (width registers : Nat) : MachineBridge.decodeState width registers [false]=none := rfl

theorem encoded_execution (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers))
    {state final : Controller.Cost.State width registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution instructions.toArray state final nativeTicks nativePeak)
    (halted : final.halted=true) :
    let input := MachineInput.encode (ColdPackets.image bound instructions state)
    let size := input.length
    let parsedBound := ImageReader.polynomial size
    let envelope := NativeEnvelope.mass width registers instructions.length
      (InstructionCodec.encodeMany bound instructions).length nativePeak
    let spaceBound := NativeLoop.space (size+parsedBound) envelope
    ∃ ticks peak, Execution program (initial program input) (StackMachine.terminal (MachineBridge.encodeState final)) ticks peak ∧
      ticks ≤ size+2*parsedBound+nativeTicks*NativeLoop.perStep envelope+11*spaceBound+121 ∧
      peak ≤ 12*spaceBound+119 := by
  intro input size parsedBound envelope spaceBound
  obtain ⟨parseTicks,parsePeak,parsing,parseTime,parseSpace⟩ := ColdPackets.execution bound instructions state
  let parsed := ColdPackets.output bound instructions state
  have packets := ColdPackets.packets bound instructions state
  obtain ⟨middle,runTicks,runPeak,running,encoded,_,runTime,runSpace⟩ :=
    NativeRun.finite_execution bound instructions native halted parsed packets
  have accepted : Option.isNone ((parsed none).head?)=true := by
    simp [parsed,ColdPackets.output,StateNative.store_status]
  rw [ColdInput.initial_bank] at parsing
  have first := GuardedChoice.success reject none Option.isNone parsing running accepted
  obtain ⟨returnTicks,returnPeak,returning,returnTime,returnSpace⟩ := NativeReturn.execution middle
  have actualReturn : Execution NativeReturn.program ⟨some NativeReturn.program.main,middle⟩
      ⟨none,NativeReturn.output middle⟩ returnTicks returnPeak := by rw [NativeReturn.terminal]; exact returning
  have trace := first.link actualReturn
  change Execution program ⟨some program.main,_⟩ ⟨none,NativeReturn.output middle⟩
    (parseTicks+runTicks+returnTicks) (max (max parsePeak runPeak) returnPeak) at trace
  rw [← ColdInput.initial_bank program] at trace
  have mass := parsing.final_live_le.trans parseSpace
  change FetchSetup.size parsed ≤ parsedBound+size at mass
  have middleMass := running.final_live_le.trans runSpace
  change FetchSetup.size middle ≤ 6*NativeLoop.space (FetchSetup.size parsed) envelope+28 at middleMass
  have bounds := ColdResources.accepted size parsedBound envelope nativeTicks parseTicks parsePeak
    (FetchSetup.size parsed) runTicks runPeak (FetchSetup.size middle) returnTicks returnPeak
    parseTime parseSpace mass runTime runSpace middleMass returnTime returnSpace
  have endpoint : (⟨none,NativeReturn.output middle⟩ : State (Fin 31) Label)=StackMachine.terminal (MachineBridge.encodeState final) := by
    congr 1
    funext port
    cases port <;> simp [NativeReturn.output_at,encoded]
  rw [endpoint] at trace
  exact ⟨_,_,trace,bounds.1,bounds.2⟩

theorem malformed_execution (input : List Bool) (malformed : MachineInput.decode input=none) :
    ∃ ticks peak, Execution program (initial program input) (StackMachine.terminal [false]) ticks peak ∧
      ticks ≤ 3*ImageReader.polynomial input.length+2*input.length+68 ∧
      peak ≤ 2*(ImageReader.polynomial input.length+input.length)+65 := by
  obtain ⟨parseTicks,parsePeak,parsed,parsing,parseTime,parseSpace,status,_⟩ := ImageReader.total_decodes input
  have rejected : Option.isNone ((parsed none).head?)=false := by simpa only [malformed,Option.isSome_none] using status
  obtain ⟨rejectPeak,rejecting⟩ := reject_execution parsed
  rw [ColdInput.initial_bank] at parsing
  have first := GuardedChoice.failure NativeRun.program none Option.isNone parsing rejecting rejected
  obtain ⟨returnTicks,returnPeak,returning,returnTime,returnSpace⟩ := NativeReturn.execution (ColdInterpreter.rejected parsed)
  have actualReturn : Execution NativeReturn.program ⟨some NativeReturn.program.main,ColdInterpreter.rejected parsed⟩
      ⟨none,NativeReturn.output (ColdInterpreter.rejected parsed)⟩ returnTicks returnPeak := by rw [NativeReturn.terminal]; exact returning
  have trace := first.link actualReturn
  change Execution program ⟨some program.main,_⟩ ⟨none,NativeReturn.output (ColdInterpreter.rejected parsed)⟩
    _ _ at trace
  rw [← ColdInput.initial_bank program] at trace
  have parsedMass := parsing.final_live_le.trans parseSpace
  change FetchSetup.size parsed ≤ ImageReader.polynomial input.length+input.length at parsedMass
  have cell : (parsed none).length ≤ FetchSetup.size parsed :=
    Finset.single_le_sum (f := fun port : Port => (parsed port).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ none)
  have rejectSpace := rejecting.peak_le
  change rejectPeak ≤ FetchSetup.size parsed+((parsed none).length+4) at rejectSpace
  have returnMass := rejection_size parsed
  have bounds := ColdResources.rejected input.length (ImageReader.polynomial input.length) parseTicks parsePeak
    (FetchSetup.size parsed) (parsed none).length rejectPeak (FetchSetup.size (ColdInterpreter.rejected parsed)) returnTicks returnPeak
    parseTime parseSpace parsedMass cell rejectSpace returnMass returnTime returnSpace
  have endpoint : (⟨none,NativeReturn.output (ColdInterpreter.rejected parsed)⟩ : State (Fin 31) Label)=StackMachine.terminal [false] := by
    congr 1
    funext port
    cases port <;> simp [NativeReturn.output_at,ColdInterpreter.rejected]
  rw [endpoint] at trace
  exact ⟨_,_,trace,bounds.1,bounds.2⟩

theorem parser_card : Fintype.card ParserLabel=1403 := ImageReader.canonical_card

theorem canonical_card : Fintype.card Label=15096 := by
  have branches : Fintype.card (NativeRun.Label ⊕ (Fin 2 ⊕ Fin 2))=Fintype.card NativeRun.Label+4 := by
    calc
      _ = Fintype.card NativeRun.Label+Fintype.card (Fin 2 ⊕ Fin 2) := Fintype.card_sum
      _ = Fintype.card NativeRun.Label+4 := by rw [Fintype.card_sum,Fintype.card_fin]
  have body : Fintype.card BodyLabel=Fintype.card ParserLabel+Fintype.card (NativeRun.Label ⊕ (Fin 2 ⊕ Fin 2)) := Fintype.card_sum
  have split : Fintype.card Label=Fintype.card BodyLabel+Fintype.card NativeReturn.Label := Fintype.card_sum
  rw [body,branches,parser_card,NativeRun.canonical_card,NativeReturn.canonical_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 135864 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.ColdInterpreter
