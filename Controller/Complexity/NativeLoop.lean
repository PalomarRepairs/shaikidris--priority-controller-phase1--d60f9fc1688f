module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeCycle
public import Controller.Cost.Refinement

@[expose] public section

/-! A fixed physical interpreter repeats reset/fetch/dispatch. Native finite
execution and a genuinely halted final state imply termination of this machine;
the theorem makes no termination claim for arbitrary native programs. -/
namespace Controller.Complexity.NativeLoop
open StackMachine WordReader
open scoped BigOperators

structure Packets (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers)) : Prop where
  stored : NativeStore.Stored input state
  code : input (some 19)=InstructionCodec.encodeMany bound instructions
  count : input (some 15)=List.replicate instructions.length true

def Label : Type := NativeCycle.Label ⊕ Fin 3
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (NativeCycle.Label ⊕ Fin 3))
def program : Program (Fin 31) Label where
  main := .inr 1
  code label := match label with
    | .inl label => linkLeftInstruction 0 (NativeCycle.program.code label)
    | .inr control => if control=0 then .peek none (.inr 1) (.inr 2) (.inr 2)
      else if control=1 then .peek (some 26) (.inr 2) (.inl NativeCycle.program.main) (.inr 2)
      else .halt

def perStep (envelope : Nat) := envelope+2*NativeStep.budget envelope+47
def space (initial envelope : Nat) := 2*max initial (envelope+NativeStep.budget envelope)+45

theorem body_step {input next : State (Fin 31) NativeCycle.Label}
    (transition : step NativeCycle.program input=some next) :
    step program (linkLeftState (0 : Fin 3) input)=some (linkLeftState (0 : Fin 3) next) := by
  cases position : input.pc with
  | none => simp [step,position] at transition
  | some label =>
    have nextEq : instructionStep (NativeCycle.program.code label) input=next := by simpa [step,position] using transition
    simp only [step,linkLeftState,position,Option.elim_some,program]
    exact congrArg some ((linkLeftInstruction_step (0 : Fin 3) (NativeCycle.program.code label) input).trans
      (congrArg (linkLeftState (0 : Fin 3)) nextEq))

theorem lift_execution {input final : State (Fin 31) NativeCycle.Label} {ticks peak}
    (trace : Execution NativeCycle.program input final ticks peak) :
    Execution program (linkLeftState (0 : Fin 3) input) (linkLeftState (0 : Fin 3) final) ticks peak := by
  induction trace with
  | refl current => exact Execution.refl _
  | cons transition rest ih => exact Execution.cons (body_step transition) ih

theorem body_execution {input output : Port → List Bool} {ticks peak}
    (trace : Execution NativeCycle.program ⟨some NativeCycle.program.main,input⟩ ⟨none,output⟩ ticks peak) :
    Execution program ⟨some (.inl NativeCycle.program.main),input⟩ ⟨some (.inr 0),output⟩ ticks peak := lift_execution trace

theorem running (instructions : List (Controller.Cost.Instruction width registers))
    (state next : Controller.Cost.State width registers)
    (transition : Controller.Cost.programStep instructions.toArray state=some next) : state.halted=false := by
  cases flag : state.halted with
  | false => rfl
  | true =>
    unfold Controller.Cost.programStep at transition
    cases entry : instructions.toArray[state.pc.val]? <;> simp [entry,Controller.Cost.step,flag] at transition

theorem packets_next (input : Port → List Bool) (state next : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (packets : Packets input state bound instructions)
    (transition : Controller.Cost.programStep instructions.toArray state=some next) :
    Packets (NativeCycle.output input state bound instructions) next bound instructions where
  stored := NativeCycle.stored input state next bound instructions packets.stored
    (running instructions state next transition) packets.code packets.count transition
  code := (NativeCycle.program_banks input state bound instructions (some 19) (Or.inr rfl)).trans packets.code
  count := (NativeCycle.program_banks input state bound instructions (some 15) (Or.inl rfl)).trans packets.count

theorem finite_execution (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers))
    {state final : Controller.Cost.State width registers} {nativeTicks nativePeak}
    (native : Controller.Cost.Execution instructions.toArray state final nativeTicks nativePeak)
    (halted : final.halted=true) (limit : Nat) (wordBound : nativePeak ≤ limit)
    (input : Port → List Bool) (packets : Packets input state bound instructions) :
    let envelope := NativeEnvelope.mass width registers instructions.length
      (InstructionCodec.encodeMany bound instructions).length limit
    ∃ output ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output⟩ ticks peak ∧
      Packets output final bound instructions ∧
      ticks ≤ FetchSetup.size input+nativeTicks*perStep envelope+2 ∧
      peak ≤ space (FetchSetup.size input) envelope := by
  intro envelope
  induction native generalizing input with
  | refl state =>
    have flag : input (some 26)=[true] := packets.stored.haltStored.trans (congrArg List.singleton halted)
    have first : step program ⟨some program.main,input⟩=some ⟨some (.inr 2),input⟩ := by
      change some (instructionStep (.peek (some 26) (.inr 2) (.inl NativeCycle.program.main) (.inr 2))
        (⟨some program.main,input⟩ : State (Fin 31) Label))=_
      simp [instructionStep,flag]
    have last : step program ⟨some (.inr 2),input⟩=some ⟨none,input⟩ := rfl
    have trace := Execution.cons first (Execution.cons last (Execution.refl _))
    refine ⟨input,2,FetchSetup.size input,?_,packets,by simp,?_⟩
    · simpa only [live,FetchSetup.size,Nat.max_self,Nat.zero_add] using trace
    · have lower := le_max_left (FetchSetup.size input) (envelope+NativeStep.budget envelope)
      unfold space
      omega
  | @cons state middle final nativeTicks nativePeak transition rest ih =>
    have liveBound : state.liveWords ≤ limit := (Nat.le_max_left state.liveWords nativePeak).trans wordBound
    have stillRunning := running instructions state middle transition
    obtain ⟨bodyTicks,bodyPeak,body,bodyTime,bodySpace,middleMass⟩ := NativeCycle.execution input state bound instructions
      packets.stored stillRunning packets.code packets.count limit liveBound
    let middleInput := NativeCycle.output input state bound instructions
    have middlePackets := packets_next input state middle bound instructions packets transition
    have accepted : middleInput none=[] := NativeCycle.status middleInput middle
      ((NativeCycle.semantics input state bound instructions packets.stored stillRunning packets.code packets.count).trans transition)
    have first : step program ⟨some program.main,input⟩=some ⟨some (.inl NativeCycle.program.main),input⟩ := by
      change some (instructionStep (.peek (some 26) (.inr 2) (.inl NativeCycle.program.main) (.inr 2))
        (⟨some program.main,input⟩ : State (Fin 31) Label))=_
      simp [instructionStep,packets.stored.haltStored,stillRunning]
    have next : step program ⟨some (.inr 0),middleInput⟩=some ⟨some program.main,middleInput⟩ := by
      change some (instructionStep (.peek none (.inr 1) (.inr 2) (.inr 2))
        (⟨some (.inr 0),middleInput⟩ : State (Fin 31) Label))=_
      simp [instructionStep,accepted,program]
    have tailBound : nativePeak ≤ limit := (Nat.le_max_right state.liveWords nativePeak).trans wordBound
    obtain ⟨output,tailTicks,tailPeak,tail,outputPackets,tailTime,tailSpace⟩ := ih halted tailBound middleInput middlePackets
    have trace := Execution.cons first ((body_execution body).append (Execution.cons next tail))
    have m : FetchSetup.size middleInput ≤ envelope+NativeStep.budget envelope := middleMass
    have a := le_max_left (FetchSetup.size input) (envelope+NativeStep.budget envelope)
    have b := le_max_right (FetchSetup.size input) (envelope+NativeStep.budget envelope)
    have nextMax : max (FetchSetup.size middleInput) (envelope+NativeStep.budget envelope)=envelope+NativeStep.budget envelope := max_eq_right m
    have tailSpaceBound : tailPeak ≤ space (FetchSetup.size input) envelope := by
      unfold space at tailSpace ⊢
      rw [nextMax] at tailSpace
      dsimp only [envelope] at *
      omega
    have bodySpaceBound : bodyPeak ≤ space (FetchSetup.size input) envelope := by
      unfold space
      apply bodySpace.trans
      dsimp only [envelope] at *
      apply max_le <;> omega
    have peakBound : max (FetchSetup.size input) (max bodyPeak (max (FetchSetup.size middleInput) tailPeak)) ≤
        space (FetchSetup.size input) envelope := by unfold space at *; dsimp only [envelope] at *; omega
    have timeBound : bodyTicks+(tailTicks+1)+1 ≤ FetchSetup.size input+(nativeTicks+1)*perStep envelope+2 := by
      unfold perStep at *
      rw [Nat.add_mul,Nat.one_mul]
      dsimp only [envelope,middleInput] at *
      omega
    exact ⟨output,_,_,trace,outputPackets,timeBound,peakBound⟩

theorem canonical_card : Fintype.card Label=13561 := by
  change Fintype.card (NativeCycle.Label ⊕ Fin 3)=_
  simp only [Fintype.card_sum,NativeCycle.canonical_card,Fintype.card_fin,Nat.reduceAdd]

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 122049 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeLoop
