module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceRequestSetup
public import Controller.Complexity.LogSpaceBounds

@[expose] public section

/-! Complete intermediate-bit request from dirty lookup workspace. Setup
physically erases every left bank, preserves and copies the caller's saved
request and rewinds the original input. The first transducer then recomputes
one bit or EOF while every caller bank and external output history is retained.
Source termination is supplied by an actual input-only halted source trace. -/
namespace Controller.Complexity.SpaceRequest
open SpaceMachine

abbrev Label (n : Nat) (Q : Type) := SpaceRequestSetup.Label n ⊕ SpaceLookup.Label Q

def program (source : SpaceMachine.Program K Q) (enumeration : Fin n ≃ SpaceLookup.Bank K) (request : J) :
    SpaceMachine.Program (SpaceRequestSetup.Bank K J) (Label n Q) :=
  SpaceLink.program (SpaceRequestSetup.program enumeration request)
    (SpaceSuppress.program (J:=J) (SpaceLookup.program source))

theorem label_card [Fintype Q] (n : Nat) : Fintype.card (Label n Q)=2*n+8*Fintype.card Q+18 := by
  calc
    _ = Fintype.card (SpaceRequestSetup.Label n)+Fintype.card (SpaceLookup.Label Q) := Fintype.card_sum
    _ = _ := by rw [SpaceRequestSetup.label_card,SpaceLookup.label_card]; omega

theorem resident [Fintype Q] (source : SpaceMachine.Program K Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank K) (request : J) :
    (∑ label, StackMachine.statementSize (SpaceTM.statement ((program source enumeration request).code label))) ≤
      9*(2*n+8*Fintype.card Q+18) := by
  simpa only [label_card] using SpaceTM.resident (program source enumeration request)

theorem execution [Fintype K] [Fintype J] [DecidableEq K] [DecidableEq J]
    (source : SpaceMachine.Program K Q) (enumeration : Fin n ≃ SpaceLookup.Bank K) (request : J)
    (input : SpaceMachine.State (SpaceRequestSetup.Bank K J) (Label n Q))
    (entry : input.pc=some (program source enumeration request).main)
    (number : Nat) (encoded : input.work (.inr request)=number.bits)
    {sourceFinal sourceTicks sourcePeak}
    (trace : SpaceMachine.Execution source (SpaceMachine.initial source (ReadOnlyInput.word input.tape)) sourceFinal sourceTicks sourcePeak)
    (halted : sourceFinal.pc=none) :
    ∃ result ticks peak, SpaceMachine.Execution (program source enumeration request) input result ticks peak ∧
      result.pc=none ∧ result.output=input.output ∧
      result.work (.inl SpaceLookup.answer)=(sourceFinal.output.reverse[number]?).toList ∧
      (∀ port, result.work (.inr port)=input.work (.inr port)) ∧
      ticks ≤ workspace input+2*n+5*number.bits.length+2*input.tape.left.length+10+
        sourceTicks*SpaceLookupTrace.budget number ∧
      peak ≤ max (workspace input)
        (SpaceBuffers.mass (SpaceRequestSetup.caller input.work)+sourcePeak+SpaceLookupTrace.width number+1) := by
  let setupInput : SpaceMachine.State (SpaceRequestSetup.Bank K J) (SpaceRequestSetup.Label n) :=
    ⟨some (SpaceRequestSetup.program enumeration request).main,input.tape,input.work,input.output⟩
  obtain ⟨setupTicks,setupTrace,setupTime⟩ :=
    SpaceRequestSetup.execution enumeration request setupInput rfl number encoded
  obtain ⟨found,lookupTicks,lookupPeak,lookupTrace,stopped,retained,answer,timeBound,spaceBound⟩ :=
    SpaceLookupTrace.from_execution trace halted input.output number
  have framed := SpaceSuppress.execution (SpaceRequestSetup.caller input.work) input.output lookupTrace
  have prepared : SpaceSuppress.state (SpaceRequestSetup.caller input.work) input.output
      (SpaceLookup.view input.output (SpaceMachine.initial source (ReadOnlyInput.word input.tape)) number)=
      (⟨some (SpaceSuppress.program (J:=J) (SpaceLookup.program source)).main,
        ReadOnlyInput.start (ReadOnlyInput.word input.tape),SpaceRequestSetup.readyWork input.work number,input.output⟩ :
        SpaceMachine.State (SpaceRequestSetup.Bank K J) (SpaceLookup.Label Q)) := rfl
  rw [prepared] at framed
  change SpaceMachine.Execution (SpaceSuppress.program (J:=J) (SpaceLookup.program source))
    ⟨some (SpaceSuppress.program (J:=J) (SpaceLookup.program source)).main,
      ReadOnlyInput.start (ReadOnlyInput.word input.tape),SpaceRequestSetup.readyWork input.work number,input.output⟩
    ⟨found.pc,found.tape,Sum.elim found.work (SpaceRequestSetup.caller input.work),input.output⟩
    lookupTicks (lookupPeak+SpaceBuffers.mass (SpaceRequestSetup.caller input.work)) at framed
  rw [stopped] at framed
  have complete := SpaceLink.execution setupTrace framed
  have ready : (⟨some (program source enumeration request).main,input.tape,input.work,input.output⟩ :
      SpaceMachine.State (SpaceRequestSetup.Bank K J) (Label n Q))=input := by
    cases input with
    | mk pc tape bank output => cases entry; rfl
  change SpaceMachine.Execution (program source enumeration request)
    ⟨some (program source enumeration request).main,input.tape,input.work,input.output⟩
    ⟨none,found.tape,Sum.elim found.work (SpaceRequestSetup.caller input.work),input.output⟩
    (setupTicks+lookupTicks)
    (max (max (workspace setupInput) (SpaceBuffers.mass (SpaceRequestSetup.caller setupInput.work)+number.bits.length))
      (lookupPeak+SpaceBuffers.mass (SpaceRequestSetup.caller input.work))) at complete
  rw [ready] at complete
  refine ⟨_,_,_,complete,rfl,rfl,?_,fun _ => rfl,?_,?_⟩
  · simpa only [Sum.elim_inl,SpaceMachine.initial,List.length_nil,List.drop_zero] using answer
  · change setupTicks ≤ workspace input+2*n+5*number.bits.length+2*input.tape.left.length+7 at setupTime
    omega
  · change max (max (workspace input) (SpaceBuffers.mass (SpaceRequestSetup.caller input.work)+number.bits.length))
      (lookupPeak+SpaceBuffers.mass (SpaceRequestSetup.caller input.work)) ≤ _
    have length := SpaceLookupTrace.counter_length number number le_rfl
    omega

theorem computed [Fintype K] [Fintype J] [Fintype Q] [DecidableEq K] [DecidableEq J]
    (source : SpaceMachine.Program K Q) (enumeration : Fin n ≃ SpaceLookup.Bank K) (request : J)
    {function constant} (computes : LogSpaceBounds.Computes source function constant)
    (input : SpaceMachine.State (SpaceRequestSetup.Bank K J) (Label n Q))
    (entry : input.pc=some (program source enumeration request).main)
    (number : Nat) (encoded : input.work (.inr request)=number.bits) :
    ∃ result ticks peak, SpaceMachine.Execution (program source enumeration request) input result ticks peak ∧
      result.pc=none ∧ result.output=input.output ∧
      result.work (.inl SpaceLookup.answer)=((function (ReadOnlyInput.word input.tape))[number]?).toList ∧
      (∀ port, result.work (.inr port)=input.work (.inr port)) ∧
      ticks ≤ workspace input+2*n+5*number.bits.length+2*input.tape.left.length+10+
        LogSpaceBounds.timeBound (Fintype.card Q) (Fintype.card K) constant (ReadOnlyInput.word input.tape).length*
          SpaceLookupTrace.budget number ∧
      peak ≤ max (workspace input)
        (SpaceBuffers.mass (SpaceRequestSetup.caller input.work)+
          constant*LogSpaceBounds.bits (ReadOnlyInput.word input.tape).length+SpaceLookupTrace.width number+1) := by
  obtain ⟨sourceFinal,sourceTicks,sourcePeak,trace,halted,output,space⟩ := computes.2 (ReadOnlyInput.word input.tape)
  have sourceTime := LogSpaceBounds.running_time trace halted
    (by simpa only [SpaceMachine.initial,ReadOnlyInput.word_start] using space)
  simp only [SpaceMachine.initial,ReadOnlyInput.word_start] at sourceTime
  have productBound := Nat.mul_le_mul_right (SpaceLookupTrace.budget number) sourceTime
  obtain ⟨result,ticks,peak,actual,stopped,retained,answer,caller,timeBound,spaceBound⟩ :=
    execution source enumeration request input entry number encoded trace halted
  rw [output] at answer
  refine ⟨result,ticks,peak,actual,stopped,retained,answer,caller,?_,?_⟩ <;> omega

end Controller.Complexity.SpaceRequest
