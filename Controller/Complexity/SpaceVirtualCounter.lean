module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtual

@[expose] public section

/-! Literal increment/decrement subroutines for the second transducer's
virtual input head. They retain the original physical input, first-machine
workspace, second-machine work and external output. Scratch starts and ends
empty; every retained bank is charged. -/
namespace Controller.Complexity.SpaceVirtualCounter
open SpaceMachine SpaceVirtual

theorem increment [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) (state : SpaceMachine.State (Bank A B) (Label n P Q))
    (next : Q) (number : Nat) (encoded : state.work headPort=number.bits) (clean : state.work scratchPort=[]) :
    ∃ ticks peak, SpaceMachine.Execution (program first second enumeration)
      ⟨some (incrementLabel next (SpaceCounter.program (ports (A:=A) (B:=B))).main),state.tape,state.work,state.output⟩
      ⟨some (sourceLabel next),state.tape,Function.update state.work headPort (number+1).bits,state.output⟩ ticks peak ∧
      peak ≤ workspace state+1 := by
  let input : SpaceMachine.State (Bank A B) (Fin 7) :=
    ⟨some (SpaceCounter.program (ports (A:=A) (B:=B))).main,state.tape,state.work,state.output⟩
  obtain ⟨final,ticks,peak,actual,stopped,tape,output,work,exactTime,time,space⟩ :=
    SpaceCounter.execution ports input rfl clean
  have canonical : BinaryIncrement.increment (input.work (ports (A:=A) (B:=B) false))=(number+1).bits := by
    change BinaryIncrement.increment (state.work headPort)=_
    rw [encoded,BinaryIncrement.increment_bits]
  rw [canonical] at work
  have finalEq : final=⟨none,state.tape,Function.update state.work headPort (number+1).bits,state.output⟩ := by
    cases final with
    | mk finalPc finalTape finalBank finalOutput =>
      cases stopped
      cases tape
      cases output
      cases work
      rfl
  rw [finalEq] at actual
  have compiled := SpaceControl.execution (SpaceCounter.program ports) (program first second enumeration)
    (incrementLabel next) (some (sourceLabel next)) (fun _ => rfl) actual
  exact ⟨ticks,peak,compiled,space⟩

theorem decrement [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) (state : SpaceMachine.State (Bank A B) (Label n P Q))
    (next : Q) (number : Nat) (encoded : state.work headPort=number.bits) (clean : state.work scratchPort=[]) :
    ∃ ticks, SpaceMachine.Execution (program first second enumeration)
      ⟨some (decrementLabel next (SpaceDecrement.program (ports (A:=A) (B:=B))).main),state.tape,state.work,state.output⟩
      ⟨some (sourceLabel next),state.tape,Function.update state.work headPort (number-1).bits,state.output⟩ ticks (workspace state) := by
  let input : SpaceMachine.State (Bank A B) (Fin 7) :=
    ⟨some (SpaceDecrement.program (ports (A:=A) (B:=B))).main,state.tape,state.work,state.output⟩
  obtain ⟨ticks,actual,time⟩ := SpaceDecrement.encoded_execution ports input rfl clean number encoded
  have compiled := SpaceControl.execution (SpaceDecrement.program ports) (program first second enumeration)
    (decrementLabel next) (some (sourceLabel next)) (fun _ => rfl) actual
  exact ⟨ticks,compiled⟩

end Controller.Complexity.SpaceVirtualCounter
