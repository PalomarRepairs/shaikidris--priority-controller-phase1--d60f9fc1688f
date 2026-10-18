module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.BinaryDecrement
public import Controller.Complexity.SpaceCounter

@[expose] public section

/-! Binary decrement in two selected work banks. The scratch bank starts and
ends empty, all other work is retained, and the actual workspace peak equals
the original workspace, including every ambient bank. -/
namespace Controller.Complexity.SpaceDecrement
open SpaceMachine

def program (ports : Bool ↪ K) := SpaceFrames.relocate ports BinaryDecrement.program

theorem execution [Fintype K] [DecidableEq K] (ports : Bool ↪ K) (input : SpaceMachine.State K (Fin 7))
    (entry : input.pc=some (program ports).main) (clean : input.work (ports true)=[]) :
    SpaceMachine.Execution (program ports) input
      ⟨none,input.tape,Function.update input.work (ports false) (BinaryDecrement.decrement (input.work (ports false))),input.output⟩
      (BinaryDecrement.cost (input.work (ports false))) (workspace input) := by
  have source := BinaryDecrement.execution input.tape input.output (input.work (ports false))
  have compiled := SpaceFrames.execution ports input.work source
  have start : SpaceCounter.prepared ports input.tape input.output input.work (some BinaryDecrement.program.main)
      (input.work (ports false))=input := by
    change input.pc=some BinaryDecrement.program.main at entry
    rw [← entry]
    exact SpaceCounter.ready ports input clean
  change SpaceMachine.Execution (program ports)
    (SpaceCounter.prepared ports input.tape input.output input.work (some BinaryDecrement.program.main) (input.work (ports false)))
    (SpaceCounter.prepared ports input.tape input.output input.work none (BinaryDecrement.decrement (input.work (ports false))))
    _ _ at compiled
  rw [start] at compiled
  have final : SpaceCounter.prepared ports input.tape input.output input.work none (BinaryDecrement.decrement (input.work (ports false)))=
      ⟨none,input.tape,Function.update input.work (ports false) (BinaryDecrement.decrement (input.work (ports false))),input.output⟩ := by
    have unchanged : Function.update input.work (ports true) []=input.work := by
      rw [← clean]
      exact Function.update_eq_self _ _
    have work := SpaceCounter.prepared_output ports input.tape input.output input.work none
      (BinaryDecrement.decrement (input.work (ports false)))
    rw [unchanged] at work
    exact congrArg (fun bank => (⟨none,input.tape,bank,input.output⟩ : SpaceMachine.State K (Fin 7))) work
  rw [final] at compiled
  have mass := SpaceFrames.workspace_embed ports input.work
    (BinaryIncrement.state input.tape input.output (some BinaryDecrement.program.main) (input.work (ports false)) [])
  change workspace (SpaceCounter.prepared ports input.tape input.output input.work (some BinaryDecrement.program.main)
    (input.work (ports false)))=_ at mass
  rw [start,BinaryIncrement.state_workspace] at mass
  simp only [List.length_nil,Nat.add_zero] at mass
  rwa [← mass] at compiled

theorem encoded_execution [Fintype K] [DecidableEq K] (ports : Bool ↪ K) (input : SpaceMachine.State K (Fin 7))
    (entry : input.pc=some (program ports).main) (clean : input.work (ports true)=[])
    (number : Nat) (encoded : input.work (ports false)=number.bits) :
    ∃ ticks, SpaceMachine.Execution (program ports) input
      ⟨none,input.tape,Function.update input.work (ports false) (number-1).bits,input.output⟩ ticks (workspace input) ∧
      ticks ≤ 4*(Nat.log 2 (number+2)+1)+3 := by
  have actual := execution ports input entry clean
  rw [encoded,BinaryDecrement.decrement_bits] at actual
  have time := BinaryDecrement.cost_le number.bits
  have length := BinaryIncrement.counter_length number
  exact ⟨_,actual,by omega⟩

end Controller.Complexity.SpaceDecrement
