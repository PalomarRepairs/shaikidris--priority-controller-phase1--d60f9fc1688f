module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.BinaryIncrement
public import Controller.Complexity.SpaceFrames

@[expose] public section

/-! The executed binary increment in two selected banks of a larger machine.
The scratch bank starts and ends empty. Every unselected work bank, the exact
read-only head and the output history are preserved and charged in workspace. -/
namespace Controller.Complexity.SpaceCounter
open SpaceMachine

def program (ports : Bool ↪ K) := SpaceFrames.relocate ports BinaryIncrement.program

def prepared [DecidableEq K] (ports : Bool ↪ K) (tape : ReadOnlyInput.Tape) (output : List Bool)
    (frame : K → List Bool) (pc : Option (Fin 7)) (bits : List Bool) : SpaceMachine.State K (Fin 7) :=
  SpaceFrames.embedState ports frame (BinaryIncrement.state tape output pc bits [])

theorem ready [DecidableEq K] (ports : Bool ↪ K) (input : SpaceMachine.State K (Fin 7))
    (clean : input.work (ports true)=[]) :
    prepared ports input.tape input.output input.work input.pc (input.work (ports false))=input := by
  have work : BinaryIncrement.work (input.work (ports false)) []=(fun port => input.work (ports port)) := by
    funext port
    cases port <;> simp [clean]
  simp only [prepared,SpaceFrames.embedState,BinaryIncrement.state,work,SpaceFrames.ready_work]

theorem prepared_output [DecidableEq K] (ports : Bool ↪ K) (tape : ReadOnlyInput.Tape) (output : List Bool)
    (frame : K → List Bool) (pc : Option (Fin 7)) (bits : List Bool) :
    (prepared ports tape output frame pc bits).work=Function.update (Function.update frame (ports true) []) (ports false) bits := by
  funext target
  by_cases first : target=ports false
  · subst target
    simp [prepared,SpaceFrames.embedState,SpaceFrames.embedWork_at,BinaryIncrement.state]
  · by_cases second : target=ports true
    · subst target
      simp [prepared,SpaceFrames.embedState,SpaceFrames.embedWork_at,ports.injective.eq_iff,BinaryIncrement.state]
    · have outside : ∀ port, target ≠ ports port := by intro port; cases port <;> assumption
      simp [prepared,SpaceFrames.embedState,SpaceFrames.embedWork_other ports frame _ target outside,
        first,second]

theorem execution [Fintype K] [DecidableEq K] (ports : Bool ↪ K) (input : SpaceMachine.State K (Fin 7))
    (entry : input.pc=some (program ports).main) (clean : input.work (ports true)=[]) :
    ∃ final ticks peak, SpaceMachine.Execution (program ports) input final ticks peak ∧
      final.pc=none ∧ final.tape=input.tape ∧ final.output=input.output ∧
      final.work=Function.update input.work (ports false) (BinaryIncrement.increment (input.work (ports false))) ∧
      ticks=4*BinaryIncrement.carries (input.work (ports false))+4 ∧
      ticks ≤ 4*(input.work (ports false)).length+4 ∧ peak ≤ workspace input+1 := by
  obtain ⟨ticks,peak,actual,exactTime,time,space⟩ :=
    BinaryIncrement.execution input.tape input.output (input.work (ports false))
  have compiled := SpaceFrames.execution ports input.work actual
  have initial : prepared ports input.tape input.output input.work (some BinaryIncrement.program.main)
      (input.work (ports false))=input := by
    change input.pc=some BinaryIncrement.program.main at entry
    rw [← entry]
    exact ready ports input clean
  change SpaceMachine.Execution (program ports)
    (prepared ports input.tape input.output input.work (some BinaryIncrement.program.main) (input.work (ports false)))
    (prepared ports input.tape input.output input.work none (BinaryIncrement.increment (input.work (ports false))))
    ticks (peak+SpaceFrames.frameBits ports input.work) at compiled
  rw [initial] at compiled
  have mass := SpaceFrames.workspace_embed ports input.work
    (BinaryIncrement.state input.tape input.output (some BinaryIncrement.program.main) (input.work (ports false)) [])
  change workspace (prepared ports input.tape input.output input.work (some BinaryIncrement.program.main)
    (input.work (ports false)))=_ at mass
  rw [initial,BinaryIncrement.state_workspace] at mass
  simp only [List.length_nil,Nat.add_zero] at mass
  refine ⟨_,ticks,_,compiled,rfl,rfl,rfl,?_,exactTime,time,by omega⟩
  rw [prepared_output]
  have unchanged : Function.update input.work (ports true) []=input.work := by
    rw [← clean]
    exact Function.update_eq_self _ _
  rw [unchanged]

end Controller.Complexity.SpaceCounter
