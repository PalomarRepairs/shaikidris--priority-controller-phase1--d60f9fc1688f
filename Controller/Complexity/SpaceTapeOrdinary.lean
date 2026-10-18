module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeRun

@[expose] public section

/-! One-step ordinary-tape realizations of source push, input read, right
movement, output emission, control transfer and halt. -/
namespace Controller.Complexity.SpaceTapeOrdinary
open SpaceTapeMachine SpaceMachine

theorem run_step [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label : Q) (position : source.pc=some label) :
    SpaceTapeMachine.step enumeration program (configuration source)=
      some (apply (delta enumeration program (.run label) (SpaceInputTape.encode source.tape).head
        (fun port => (SpaceWorkTape.encode (source.work port)).head)) (configuration source)) := by
  simp [SpaceTapeMachine.step,configuration,position]

theorem push [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label : Q) (port : K) (bit : Bool) (next : Q)
    (position : source.pc=some label) (code : program.code label=.push port bit next) :
    SpaceTapeMachine.step enumeration program (configuration source)=
      some (configuration (instructionStep (.push port bit next) source)) := by
  rw [run_step enumeration program source label position]
  congr 1
  simp only [delta,code,apply,configuration,instructionStep,advance,operate,shift,
    Option.elim_some,Option.elim_none,Option.map_some]
  congr 1
  · funext selected
    by_cases same : selected=port
    · subst selected; simp [SpaceWorkTape.push]
    · simp [same]
  · funext selected
    by_cases same : selected=port
    · subst selected; simp
    · simp [same]

theorem readInput [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label eof low high : Q)
    (position : source.pc=some label) (code : program.code label=.readInput eof low high) :
    SpaceTapeMachine.step enumeration program (configuration source)=
      some (configuration (instructionStep (.readInput eof low high) source)) := by
  rw [run_step enumeration program source label position]
  simp [delta,code,apply,configuration,instructionStep,advance,SpaceInputTape.symbol]

theorem emit [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label : Q) (bit : Bool) (next : Q)
    (position : source.pc=some label) (code : program.code label=.emit bit next) :
    SpaceTapeMachine.step enumeration program (configuration source)=
      some (configuration (instructionStep (.emit bit next) source)) := by
  rw [run_step enumeration program source label position]
  simp [delta,code,apply,configuration,instructionStep,advance]

theorem jump [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label next : Q)
    (position : source.pc=some label) (code : program.code label=.jump next) :
    SpaceTapeMachine.step enumeration program (configuration source)=
      some (configuration (instructionStep (.jump next) source)) := by
  rw [run_step enumeration program source label position]
  simp [delta,code,apply,configuration,instructionStep,advance]

theorem halt [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label : Q)
    (position : source.pc=some label) (code : program.code label=.halt) :
    SpaceTapeMachine.step enumeration program (configuration source)=
      some (configuration (instructionStep .halt source)) := by
  rw [run_step enumeration program source label position]
  simp [delta,code,apply,configuration,instructionStep]

theorem right [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label next : Q)
    (position : source.pc=some label) (code : program.code label=.right next) :
    SpaceTapeMachine.step enumeration program (configuration source)=
      some (configuration (instructionStep (.right next) source)) := by
  rw [run_step enumeration program source label position]
  congr 1
  simp only [delta,code,apply,configuration,instructionStep,advance,Option.elim_none,Option.map_some]
  congr 1
  by_cases flag : (SpaceInputTape.encode source.tape).head=.stop <;>
    simpa [flag] using SpaceInputTape.right_clamped source.tape

end Controller.Complexity.SpaceTapeOrdinary
