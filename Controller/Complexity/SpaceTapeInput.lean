module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTapeOrdinary

@[expose] public section

/-! The start test and clamped left move inspect the start marker by moving
the immutable input head left. Every work tape and allocation counter is retained. -/
namespace Controller.Complexity.SpaceTapeInput
open SpaceTapeMachine SpaceMachine SpaceTapeRun

def lower (source : SpaceMachine.State K Q) (phase : Label n K Q) : SpaceTapeMachine.State n K Q :=
  { (configuration source : SpaceTapeMachine.State n K Q) with
    pc := some phase, input := (SpaceInputTape.encode source.tape).move .left }

theorem lower_within (source : SpaceMachine.State K Q) (phase : Label n K Q)
    (bound : ∀ port, (source.work port).length+2 ≤ capacity) : Within capacity (lower source phase) :=
  configuration_within (n := n) source capacity bound

theorem left_first [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label next : Q)
    (position : source.pc=some label) (code : program.code label=.left next) :
    SpaceTapeMachine.step enumeration program (configuration source)=some (lower source (.left next)) := by
  rw [SpaceTapeOrdinary.run_step enumeration program source label position]
  simp only [delta,code]
  rfl

theorem start_first [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (label yes no : Q)
    (position : source.pc=some label) (code : program.code label=.atStart yes no) :
    SpaceTapeMachine.step enumeration program (configuration source)=some (lower source (.start yes no)) := by
  rw [SpaceTapeOrdinary.run_step enumeration program source label position]
  simp only [delta,code]
  rfl

theorem left_return [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (next : Q) :
    SpaceTapeMachine.step enumeration program (lower source (.left next))=
      some (configuration (instructionStep (.left next) source)) := by
  simp only [SpaceTapeMachine.step,lower,Option.map_some,delta]
  congr 1
  simp only [apply,configuration,instructionStep,advance,Option.elim_none,Option.map_some]
  congr 1
  by_cases flag : ((SpaceInputTape.encode source.tape).move .left).head=.start <;>
    simpa [flag] using SpaceInputTape.left_clamped source.tape

theorem start_return [DecidableEq K] (enumeration : Fin n ≃ K) (program : SpaceMachine.Program K Q)
    (source : SpaceMachine.State K Q) (yes no : Q) :
    SpaceTapeMachine.step enumeration program (lower source (.start yes no))=
      some (configuration (instructionStep (.atStart yes no) source)) := by
  simp only [SpaceTapeMachine.step,lower,Option.map_some,delta]
  congr 1
  simp only [apply,configuration,instructionStep,advance,Option.elim_none,Option.elim_some,Option.map_some,
    Turing.Tape.move_left_right,SpaceInputTape.start]
  cases source.tape.left <;> simp

end Controller.Complexity.SpaceTapeInput
