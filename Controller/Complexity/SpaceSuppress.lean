module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceControl
public import Controller.Complexity.SpaceTM

@[expose] public section

/-! Output suppression executes a jump at every emission. The readable source
state is simulated exactly inside the left work banks. Right work banks and
the external output history are retained, with their full workspace charged.
This is the source-state simulation used by intermediate-bit recomputation. -/
namespace Controller.Complexity.SpaceSuppress
open SpaceMachine
open scoped BigOperators

def instruction : SpaceMachine.Instruction K Q → SpaceMachine.Instruction (K ⊕ J) Q
  | .push port bit next => .push (.inl port) bit next
  | .pop port empty low high => .pop (.inl port) empty low high
  | .peek port empty low high => .peek (.inl port) empty low high
  | .readInput eof low high => .readInput eof low high
  | .atStart yes no => .atStart yes no
  | .left next => .left next
  | .right next => .right next
  | .emit _ next => .jump next
  | .jump next => .jump next
  | .halt => .halt

def program (source : SpaceMachine.Program K Q) : SpaceMachine.Program (K ⊕ J) Q :=
  ⟨source.main,fun label => instruction (source.code label)⟩

def state (frame : J → List Bool) (output : List Bool) (source : SpaceMachine.State K Q) : SpaceMachine.State (K ⊕ J) Q :=
  ⟨source.pc,source.tape,Sum.elim source.work frame,output⟩

theorem work_update [DecidableEq K] [DecidableEq J] (bank : K → List Bool) (frame : J → List Bool)
    (port : K) (bits : List Bool) :
    Sum.elim (Function.update bank port bits) frame=Function.update (Sum.elim bank frame) (.inl port) bits := by
  funext target
  cases target with
  | inl target => simp [Function.update_apply]
  | inr target => simp

theorem instruction_step [DecidableEq K] [DecidableEq J] (frame : J → List Bool) (output : List Bool)
    (code : SpaceMachine.Instruction K Q) (source : SpaceMachine.State K Q) :
    instructionStep (instruction code) (state frame output source)=
      state frame output (instructionStep code source) := by
  cases code with
  | push port bit next =>
    simp only [instruction,instructionStep,advance,state,Sum.elim_inl,work_update]
  | pop port empty low high =>
    simp only [instruction,instructionStep,advance,state,Sum.elim_inl,work_update]
  | peek port empty low high => rfl
  | readInput eof low high => rfl
  | atStart yes no => rfl
  | left next => rfl
  | right next => rfl
  | emit bit next => rfl
  | jump next => rfl
  | halt => rfl

theorem step [DecidableEq K] [DecidableEq J] (frame : J → List Bool) (output : List Bool)
    (source : SpaceMachine.Program K Q) (input : SpaceMachine.State K Q) :
    SpaceMachine.step (program (J:=J) source) (state frame output input)=
      (SpaceMachine.step source input).map (state frame output) := by
  cases position : input.pc with
  | none => simp [SpaceMachine.step,state,position]
  | some label =>
    simp only [SpaceMachine.step,state,position,Option.map_some,program]
    exact congrArg some (instruction_step frame output (source.code label) input)

theorem workspace_state [Fintype K] [Fintype J] (frame : J → List Bool) (output : List Bool)
    (source : SpaceMachine.State K Q) :
    workspace (state frame output source)=workspace source+∑ port, (frame port).length := by
  simp [workspace,state,Fintype.sum_sum_type]

theorem execution [Fintype K] [Fintype J] [DecidableEq K] [DecidableEq J]
    (frame : J → List Bool) (output : List Bool) {source : SpaceMachine.Program K Q} {input final ticks peak}
    (trace : SpaceMachine.Execution source input final ticks peak) :
    SpaceMachine.Execution (program (J:=J) source) (state frame output input) (state frame output final)
      ticks (peak+∑ port, (frame port).length) := by
  induction trace with
  | refl input => simpa only [workspace_state] using Execution.refl (program:=program source) (state frame output input)
  | @cons input next final ticks peak actual rest ih =>
    have compiled := step frame output source input
    rw [actual] at compiled
    have mass : max (workspace input+∑ port, (frame port).length) (peak+∑ port, (frame port).length)=
        max (workspace input) peak+∑ port, (frame port).length := by omega
    simpa only [workspace_state,mass] using Execution.cons compiled ih

end Controller.Complexity.SpaceSuppress
