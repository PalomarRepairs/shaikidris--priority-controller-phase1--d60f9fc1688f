module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTM

@[expose] public section

/-! Relocation of a two-work-stack transducer into an arbitrary finite work
bank. Unselected work bits form a preserved frame; input tape and output retain
their source semantics. Actual execution time is unchanged and workspace adds. -/
namespace Controller.Complexity.SpaceFrames
open SpaceMachine
open scoped BigOperators

def twoPorts (first second : K) (different : first ≠ second) : Bool ↪ K where
  toFun bit := if bit then second else first
  inj' := by intro a b same; cases a <;> cases b <;> simp_all

def embedWork [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool) (bank : Bool → List Bool) (target : K) :=
  if target=ports false then bank false else if target=ports true then bank true else frame target

theorem embedWork_at [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool)
    (bank : Bool → List Bool) (port : Bool) : embedWork ports frame bank (ports port)=bank port := by
  cases port <;> simp [embedWork,ports.injective.eq_iff]

theorem embedWork_other [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool)
    (bank : Bool → List Bool) (target : K) (outside : ∀ port, target ≠ ports port) :
    embedWork ports frame bank target=frame target := by simp [embedWork,outside]

theorem embedWork_update [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool)
    (bank : Bool → List Bool) (port : Bool) (bits : List Bool) :
    embedWork ports frame (Function.update bank port bits)=Function.update (embedWork ports frame bank) (ports port) bits := by
  funext target
  by_cases mapped : ∃ selected, target=ports selected
  · obtain ⟨selected,rfl⟩ := mapped
    simp only [embedWork_at,Function.update_apply,ports.injective.eq_iff]
  · have outside : ∀ selected, target ≠ ports selected := by simpa using mapped
    simp [embedWork_other ports frame _ target outside,outside]

def embedState [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool) (state : SpaceMachine.State Bool Q) :
    SpaceMachine.State K Q := ⟨state.pc,state.tape,embedWork ports frame state.work,state.output⟩

def instruction (ports : Bool ↪ K) : SpaceMachine.Instruction Bool Q → SpaceMachine.Instruction K Q
  | .push port bit label => .push (ports port) bit label
  | .pop port empty low high => .pop (ports port) empty low high
  | .peek port empty low high => .peek (ports port) empty low high
  | .readInput eof low high => .readInput eof low high
  | .atStart yes no => .atStart yes no
  | .left label => .left label
  | .right label => .right label
  | .emit bit label => .emit bit label
  | .jump label => .jump label
  | .halt => .halt

def relocate (ports : Bool ↪ K) (program : SpaceMachine.Program Bool Q) : SpaceMachine.Program K Q :=
  ⟨program.main,fun label => instruction ports (program.code label)⟩

theorem instruction_step [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool)
    (code : SpaceMachine.Instruction Bool Q) (state : SpaceMachine.State Bool Q) :
    instructionStep (instruction ports code) (embedState ports frame state)=embedState ports frame (instructionStep code state) := by
  cases code with
  | push port bit label => simp [instruction,instructionStep,advance,embedState,embedWork_at,embedWork_update]
  | pop port empty low high => simp [instruction,instructionStep,advance,embedState,embedWork_at,embedWork_update]
  | peek port empty low high => simp [instruction,instructionStep,advance,embedState,embedWork_at]
  | readInput eof low high => rfl
  | atStart yes no => rfl
  | left label => rfl
  | right label => rfl
  | emit bit label => rfl
  | jump label => rfl
  | halt => rfl

theorem step [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool)
    (program : SpaceMachine.Program Bool Q) (state : SpaceMachine.State Bool Q) :
    SpaceMachine.step (relocate ports program) (embedState ports frame state)=
      (SpaceMachine.step program state).map (embedState ports frame) := by
  cases position : state.pc with
  | none => simp [SpaceMachine.step,embedState,position]
  | some label =>
    simp only [SpaceMachine.step,embedState,position,Option.map_some,relocate]
    exact congrArg some (instruction_step ports frame (program.code label) state)

def frameBits [Fintype K] [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool) :=
  ∑ target, (embedWork ports frame (fun _ => []) target).length

theorem cell_length [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool)
    (bank : Bool → List Bool) (target : K) :
    (embedWork ports frame bank target).length=(embedWork ports frame (fun _ => []) target).length+
      (if target=ports false then (bank false).length else 0)+(if target=ports true then (bank true).length else 0) := by
  by_cases first : target=ports false
  · subst target
    simp [embedWork,ports.injective.eq_iff]
  · by_cases second : target=ports true
    · subst target
      simp [embedWork,ports.injective.eq_iff]
    · simp [embedWork,first,second]

theorem workspace_embed [Fintype K] [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool)
    (state : SpaceMachine.State Bool Q) :
    workspace (embedState ports frame state)=workspace state+frameBits ports frame := by
  calc
    _ = ∑ target, ((embedWork ports frame (fun _ => []) target).length+
        (if target=ports false then (state.work false).length else 0)+
        (if target=ports true then (state.work true).length else 0)) :=
      Finset.sum_congr rfl fun target _ => cell_length ports frame state.work target
    _ = frameBits ports frame+(state.work false).length+(state.work true).length := by
      simp [Finset.sum_add_distrib,frameBits]
    _ = _ := by simp [workspace,Nat.add_comm,Nat.add_assoc]

theorem execution [Fintype K] [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool)
    {program : SpaceMachine.Program Bool Q} {state final ticks peak}
    (trace : SpaceMachine.Execution program state final ticks peak) :
    SpaceMachine.Execution (relocate ports program) (embedState ports frame state) (embedState ports frame final)
      ticks (peak+frameBits ports frame) := by
  induction trace with
  | refl state => simpa only [workspace_embed] using Execution.refl (program := relocate ports program) (embedState ports frame state)
  | @cons state middle final ticks peak actual rest ih =>
    have compiled : SpaceMachine.step (relocate ports program) (embedState ports frame state)=some (embedState ports frame middle) := by
      rw [step,actual]
      rfl
    have mass : max (workspace state+frameBits ports frame) (peak+frameBits ports frame)=
        max (workspace state) peak+frameBits ports frame := by omega
    simpa only [workspace_embed,mass] using Execution.cons compiled ih

theorem ready_work [DecidableEq K] (ports : Bool ↪ K) (frame : K → List Bool) :
    embedWork ports frame (fun port => frame (ports port))=frame := by
  funext target
  by_cases mapped : ∃ port, target=ports port
  · obtain ⟨port,rfl⟩ := mapped
    exact embedWork_at ports frame _ port
  · have outside : ∀ port, target ≠ ports port := by simpa using mapped
    exact embedWork_other ports frame _ target outside

end Controller.Complexity.SpaceFrames
