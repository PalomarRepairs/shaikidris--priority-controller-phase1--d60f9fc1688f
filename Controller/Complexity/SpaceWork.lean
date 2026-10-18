module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTM
public import Controller.Complexity.StackFrames

@[expose] public section

/-! Three-port binary stack routines realized inside selected work banks of
a read-only-input/write-only-output transducer. The stack routine's shared
port is an ordinary work bank here; it has no access to external input/output. -/
namespace Controller.Complexity.SpaceWork
open scoped BigOperators

def threePorts (first second third : K) (firstSecond : first ≠ second) (firstThird : first ≠ third)
    (secondThird : second ≠ third) : Option Bool ↪ K where
  toFun port := match port with | none => first | some false => second | some true => third
  inj' := by
    intro a b same
    cases a with
    | none => cases b with
      | none => rfl
      | some bit => cases bit <;> simp_all
    | some bit => cases bit <;> cases b with
      | none => simp_all
      | some other => cases other <;> simp_all

def embedWork [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (bank : Option Bool → List Bool) (target : K) :=
  if target=ports none then bank none
  else if target=ports (some false) then bank (some false)
  else if target=ports (some true) then bank (some true)
  else frame target

theorem embedWork_at [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (bank : Option Bool → List Bool) (port : Option Bool) : embedWork ports frame bank (ports port)=bank port := by
  cases port with
  | none => simp [embedWork]
  | some bit => cases bit <;> simp [embedWork,ports.injective.eq_iff]

theorem embedWork_other [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (bank : Option Bool → List Bool) (target : K) (outside : ∀ port, target ≠ ports port) :
    embedWork ports frame bank target=frame target := by simp [embedWork,outside]

theorem embedWork_update [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (bank : Option Bool → List Bool) (port : Option Bool) (bits : List Bool) :
    embedWork ports frame (Function.update bank port bits)=Function.update (embedWork ports frame bank) (ports port) bits := by
  funext target
  by_cases mapped : ∃ selected, target=ports selected
  · obtain ⟨selected,rfl⟩ := mapped
    simp only [embedWork_at,Function.update_apply,ports.injective.eq_iff]
  · have outside : ∀ selected, target ≠ ports selected := by simpa using mapped
    simp [embedWork_other ports frame _ target outside,outside]

def embedState [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (tape : ReadOnlyInput.Tape) (output : List Bool) (state : StackMachine.State Bool Q) : SpaceMachine.State K Q :=
  ⟨state.pc,tape,embedWork ports frame state.stk,output⟩

def instruction (ports : Option Bool ↪ K) : StackMachine.Instruction Bool Q → SpaceMachine.Instruction K Q
  | .push port bit label => .push (ports port) bit label
  | .pop port empty low high => .pop (ports port) empty low high
  | .peek port empty low high => .peek (ports port) empty low high
  | .jump label => .jump label
  | .halt => .halt

def program (ports : Option Bool ↪ K) (source : StackMachine.Program Bool Q) : SpaceMachine.Program K Q :=
  ⟨source.main,fun label => instruction ports (source.code label)⟩

theorem instruction_step [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (tape : ReadOnlyInput.Tape) (output : List Bool) (code : StackMachine.Instruction Bool Q) (state : StackMachine.State Bool Q) :
    SpaceMachine.instructionStep (instruction ports code) (embedState ports frame tape output state)=
      embedState ports frame tape output (StackMachine.instructionStep code state) := by
  cases code with
  | push port bit label =>
    simp [instruction,SpaceMachine.instructionStep,SpaceMachine.advance,StackMachine.instructionStep,embedState,embedWork_at,embedWork_update]
  | pop port empty low high =>
    cases observed : (state.stk port).head? with
    | none => simp [instruction,SpaceMachine.instructionStep,SpaceMachine.advance,SpaceMachine.observed,StackMachine.instructionStep,embedState,embedWork_at,embedWork_update,observed]
    | some bit => cases bit <;> simp [instruction,SpaceMachine.instructionStep,SpaceMachine.advance,SpaceMachine.observed,StackMachine.instructionStep,embedState,embedWork_at,embedWork_update,observed]
  | peek port empty low high =>
    cases observed : (state.stk port).head? with
    | none => simp [instruction,SpaceMachine.instructionStep,SpaceMachine.advance,SpaceMachine.observed,StackMachine.instructionStep,embedState,embedWork_at,observed]
    | some bit => cases bit <;> simp [instruction,SpaceMachine.instructionStep,SpaceMachine.advance,SpaceMachine.observed,StackMachine.instructionStep,embedState,embedWork_at,observed]
  | jump label => rfl
  | halt => rfl

theorem step [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (tape : ReadOnlyInput.Tape) (output : List Bool) (source : StackMachine.Program Bool Q) (state : StackMachine.State Bool Q) :
    SpaceMachine.step (program ports source) (embedState ports frame tape output state)=
      (StackMachine.step source state).map (embedState ports frame tape output) := by
  cases position : state.pc with
  | none => simp [SpaceMachine.step,StackMachine.step,embedState,position]
  | some label =>
    simp only [SpaceMachine.step,StackMachine.step,embedState,position,Option.map_some,program]
    exact congrArg some (instruction_step ports frame tape output (source.code label) state)

def frameBits [Fintype K] [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool) :=
  ∑ target, (embedWork ports frame (fun _ => []) target).length

theorem cell_length [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (bank : Option Bool → List Bool) (target : K) :
    (embedWork ports frame bank target).length=(embedWork ports frame (fun _ => []) target).length+
      (if target=ports none then (bank none).length else 0)+
      (if target=ports (some false) then (bank (some false)).length else 0)+
      (if target=ports (some true) then (bank (some true)).length else 0) := by
  by_cases first : target=ports none
  · subst target
    simp [embedWork,ports.injective.eq_iff]
  · by_cases second : target=ports (some false)
    · subst target
      simp [embedWork,ports.injective.eq_iff]
    · by_cases third : target=ports (some true)
      · subst target
        simp [embedWork,ports.injective.eq_iff]
      · simp [embedWork,first,second,third]

theorem workspace_embed [Fintype K] [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (tape : ReadOnlyInput.Tape) (output : List Bool) (state : StackMachine.State Bool Q) :
    SpaceMachine.workspace (embedState ports frame tape output state)=StackMachine.live state+frameBits ports frame := by
  calc
    _ = ∑ target, ((embedWork ports frame (fun _ => []) target).length+
        (if target=ports none then (state.stk none).length else 0)+
        (if target=ports (some false) then (state.stk (some false)).length else 0)+
        (if target=ports (some true) then (state.stk (some true)).length else 0)) :=
      Finset.sum_congr rfl fun target _ => cell_length ports frame state.stk target
    _ = frameBits ports frame+(state.stk none).length+(state.stk (some false)).length+(state.stk (some true)).length := by
      simp [Finset.sum_add_distrib,frameBits]
    _ = _ := by simp [StackMachine.live,Fintype.sum_option,Nat.add_comm,Nat.add_assoc]

theorem execution [Fintype K] [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (tape : ReadOnlyInput.Tape) (output : List Bool) {source : StackMachine.Program Bool Q} {state final ticks peak}
    (trace : StackMachine.Execution source state final ticks peak) :
    SpaceMachine.Execution (program ports source) (embedState ports frame tape output state)
      (embedState ports frame tape output final) ticks (peak+frameBits ports frame) := by
  induction trace with
  | refl state => simpa only [workspace_embed] using SpaceMachine.Execution.refl (program := program ports source) (embedState ports frame tape output state)
  | @cons state middle final ticks peak actual rest ih =>
    have compiled : SpaceMachine.step (program ports source) (embedState ports frame tape output state)=some (embedState ports frame tape output middle) := by
      rw [step,actual]
      rfl
    have mass : max (StackMachine.live state+frameBits ports frame) (peak+frameBits ports frame)=
        max (StackMachine.live state) peak+frameBits ports frame := by omega
    simpa only [workspace_embed,mass] using SpaceMachine.Execution.cons compiled ih

theorem ready_work [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool) :
    embedWork ports frame (fun port => frame (ports port))=frame := by
  funext target
  by_cases mapped : ∃ port, target=ports port
  · obtain ⟨port,rfl⟩ := mapped
    exact embedWork_at ports frame _ port
  · have outside : ∀ port, target ≠ ports port := by simpa using mapped
    exact embedWork_other ports frame _ target outside

end Controller.Complexity.SpaceWork
