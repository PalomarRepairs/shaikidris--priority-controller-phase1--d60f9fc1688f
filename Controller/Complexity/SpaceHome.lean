module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMachine

@[expose] public section

/-! Executed rewind of the read-only input head. Each already passed bit
moves back across the head; no work bank or output bit changes. -/
namespace Controller.Complexity.SpaceHome
open SpaceMachine

def program : SpaceMachine.Program K (Fin 3) where
  main := 0
  code label := match label.val with
    | 0 => .atStart 2 1
    | 1 => .left 0
    | _ => .halt

def state (work : K → List Bool) (output : List Bool) (pc : Option (Fin 3)) (left right : List Bool) :
    SpaceMachine.State K (Fin 3) := ⟨pc,⟨left,right⟩,work,output⟩

theorem workspace_state [Fintype K] (work : K → List Bool) (output : List Bool) (pc : Option (Fin 3)) (left right : List Bool) :
    workspace (state work output pc left right)=∑ port, (work port).length := rfl

theorem empty_step [DecidableEq K] (work : K → List Bool) (output right : List Bool) :
    step program (state work output (some 0) [] right)=some (state work output (some 2) [] right) := rfl

theorem nonempty_step [DecidableEq K] (work : K → List Bool) (output left right : List Bool) (bit : Bool) :
    step program (state work output (some 0) (bit :: left) right)=some (state work output (some 1) (bit :: left) right) := rfl

theorem move_step [DecidableEq K] (work : K → List Bool) (output left right : List Bool) (bit : Bool) :
    step program (state work output (some 1) (bit :: left) right)=some (state work output (some 0) left (bit :: right)) := rfl

theorem halt_step [DecidableEq K] (work : K → List Bool) (output right : List Bool) :
    step program (state work output (some 2) [] right)=some (state work output none [] right) := rfl

theorem head_execution [Fintype K] [DecidableEq K] (work : K → List Bool) (output left right : List Bool) :
    SpaceMachine.Execution program (state work output (some (program (K := K)).main) left right)
      (state work output none [] (left.reverse++right)) (2*left.length+2) (∑ port, (work port).length) := by
  induction left generalizing right with
  | nil =>
    have actual := Execution.cons (empty_step work output right)
      (Execution.cons (halt_step work output right) (Execution.refl _))
    simpa only [program,List.length_nil,List.reverse_nil,List.nil_append,workspace_state,Nat.max_self] using actual
  | cons bit left ih =>
    have actual := Execution.cons (nonempty_step work output left right bit)
      (Execution.cons (move_step work output left right bit) (ih (bit :: right)))
    have result : left.reverse++bit :: right=(bit :: left).reverse++right := by simp [List.append_assoc]
    rw [result] at actual
    convert actual using 1 <;>
      simp only [program,workspace_state,Nat.max_self]

theorem execution [Fintype K] [DecidableEq K] (input : SpaceMachine.State K (Fin 3)) (entry : input.pc=some (program (K := K)).main) :
    SpaceMachine.Execution program input
      ⟨none,ReadOnlyInput.start (ReadOnlyInput.word input.tape),input.work,input.output⟩
      (2*input.tape.left.length+2) (workspace input) := by
  have actual := head_execution input.work input.output input.tape.left input.tape.right
  have ready : state input.work input.output (some (program (K := K)).main) input.tape.left input.tape.right=input := by
    cases input with
    | mk pc tape work output => cases tape; cases entry; rfl
  rw [ready] at actual
  exact actual

end Controller.Complexity.SpaceHome
