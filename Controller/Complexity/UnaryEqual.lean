module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StackFrames

@[expose] public section

/-! A finite comparator consumes two unary counts and publishes equality.
Both count banks are cleared after either outcome. The third bank is the
status flag, initially empty, and every transition is charged. -/
namespace Controller.Complexity.UnaryEqual
open StackMachine StackBlocks
open scoped BigOperators

def program : Program Bool (Fin 7) where
  main := 0
  code label := match label.val with
    | 0 => .pop none 2 3 1
    | 1 => .pop (some false) 3 3 0
    | 2 => .peek (some false) 6 3 3
    | 3 => .push (some true) false 4
    | 4 => .pop none 5 4 4
    | 5 => .pop (some false) 6 5 5
    | _ => .halt

def state (label : Option (Fin 7)) (left right status : List Bool) : State Bool (Fin 7) :=
  ⟨label,layout left right status⟩

theorem left_update (left right status replacement : List Bool) :
    Function.update (layout left right status) none replacement=layout replacement right status := by
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem right_update (left right status replacement : List Bool) :
    Function.update (layout left right status) (some false) replacement=layout left replacement status := by
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem status_update (left right status replacement : List Bool) :
    Function.update (layout left right status) (some true) replacement=layout left right replacement := by
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem clear_right (right status : List Bool) :
    ∃ peak, Execution program (state (some 5) [] right status) (state none [] [] status) (right.length+2) peak := by
  induction right with
  | nil =>
    have first : step program (state (some 5) [] [] status)=some (state (some 6) [] [] status) := by
      simp [step,program,instructionStep,state,layout,right_update]
    have last : step program (state (some 6) [] [] status)=some (state none [] [] status) := rfl
    exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩
  | cons bit right ih =>
    obtain ⟨peak,tail⟩ := ih
    have first : step program (state (some 5) [] (bit :: right) status)=some (state (some 5) [] right status) := by
      cases bit <;> simp [step,program,instructionStep,state,layout,right_update]
    exact ⟨_,by simpa only [List.length_cons,Nat.add_right_comm] using Execution.cons first tail⟩

theorem clear_left (left right status : List Bool) :
    ∃ peak, Execution program (state (some 4) left right status) (state none [] [] status) (left.length+right.length+3) peak := by
  induction left with
  | nil =>
    obtain ⟨peak,tail⟩ := clear_right right status
    have first : step program (state (some 4) [] right status)=some (state (some 5) [] right status) := by
      simp [step,program,instructionStep,state,layout,left_update]
    exact ⟨_,by simpa only [List.length_nil,Nat.zero_add,Nat.add_assoc] using Execution.cons first tail⟩
  | cons bit left ih =>
    obtain ⟨peak,tail⟩ := ih
    have first : step program (state (some 4) (bit :: left) right status)=some (state (some 4) left right status) := by
      cases bit <;> simp [step,program,instructionStep,state,layout,left_update]
    have ticks : (left.length+right.length+3)+1=(bit :: left).length+right.length+3 := by simp only [List.length_cons]; omega
    exact ⟨_,by simpa only [ticks] using Execution.cons first tail⟩

theorem execution (left right : Nat) :
    ∃ ticks peak, Execution program (state (some program.main) (List.replicate left true) (List.replicate right true) [])
      (state none [] [] (if left=right then [] else [false])) ticks peak ∧ ticks ≤ left+right+6 := by
  induction left generalizing right with
  | zero =>
    cases right with
    | zero =>
      have first : step program (state (some 0) [] [] [])=some (state (some 2) [] [] []) := by
        simp [step,program,instructionStep,state,layout,left_update]
      have second : step program (state (some 2) [] [] [])=some (state (some 6) [] [] []) := rfl
      have last : step program (state (some 6) [] [] [])=some (state none [] [] []) := rfl
      exact ⟨3,_,Execution.cons first (Execution.cons second (Execution.cons last (Execution.refl _))),by decide⟩
    | succ right =>
      obtain ⟨peak,tail⟩ := clear_left [] (List.replicate (right+1) true) [false]
      have first : step program (state (some 0) [] (List.replicate (right+1) true) [])=
          some (state (some 2) [] (List.replicate (right+1) true) []) := by
        simp [step,program,instructionStep,state,layout,left_update]
      have second : step program (state (some 2) [] (List.replicate (right+1) true) [])=
          some (state (some 3) [] (List.replicate (right+1) true) []) := rfl
      have flag : step program (state (some 3) [] (List.replicate (right+1) true) [])=
          some (state (some 4) [] (List.replicate (right+1) true) [false]) := by
        simp [step,program,instructionStep,state,layout,status_update]
      have trace := Execution.cons first (Execution.cons second (Execution.cons flag tail))
      exact ⟨_,_,by simpa only [program,state,List.replicate_zero,show ¬0=right+1 by omega,ite_false] using trace,
        by simp only [List.length_nil,List.length_replicate]; omega⟩
  | succ left ih =>
    cases right with
    | zero =>
      obtain ⟨peak,tail⟩ := clear_left (List.replicate left true) [] [false]
      have first : step program (state (some 0) (List.replicate (left+1) true) [] [])=
          some (state (some 1) (List.replicate left true) [] []) := by
        simp [step,program,instructionStep,state,layout,left_update,List.replicate_succ]
      have second : step program (state (some 1) (List.replicate left true) [] [])=
          some (state (some 3) (List.replicate left true) [] []) := by
        simp [step,program,instructionStep,state,layout,right_update]
      have flag : step program (state (some 3) (List.replicate left true) [] [])=
          some (state (some 4) (List.replicate left true) [] [false]) := by
        simp [step,program,instructionStep,state,layout,status_update]
      have trace := Execution.cons first (Execution.cons second (Execution.cons flag tail))
      exact ⟨_,_,by simpa only [program,state,List.replicate_zero,show ¬left+1=0 by omega,ite_false] using trace,
        by simp only [List.length_nil,List.length_replicate]; omega⟩
    | succ right =>
      obtain ⟨ticks,peak,tail,bound⟩ := ih right
      have first : step program (state (some 0) (List.replicate (left+1) true) (List.replicate (right+1) true) [])=
          some (state (some 1) (List.replicate left true) (List.replicate (right+1) true) []) := by
        simp [step,program,instructionStep,state,layout,left_update,List.replicate_succ]
      have second : step program (state (some 1) (List.replicate left true) (List.replicate (right+1) true) [])=
          some (state (some 0) (List.replicate left true) (List.replicate right true) []) := by
        simp [step,program,instructionStep,state,layout,right_update,List.replicate_succ]
      have trace := Execution.cons first (Execution.cons second tail)
      have same : (left+1=right+1) ↔ left=right := by omega
      exact ⟨ticks+2,_,by simpa only [program,state,same,Nat.add_assoc] using trace,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 63 := by
  simpa only [Fintype.card_fin,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.UnaryEqual
