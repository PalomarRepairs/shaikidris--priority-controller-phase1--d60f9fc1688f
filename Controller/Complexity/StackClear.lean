module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordReader

@[expose] public section

/-! A finite loop erases one selected physical stack and preserves every
other stack. Its running time counts each consumed bit and the final halt. -/
namespace Controller.Complexity.StackClear
open StackMachine
open scoped BigOperators

def program (port : Option K) : Program K (Fin 2) where
  main := 0
  code label := if label=0 then .pop port 1 0 0 else .halt

theorem execution [Fintype K] [DecidableEq K] (input : Option K → List Bool) (port : Option K) (word : List Bool) :
    ∃ peak, Execution (program port) ⟨some (program port).main,Function.update input port word⟩
      ⟨none,Function.update input port []⟩ (word.length+2) peak := by
  induction word with
  | nil =>
    have first : step (program port) ⟨some (program port).main,Function.update input port []⟩=
        some ⟨some 1,Function.update input port []⟩ := by simp [step,program,instructionStep]
    have last : step (program port) ⟨some 1,Function.update input port []⟩=some ⟨none,Function.update input port []⟩ := rfl
    exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩
  | cons bit word ih =>
    obtain ⟨peak,tail⟩ := ih
    have first : step (program port) ⟨some (program port).main,Function.update input port (bit :: word)⟩=
        some ⟨some (program port).main,Function.update input port word⟩ := by
      cases bit <;> simp [step,program,instructionStep]
    exact ⟨_,by simpa only [List.length_cons,Nat.add_right_comm] using Execution.cons first tail⟩

theorem ready_execution [Fintype K] [DecidableEq K] (input : Option K → List Bool) (port : Option K) :
    ∃ peak, Execution (program port) ⟨some (program port).main,input⟩
      ⟨none,Function.update input port []⟩ ((input port).length+2) peak := by
  simpa only [Function.update_eq_self] using execution input port (input port)

theorem resident (port : Option K) : (∑ label, statementSize (tmStatement ((program port).code label))) ≤ 18 := by
  simpa only [Fintype.card_fin,Nat.reduceMul] using finiteTM_resident (program port)

end Controller.Complexity.StackClear
