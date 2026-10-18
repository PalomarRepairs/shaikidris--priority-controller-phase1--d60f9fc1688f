module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.Reductions

@[expose] public section

/-! Bounded evaluation produces a literal stack-machine execution. Fuel only
limits observation: the soundness theorem does not assume that the resulting
state is halted. Finite control blocks can prove halting by checking that
actual endpoint separately. -/
namespace Controller.Complexity.StackEvaluation
open StackMachine

structure Result (K Q : Type) where
  state : State K Q
  ticks : Nat
  peak : Nat

def eval [Fintype K] [DecidableEq K] (program : Program K Q) : Nat → State K Q → Result K Q
  | 0,state => ⟨state,0,live state⟩
  | fuel+1,state => match step program state with
    | none => ⟨state,0,live state⟩
    | some next =>
      let result := eval program fuel next
      ⟨result.state,result.ticks+1,max (live state) result.peak⟩

theorem sound [Fintype K] [DecidableEq K] (program : Program K Q) (fuel : Nat) (state : State K Q) :
    Execution program state (eval program fuel state).state (eval program fuel state).ticks (eval program fuel state).peak := by
  induction fuel generalizing state with
  | zero => exact Execution.refl state
  | succ fuel ih =>
    cases transition : step program state with
    | none => simpa only [eval, transition] using Execution.refl (program := program) state
    | some next => simpa only [eval, transition] using Execution.cons transition (ih next)

theorem ticks_le [Fintype K] [DecidableEq K] (program : Program K Q) (fuel : Nat) (state : State K Q) :
    (eval program fuel state).ticks ≤ fuel := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases transition : step program state with
    | none => simp only [eval, transition]; omega
    | some next => simpa only [eval, transition, Nat.add_le_add_iff_right] using ih next

end Controller.Complexity.StackEvaluation
