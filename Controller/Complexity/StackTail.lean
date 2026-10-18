module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StackEvaluation

@[expose] public section

/-! Appending an untouched suffix to a stack preserves execution while its
visible prefix stays nonempty. The finite trace checks only this explicit
condition; the suffix can have arbitrary length and contents. -/
namespace Controller.Complexity.StackTail
open StackMachine

def storage [DecidableEq K] (port : Option K) (suffix : List Bool) (data : Option K → List Bool) :=
  Function.update data port (data port++suffix)

def state [DecidableEq K] (port : Option K) (suffix : List Bool) (current : State K Q) : State K Q :=
  ⟨current.pc,storage port suffix current.stk⟩

theorem at_port [DecidableEq K] (port : Option K) (suffix : List Bool) (data : Option K → List Bool) :
    storage port suffix data port=data port++suffix := by simp [storage]

theorem other [DecidableEq K] (port : Option K) (suffix : List Bool) (data : Option K → List Bool)
    {target : Option K} (outside : target ≠ port) : storage port suffix data target=data target := by simp [storage, outside]

theorem update_selected [DecidableEq K] (port : Option K) (suffix : List Bool) (data : Option K → List Bool) (value : List Bool) :
    storage port suffix (Function.update data port value)=Function.update (storage port suffix data) port (value++suffix) := by
  funext target
  by_cases same : target=port <;> simp_all [storage]

theorem update_other [DecidableEq K] (port : Option K) (suffix : List Bool) (data : Option K → List Bool)
    {target : Option K} (outside : target ≠ port) (value : List Bool) :
    storage port suffix (Function.update data target value)=Function.update (storage port suffix data) target value := by
  funext selected
  by_cases hp : selected=port <;> by_cases ht : selected=target <;> simp_all [storage]

theorem instruction_step [DecidableEq K] (port : Option K) (suffix : List Bool) (instruction : Instruction K Q)
    (current : State K Q) (nonempty : current.stk port ≠ []) :
    instructionStep instruction (state port suffix current)=state port suffix (instructionStep instruction current) := by
  cases instruction with
  | push target bit next =>
    by_cases same : target=port
    · subst target
      simp only [instructionStep, state, at_port, update_selected, List.cons_append]
    · simp only [instructionStep, state, other port suffix current.stk same, update_other port suffix current.stk same]
  | pop target empty low high =>
    by_cases same : target=port
    · subst target
      cases contents : current.stk port with
      | nil => exact False.elim (nonempty contents)
      | cons bit rest =>
        simp only [instructionStep, state, at_port, contents, List.cons_append, List.head?_cons,
          List.tail_cons, update_selected]
    · simp only [instructionStep, state, other port suffix current.stk same, update_other port suffix current.stk same]
  | peek target empty low high =>
    by_cases same : target=port
    · subst target
      cases contents : current.stk port with
      | nil => exact False.elim (nonempty contents)
      | cons bit rest => simp only [instructionStep, state, at_port, contents, List.cons_append, List.head?_cons]
    · simp only [instructionStep, state, other port suffix current.stk same]
  | jump next => rfl
  | halt => rfl

theorem step_eq [DecidableEq K] (program : Program K Q) (port : Option K) (suffix : List Bool)
    (current : State K Q) (nonempty : current.stk port ≠ []) :
    step program (state port suffix current)=(step program current).map (state port suffix) := by
  cases position : current.pc with
  | none => simp [step, state, position]
  | some label =>
    simp only [step, state, position, Option.map_some]
    exact congrArg some (instruction_step port suffix (program.code label) current nonempty)

def safe [DecidableEq K] (program : Program K Q) (port : Option K) : Nat → State K Q → Bool
  | 0,current => !(current.stk port).isEmpty
  | fuel+1,current => !(current.stk port).isEmpty && match step program current with
    | none => true
    | some next => safe program port fuel next

theorem eval_state [Fintype K] [DecidableEq K] (program : Program K Q) (port : Option K) (suffix : List Bool)
    (fuel : Nat) (current : State K Q) (safety : safe program port fuel current=true) :
    (StackEvaluation.eval program fuel (state port suffix current)).state=
      state port suffix (StackEvaluation.eval program fuel current).state := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
    have nonempty : current.stk port ≠ [] := by intro empty; simp [safe, empty] at safety
    cases transition : step program current with
    | none => simp only [StackEvaluation.eval, step_eq program port suffix current nonempty, transition, Option.map_none]
    | some next =>
      have tailSafety : safe program port fuel next=true := by
        have both : (!(current.stk port).isEmpty && safe program port fuel next)=true := by simpa only [safe, transition] using safety
        exact (Bool.and_eq_true_iff.mp both).2
      simpa only [StackEvaluation.eval, step_eq program port suffix current nonempty, transition, Option.map_some] using ih next tailSafety

end Controller.Complexity.StackTail
