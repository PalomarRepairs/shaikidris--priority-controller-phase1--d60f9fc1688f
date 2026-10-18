module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.GuardedLink

@[expose] public section

/-! A unary-counted loop executes one fixed finite body. Each true count bit
is consumed by a charged transition. The body's actual error predicate guards
the backedge; a false count bit sets an error marker before halting. -/
namespace Controller.Complexity.CountLoop
open StackMachine

def program (body : Program K Q) (counter guard : Option K) (accept : Option Bool → Bool) :
    Program K (Q ⊕ Option (Fin 2)) where
  main := .inr (some 0)
  code label := match label with
    | .inl label => GuardedLink.leftInstruction guard (0 : Fin 2) accept (body.code label)
    | .inr none => .halt
    | .inr (some label) => if label=0 then
        .pop counter (.inr none) (.inr (some 1)) (.inl body.main)
      else .push guard false (.inr none)

theorem body_step [DecidableEq K] (body : Program K Q) (counter guard : Option K)
    (accept : Option Bool → Bool) {state next} (transition : step body state = some next) :
    step (program body counter guard accept) (GuardedLink.leftState guard (0 : Fin 2) accept state) =
      some (GuardedLink.leftState guard (0 : Fin 2) accept next) := by
  cases position : state.pc with
  | none => simp [step, position] at transition
  | some label =>
    have next_eq : instructionStep (body.code label) state = next := by simpa [step, position] using transition
    simp only [step, GuardedLink.leftState, position, Option.elim_some, program]
    exact congrArg some ((GuardedLink.leftInstruction_step guard (0 : Fin 2) accept (body.code label) state).trans
      (congrArg (GuardedLink.leftState guard (0 : Fin 2) accept) next_eq))

theorem body_execution [Fintype K] [DecidableEq K] {body : Program K Q} (counter guard : Option K)
    (accept : Option Bool → Bool) {state final ticks peak} (trace : Execution body state final ticks peak) :
    Execution (program body counter guard accept) (GuardedLink.leftState guard (0 : Fin 2) accept state)
      (GuardedLink.leftState guard (0 : Fin 2) accept final) ticks peak := by
  induction trace with
  | refl state => exact Execution.refl _
  | cons transition tail ih => exact Execution.cons (body_step body counter guard accept transition) ih

theorem empty [Fintype K] [DecidableEq K] (body : Program K Q) (counter guard : Option K)
    (accept : Option Bool → Bool) (data : Option K → List Bool) (exhausted : data counter = []) :
    Execution (program body counter guard accept) ⟨some (program body counter guard accept).main,data⟩
      ⟨none,data⟩ 2 (live (⟨none,data⟩ : State K (Q ⊕ Option (Fin 2)))) := by
  have restored : Function.update data counter [] = data := by
    funext target
    by_cases same : target=counter <;> simp_all
  have first : step (program body counter guard accept) ⟨some (program body counter guard accept).main,data⟩ =
      some ⟨some (.inr none),data⟩ := by simp [step, program, instructionStep, exhausted, restored]
  have last : step (program body counter guard accept) (⟨some (.inr none),data⟩ : State K _) = some ⟨none,data⟩ := rfl
  simpa only [live, Nat.max_self] using Execution.cons first (Execution.cons last (Execution.refl _))

theorem next [Fintype K] [DecidableEq K] {body : Program K Q} (counter guard : Option K)
    (accept : Option Bool → Bool) {input middle output : Option K → List Bool} {rest : List Bool}
    {bodyTicks bodyPeak tailTicks tailPeak}
    (counted : input counter = true :: rest)
    (bodyRun : Execution body ⟨some body.main,Function.update input counter rest⟩ ⟨none,middle⟩ bodyTicks bodyPeak)
    (accepted : accept (middle guard).head? = true)
    (tailRun : Execution (program body counter guard accept)
      ⟨some (program body counter guard accept).main,middle⟩ ⟨none,output⟩ tailTicks tailPeak) :
    ∃ peak, Execution (program body counter guard accept)
      ⟨some (program body counter guard accept).main,input⟩ ⟨none,output⟩ (bodyTicks+tailTicks+1) peak := by
  have lifted := body_execution counter guard accept bodyRun
  have boundary : GuardedLink.leftState guard (0 : Fin 2) accept (⟨none,middle⟩ : State K Q) =
      (⟨some (program body counter guard accept).main,middle⟩ : State K _) := by
    simp [GuardedLink.leftState, GuardedLink.exitLabel, accepted, program]
  rw [boundary] at lifted
  have entry : step (program body counter guard accept) ⟨some (program body counter guard accept).main,input⟩ =
      some (GuardedLink.leftState guard (0 : Fin 2) accept ⟨some body.main,Function.update input counter rest⟩) := by
    simp [step, program, instructionStep, counted, GuardedLink.leftState]
  exact ⟨_,Execution.cons entry (lifted.append tailRun)⟩

theorem reject [Fintype K] [DecidableEq K] {body : Program K Q} (counter guard : Option K)
    (accept : Option Bool → Bool) {input middle : Option K → List Bool} {rest : List Bool} {ticks peak}
    (counted : input counter = true :: rest)
    (bodyRun : Execution body ⟨some body.main,Function.update input counter rest⟩ ⟨none,middle⟩ ticks peak)
    (rejected : accept (middle guard).head? = false) :
    ∃ fullPeak, Execution (program body counter guard accept)
      ⟨some (program body counter guard accept).main,input⟩ ⟨none,middle⟩ (ticks+2) fullPeak := by
  have lifted := body_execution counter guard accept bodyRun
  have boundary : GuardedLink.leftState guard (0 : Fin 2) accept (⟨none,middle⟩ : State K Q) =
      (⟨some (.inr none),middle⟩ : State K (Q ⊕ Option (Fin 2))) := by
    simp [GuardedLink.leftState, GuardedLink.exitLabel, rejected]
  rw [boundary] at lifted
  have entry : step (program body counter guard accept) ⟨some (program body counter guard accept).main,input⟩ =
      some (GuardedLink.leftState guard (0 : Fin 2) accept ⟨some body.main,Function.update input counter rest⟩) := by
    simp [step, program, instructionStep, counted, GuardedLink.leftState]
  have last : step (program body counter guard accept) (⟨some (.inr none),middle⟩ : State K _) = some ⟨none,middle⟩ := rfl
  have trace := Execution.cons entry (lifted.append (Execution.cons last (Execution.refl _)))
  simpa only [Nat.add_assoc] using Exists.intro _ trace

end Controller.Complexity.CountLoop
