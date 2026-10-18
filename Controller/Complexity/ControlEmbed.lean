module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.Reductions

@[expose] public section

/-! Renaming finite control labels preserves every physical stack, transition
count and peak. Code compatibility is stated for the actual target program. -/
namespace Controller.Complexity.ControlEmbed
open StackMachine

def instruction (rename : Q → P) : Instruction K Q → Instruction K P
  | .push port bit label => .push port bit (rename label)
  | .pop port empty low high => .pop port (rename empty) (rename low) (rename high)
  | .peek port empty low high => .peek port (rename empty) (rename low) (rename high)
  | .jump label => .jump (rename label)
  | .halt => .halt

def state (rename : Q → P) (input : State K Q) : State K P := ⟨input.pc.map rename,input.stk⟩

theorem instruction_step [DecidableEq K] (rename : Q → P) (code : Instruction K Q) (input : State K Q) :
    instructionStep (instruction rename code) (state rename input)=state rename (instructionStep code input) := by
  cases code with
  | push port bit label => rfl
  | pop port empty low high =>
    cases observed : (input.stk port).head? with
    | none => simp [instruction,instructionStep,state,observed]
    | some bit => cases bit <;> simp [instruction,instructionStep,state,observed]
  | peek port empty low high =>
    cases observed : (input.stk port).head? with
    | none => simp [instruction,instructionStep,state,observed]
    | some bit => cases bit <;> simp [instruction,instructionStep,state,observed]
  | jump label => rfl
  | halt => rfl

theorem step [DecidableEq K] (source : Program K Q) (target : Program K P) (rename : Q → P)
    (compatible : ∀ label, target.code (rename label)=instruction rename (source.code label)) (input : State K Q) :
    StackMachine.step target (state rename input)=(StackMachine.step source input).map (state rename) := by
  cases position : input.pc with
  | none => simp [StackMachine.step,state,position]
  | some label =>
    simp only [StackMachine.step,state,position,Option.map_some,compatible]
    exact congrArg some (instruction_step rename (source.code label) input)

theorem execution [Fintype K] [DecidableEq K] (source : Program K Q) (target : Program K P) (rename : Q → P)
    (compatible : ∀ label, target.code (rename label)=instruction rename (source.code label))
    {input final ticks peak} (trace : Execution source input final ticks peak) :
    Execution target (state rename input) (state rename final) ticks peak := by
  induction trace with
  | refl input => exact Execution.refl _
  | @cons input next final ticks peak transition tail ih =>
    have lifted : StackMachine.step target (state rename input)=some (state rename next) := by rw [step source target rename compatible input,transition]; rfl
    exact Execution.cons lifted ih

end Controller.Complexity.ControlEmbed
