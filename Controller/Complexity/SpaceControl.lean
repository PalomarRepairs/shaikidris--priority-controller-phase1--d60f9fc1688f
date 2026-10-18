module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMachine

@[expose] public section

/-! Finite control-label relocation, optionally replacing a block halt by a
physical continuation jump. All input, work and output data cross the boundary
unchanged; source ticks and actual workspace peaks are preserved. -/
namespace Controller.Complexity.SpaceControl
open SpaceMachine

def instruction (rename : Q → P) (ending : Option P) : SpaceMachine.Instruction K Q → SpaceMachine.Instruction K P
  | .push port bit label => .push port bit (rename label)
  | .pop port empty low high => .pop port (rename empty) (rename low) (rename high)
  | .peek port empty low high => .peek port (rename empty) (rename low) (rename high)
  | .readInput eof low high => .readInput (rename eof) (rename low) (rename high)
  | .atStart yes no => .atStart (rename yes) (rename no)
  | .left label => .left (rename label)
  | .right label => .right (rename label)
  | .emit bit label => .emit bit (rename label)
  | .jump label => .jump (rename label)
  | .halt => match ending with | none => .halt | some label => .jump label

def state (rename : Q → P) (ending : Option P) (source : SpaceMachine.State K Q) : SpaceMachine.State K P :=
  ⟨source.pc.elim ending (some ∘ rename),source.tape,source.work,source.output⟩

theorem observed_map (rename : Q → P) (empty low high : Q) (bit : Option Bool) :
    observed (rename empty) (rename low) (rename high) bit=rename (observed empty low high bit) := by
  cases bit with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem instruction_step [DecidableEq K] (rename : Q → P) (ending : Option P)
    (code : SpaceMachine.Instruction K Q) (source : SpaceMachine.State K Q) :
    instructionStep (instruction rename ending code) (state rename ending source)=
      state rename ending (instructionStep code source) := by
  cases code with
  | push port bit label => rfl
  | pop port empty low high => simp [instruction,instructionStep,advance,state,observed_map]
  | peek port empty low high => simp [instruction,instructionStep,advance,state,observed_map]
  | readInput eof low high => simp [instruction,instructionStep,advance,state,observed_map]
  | atStart yes no =>
    cases flag : source.tape.left.isEmpty <;> simp [instruction,instructionStep,advance,state,flag]
  | left label => rfl
  | right label => rfl
  | emit bit label => rfl
  | jump label => rfl
  | halt => cases ending <;> rfl

theorem step [DecidableEq K] (source : SpaceMachine.Program K Q) (target : SpaceMachine.Program K P)
    (rename : Q → P) (ending : Option P)
    (compatible : ∀ label, target.code (rename label)=instruction rename ending (source.code label))
    {input next} (actual : SpaceMachine.step source input=some next) :
    SpaceMachine.step target (state rename ending input)=some (state rename ending next) := by
  cases position : input.pc with
  | none => simp [SpaceMachine.step,position] at actual
  | some label =>
    have nextEq : instructionStep (source.code label) input=next := by simpa [SpaceMachine.step,position] using actual
    simp only [SpaceMachine.step,state,position,Option.elim_some,Function.comp_apply,Option.map_some,compatible]
    exact congrArg some ((instruction_step rename ending (source.code label) input).trans
      (congrArg (state rename ending) nextEq))

theorem execution [Fintype K] [DecidableEq K] (source : SpaceMachine.Program K Q) (target : SpaceMachine.Program K P)
    (rename : Q → P) (ending : Option P)
    (compatible : ∀ label, target.code (rename label)=instruction rename ending (source.code label))
    {input final ticks peak} (trace : SpaceMachine.Execution source input final ticks peak) :
    SpaceMachine.Execution target (state rename ending input) (state rename ending final) ticks peak := by
  induction trace with
  | refl input => exact Execution.refl _
  | cons actual rest ih => exact Execution.cons (step source target rename ending compatible actual) ih

end Controller.Complexity.SpaceControl
