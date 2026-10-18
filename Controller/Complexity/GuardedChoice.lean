module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ControlEmbed

@[expose] public section

/-! A physical head test selects one of two executed continuations. The
first block's final halt is replaced by that test, preserving its tick count;
both continuations retain the original shared storage and transition costs. -/
namespace Controller.Complexity.GuardedChoice
open StackMachine

def exitLabel (yes : Q₁) (no : Q₂) (accept : Option Bool → Bool) (observed : Option Bool) : Q₀ ⊕ (Q₁ ⊕ Q₂) :=
  if accept observed then .inr (.inl yes) else .inr (.inr no)

def firstInstruction (guard : Option K) (yes : Q₁) (no : Q₂) (accept : Option Bool → Bool) :
    Instruction K Q₀ → Instruction K (Q₀ ⊕ (Q₁ ⊕ Q₂))
  | .halt => .peek guard (exitLabel yes no accept none) (exitLabel yes no accept (some false))
      (exitLabel yes no accept (some true))
  | .push port bit next => .push port bit (.inl next)
  | .pop port empty low high => .pop port (.inl empty) (.inl low) (.inl high)
  | .peek port empty low high => .peek port (.inl empty) (.inl low) (.inl high)
  | .jump next => .jump (.inl next)

def program (first : Program K Q₀) (yes : Program K Q₁) (no : Program K Q₂)
    (guard : Option K) (accept : Option Bool → Bool) : Program K (Q₀ ⊕ (Q₁ ⊕ Q₂)) where
  main := .inl first.main
  code label := match label with
    | .inl label => firstInstruction guard yes.main no.main accept (first.code label)
    | .inr (.inl label) => ControlEmbed.instruction (fun q => .inr (.inl q)) (yes.code label)
    | .inr (.inr label) => ControlEmbed.instruction (fun q => .inr (.inr q)) (no.code label)

def firstState (guard : Option K) (yes : Q₁) (no : Q₂) (accept : Option Bool → Bool) (state : State K Q₀) :
    State K (Q₀ ⊕ (Q₁ ⊕ Q₂)) :=
  ⟨some (state.pc.elim (exitLabel yes no accept ((state.stk guard).head?)) Sum.inl),state.stk⟩

theorem firstInstruction_step [DecidableEq K] (guard : Option K) (yes : Q₁) (no : Q₂)
    (accept : Option Bool → Bool) (code : Instruction K Q₀) (input : State K Q₀) :
    instructionStep (firstInstruction guard yes no accept code) (firstState guard yes no accept input)=
      firstState guard yes no accept (instructionStep code input) := by
  cases code with
  | push port bit next => rfl
  | pop port empty low high =>
    cases observed : (input.stk port).head? with
    | none => simp [firstInstruction,instructionStep,firstState,observed]
    | some bit => cases bit <;> simp [firstInstruction,instructionStep,firstState,observed]
  | peek port empty low high =>
    cases observed : (input.stk port).head? with
    | none => simp [firstInstruction,instructionStep,firstState,observed]
    | some bit => cases bit <;> simp [firstInstruction,instructionStep,firstState,observed]
  | jump next => rfl
  | halt =>
    cases observed : (input.stk guard).head? with
    | none => simp [firstInstruction,instructionStep,firstState,observed]
    | some bit => cases bit <;> simp [firstInstruction,instructionStep,firstState,observed]

theorem first_step [DecidableEq K] (first : Program K Q₀) (yes : Program K Q₁) (no : Program K Q₂)
    (guard : Option K) (accept : Option Bool → Bool) {input next}
    (transition : step first input=some next) :
    step (program first yes no guard accept) (firstState guard yes.main no.main accept input)=
      some (firstState guard yes.main no.main accept next) := by
  cases position : input.pc with
  | none => simp [step,position] at transition
  | some label =>
    have nextEq : instructionStep (first.code label) input=next := by simpa [step,position] using transition
    simp only [step,firstState,position,Option.elim_some,program]
    exact congrArg some ((firstInstruction_step guard yes.main no.main accept (first.code label) input).trans
      (congrArg (firstState guard yes.main no.main accept) nextEq))

theorem first_execution [Fintype K] [DecidableEq K]
    (first : Program K Q₀) (yes : Program K Q₁) (no : Program K Q₂)
    (guard : Option K) (accept : Option Bool → Bool) {input final ticks peak}
    (trace : Execution first input final ticks peak) :
    Execution (program first yes no guard accept) (firstState guard yes.main no.main accept input)
      (firstState guard yes.main no.main accept final) ticks peak := by
  induction trace with
  | refl input => exact Execution.refl _
  | cons transition rest ih => exact Execution.cons (first_step first yes no guard accept transition) ih

theorem success [Fintype K] [DecidableEq K]
    {first : Program K Q₀} {yes : Program K Q₁} (no : Program K Q₂)
    (guard : Option K) (accept : Option Bool → Bool) {input middle output : Option K → List Bool}
    {firstTicks firstPeak nextTicks nextPeak}
    (firstRun : Execution first ⟨some first.main,input⟩ ⟨none,middle⟩ firstTicks firstPeak)
    (nextRun : Execution yes ⟨some yes.main,middle⟩ ⟨none,output⟩ nextTicks nextPeak)
    (accepted : accept ((middle guard).head?)=true) :
    Execution (program first yes no guard accept) ⟨some (program first yes no guard accept).main,input⟩
      ⟨none,output⟩ (firstTicks+nextTicks) (max firstPeak nextPeak) := by
  have left := first_execution first yes no guard accept firstRun
  have right := ControlEmbed.execution yes (program first yes no guard accept) (fun q => .inr (.inl q)) (fun _ => rfl) nextRun
  have boundary : firstState guard yes.main no.main accept (⟨none,middle⟩ : State K Q₀)=
      ControlEmbed.state (fun q : Q₁ => (Sum.inr (Sum.inl q) : Q₀ ⊕ (Q₁ ⊕ Q₂))) ⟨some yes.main,middle⟩ := by
    simp [firstState,exitLabel,accepted,ControlEmbed.state]
  rw [boundary] at left
  exact left.append right

theorem failure [Fintype K] [DecidableEq K]
    {first : Program K Q₀} (yes : Program K Q₁) {no : Program K Q₂}
    (guard : Option K) (accept : Option Bool → Bool) {input middle output : Option K → List Bool}
    {firstTicks firstPeak nextTicks nextPeak}
    (firstRun : Execution first ⟨some first.main,input⟩ ⟨none,middle⟩ firstTicks firstPeak)
    (nextRun : Execution no ⟨some no.main,middle⟩ ⟨none,output⟩ nextTicks nextPeak)
    (rejected : accept ((middle guard).head?)=false) :
    Execution (program first yes no guard accept) ⟨some (program first yes no guard accept).main,input⟩
      ⟨none,output⟩ (firstTicks+nextTicks) (max firstPeak nextPeak) := by
  have left := first_execution first yes no guard accept firstRun
  have right := ControlEmbed.execution no (program first yes no guard accept) (fun q => .inr (.inr q)) (fun _ => rfl) nextRun
  have boundary : firstState guard yes.main no.main accept (⟨none,middle⟩ : State K Q₀)=
      ControlEmbed.state (fun q : Q₂ => (Sum.inr (Sum.inr q) : Q₀ ⊕ (Q₁ ⊕ Q₂))) ⟨some no.main,middle⟩ := by
    simp [firstState,exitLabel,rejected,ControlEmbed.state]
  rw [boundary] at left
  exact left.append right

end Controller.Complexity.GuardedChoice
