module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.Reductions

@[expose] public section

/-! A finite head test controls continuation between shared-stack blocks.
The test preserves every stack. Rejection halts with the first block's data;
acceptance enters the second block without an extra transition. -/
namespace Controller.Complexity.GuardedLink
open StackMachine

def exitLabel (entry : Q₂) (accept : Option Bool → Bool) (observed : Option Bool) : Q₁ ⊕ Option Q₂ :=
  if accept observed then .inr (some entry) else .inr none

def leftInstruction (guard : Option K) (entry : Q₂) (accept : Option Bool → Bool) :
    Instruction K Q₁ → Instruction K (Q₁ ⊕ Option Q₂)
  | .push stack bit next => .push stack bit (.inl next)
  | .pop stack empty low high => .pop stack (.inl empty) (.inl low) (.inl high)
  | .peek stack empty low high => .peek stack (.inl empty) (.inl low) (.inl high)
  | .jump next => .jump (.inl next)
  | .halt => .peek guard (exitLabel entry accept none) (exitLabel entry accept (some false))
      (exitLabel entry accept (some true))

def rightInstruction : Instruction K Q₂ → Instruction K (Q₁ ⊕ Option Q₂)
  | .push stack bit next => .push stack bit (.inr (some next))
  | .pop stack empty low high => .pop stack (.inr (some empty)) (.inr (some low)) (.inr (some high))
  | .peek stack empty low high => .peek stack (.inr (some empty)) (.inr (some low)) (.inr (some high))
  | .jump next => .jump (.inr (some next))
  | .halt => .halt

def program (first : Program K Q₁) (second : Program K Q₂) (guard : Option K) (accept : Option Bool → Bool) :
    Program K (Q₁ ⊕ Option Q₂) where
  main := .inl first.main
  code label := match label with
    | .inl label => leftInstruction guard second.main accept (first.code label)
    | .inr none => .halt
    | .inr (some label) => rightInstruction (second.code label)

def leftState (guard : Option K) (entry : Q₂) (accept : Option Bool → Bool) (state : State K Q₁) :
    State K (Q₁ ⊕ Option Q₂) :=
  ⟨some (state.pc.elim (exitLabel entry accept ((state.stk guard).head?)) Sum.inl), state.stk⟩

def rightState (state : State K Q₂) : State K (Q₁ ⊕ Option Q₂) :=
  ⟨state.pc.map (fun label => .inr (some label)), state.stk⟩

theorem leftInstruction_step [DecidableEq K] (guard : Option K) (entry : Q₂) (accept : Option Bool → Bool)
    (instruction : Instruction K Q₁) (state : State K Q₁) :
    instructionStep (leftInstruction guard entry accept instruction) (leftState guard entry accept state) =
      leftState guard entry accept (instructionStep instruction state) := by
  cases instruction with
  | push stack bit next => rfl
  | pop stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [leftInstruction, instructionStep, leftState, observed]
    | some bit => cases bit <;> simp [leftInstruction, instructionStep, leftState, observed]
  | peek stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [leftInstruction, instructionStep, leftState, observed]
    | some bit => cases bit <;> simp [leftInstruction, instructionStep, leftState, observed]
  | jump next => rfl
  | halt =>
    cases observed : (state.stk guard).head? with
    | none => simp [leftInstruction, instructionStep, leftState, observed]
    | some bit => cases bit <;> simp [leftInstruction, instructionStep, leftState, observed]

theorem rightInstruction_step [DecidableEq K] (instruction : Instruction K Q₂) (state : State K Q₂) :
    instructionStep (rightInstruction (Q₁ := Q₁) instruction) (rightState state) =
      rightState (instructionStep instruction state) := by
  cases instruction with
  | push stack bit next => rfl
  | pop stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [rightInstruction, instructionStep, rightState, observed]
    | some bit => cases bit <;> simp [rightInstruction, instructionStep, rightState, observed]
  | peek stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [rightInstruction, instructionStep, rightState, observed]
    | some bit => cases bit <;> simp [rightInstruction, instructionStep, rightState, observed]
  | jump next => rfl
  | halt => rfl

theorem left_step [DecidableEq K] (first : Program K Q₁) (second : Program K Q₂)
    (guard : Option K) (accept : Option Bool → Bool) {state next} (transition : step first state = some next) :
    step (program first second guard accept) (leftState guard second.main accept state) =
      some (leftState guard second.main accept next) := by
  cases position : state.pc with
  | none => simp [step, position] at transition
  | some label =>
    have next_eq : instructionStep (first.code label) state = next := by simpa [step, position] using transition
    simp only [step, leftState, position, Option.elim_some, Option.map_some, program]
    exact congrArg some ((leftInstruction_step guard second.main accept (first.code label) state).trans
      (congrArg (leftState guard second.main accept) next_eq))

theorem right_step [DecidableEq K] (first : Program K Q₁) (second : Program K Q₂)
    (guard : Option K) (accept : Option Bool → Bool) (state : State K Q₂) :
    step (program first second guard accept) (rightState (Q₁ := Q₁) state) =
      (step second state).map rightState := by
  cases position : state.pc with
  | none => simp [step, rightState, position]
  | some label =>
    simp only [step, rightState, position, Option.map_some, program]
    exact congrArg some (rightInstruction_step (second.code label) state)

theorem left_execution [Fintype K] [DecidableEq K] {first : Program K Q₁} (second : Program K Q₂)
    (guard : Option K) (accept : Option Bool → Bool) {state final ticks peak}
    (trace : Execution first state final ticks peak) :
    Execution (program first second guard accept) (leftState guard second.main accept state)
      (leftState guard second.main accept final) ticks peak := by
  induction trace with
  | refl state => exact Execution.refl _
  | cons transition tail ih => exact Execution.cons (left_step first second guard accept transition) ih

theorem right_execution [Fintype K] [DecidableEq K] (first : Program K Q₁) {second : Program K Q₂}
    (guard : Option K) (accept : Option Bool → Bool) {state final ticks peak}
    (trace : Execution second state final ticks peak) :
    Execution (program first second guard accept) (rightState state) (rightState final) ticks peak := by
  induction trace with
  | refl state => exact Execution.refl _
  | @cons state next final ticks peak transition tail ih =>
    have lifted : step (program first second guard accept) (rightState state) = some (rightState next) := by
      rw [right_step, transition]
      rfl
    exact Execution.cons lifted ih

theorem success [Fintype K] [DecidableEq K] {first : Program K Q₁} {second : Program K Q₂}
    (guard : Option K) (accept : Option Bool → Bool)
    {input middle output : Option K → List Bool} {firstTicks firstPeak secondTicks secondPeak}
    (firstRun : Execution first ⟨some first.main,input⟩ ⟨none,middle⟩ firstTicks firstPeak)
    (secondRun : Execution second ⟨some second.main,middle⟩ ⟨none,output⟩ secondTicks secondPeak)
    (accepted : accept (middle guard).head? = true) :
    Execution (program first second guard accept) ⟨some (program first second guard accept).main,input⟩ ⟨none,output⟩
      (firstTicks+secondTicks) (max firstPeak secondPeak) := by
  have leftRun := left_execution second guard accept firstRun
  have rightRun := right_execution first guard accept secondRun
  have boundary : leftState guard second.main accept (⟨none,middle⟩ : State K Q₁) =
      rightState (Q₁ := Q₁) (⟨some second.main,middle⟩ : State K Q₂) := by
    simp [leftState, rightState, exitLabel, accepted]
  rw [boundary] at leftRun
  exact leftRun.append rightRun

theorem failure [Fintype K] [DecidableEq K] {first : Program K Q₁} (second : Program K Q₂)
    (guard : Option K) (accept : Option Bool → Bool)
    {input middle : Option K → List Bool} {ticks peak}
    (firstRun : Execution first ⟨some first.main,input⟩ ⟨none,middle⟩ ticks peak)
    (rejected : accept (middle guard).head? = false) :
    Execution (program first second guard accept) ⟨some (program first second guard accept).main,input⟩ ⟨none,middle⟩
      (ticks+1) peak := by
  have leftRun := left_execution second guard accept firstRun
  have stop : leftState guard second.main accept (⟨none,middle⟩ : State K Q₁) =
      (⟨some (.inr none),middle⟩ : State K (Q₁ ⊕ Option Q₂)) := by
    simp [leftState, exitLabel, rejected]
  rw [stop] at leftRun
  change Execution (program first second guard accept) ⟨some (program first second guard accept).main,input⟩
    ⟨some (.inr none),middle⟩ ticks peak at leftRun
  have last : step (program first second guard accept) (⟨some (.inr none),middle⟩ : State K _) =
      some ⟨none,middle⟩ := rfl
  have tail := Execution.cons last (Execution.refl (program := program first second guard accept) ⟨none,middle⟩)
  have bound := firstRun.final_live_le
  simp only [live] at bound
  simpa only [live, Nat.zero_add, Nat.max_self, Nat.max_eq_left bound] using leftRun.append tail

end Controller.Complexity.GuardedLink
