module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! A finite binary-stack instruction model and its literal TM2 realization.
The distinguished stack is input/output; private stack indices and program
labels are finite in applications. Execution counts actual transitions. -/
namespace Controller.Complexity.StackMachine
open scoped BigOperators

inductive Instruction (K Q : Type)
  | push (stack : Option K) (bit : Bool) (next : Q)
  | pop (stack : Option K) (empty low high : Q)
  | peek (stack : Option K) (empty low high : Q)
  | jump (next : Q)
  | halt

structure Program (K Q : Type) where
  main : Q
  code : Q → Instruction K Q

structure State (K Q : Type) where
  pc : Option Q
  stk : Option K → List Bool

def initial (program : Program K Q) (input : List Bool) : State K Q :=
  ⟨some program.main,fun stack => match stack with | none => input | some _ => []⟩

def terminal (output : List Bool) : State K Q :=
  ⟨none,fun stack => match stack with | none => output | some _ => []⟩

def instructionStep [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) : State K Q :=
  match instruction with
  | .push stack bit next => ⟨some next,Function.update state.stk stack (bit :: state.stk stack)⟩
  | .pop stack empty low high =>
    let next := match (state.stk stack).head? with | none => empty | some false => low | some true => high
    ⟨some next,Function.update state.stk stack (state.stk stack).tail⟩
  | .peek stack empty low high =>
    let next := match (state.stk stack).head? with | none => empty | some false => low | some true => high
    ⟨some next,state.stk⟩
  | .jump next => ⟨some next,state.stk⟩
  | .halt => ⟨none,state.stk⟩

def step [DecidableEq K] (program : Program K Q) (state : State K Q) : Option (State K Q) :=
  state.pc.map fun label => instructionStep (program.code label) state

def live [Fintype K] (state : State K Q) : Nat := ∑ stack : Option K, (state.stk stack).length

inductive Execution [Fintype K] [DecidableEq K] (program : Program K Q) :
    State K Q → State K Q → Nat → Nat → Prop
  | refl (state) : Execution program state state 0 (live state)
  | cons {state next final ticks peak} : step program state = some next →
      Execution program next final ticks peak → Execution program state final (ticks+1) (max (live state) peak)

theorem Execution.initial_live_le [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) : live state ≤ peak := by
  cases trace with
  | refl => rfl
  | cons => exact Nat.le_max_left _ _

theorem Execution.final_live_le [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) : live final ≤ peak := by
  induction trace with
  | refl => rfl
  | cons transition tail ih => exact ih.trans (Nat.le_max_right _ _)

theorem Execution.append [Fintype K] [DecidableEq K] {program : Program K Q}
    {state middle final firstTicks secondTicks firstPeak secondPeak}
    (first : Execution program state middle firstTicks firstPeak)
    (second : Execution program middle final secondTicks secondPeak) :
    Execution program state final (firstTicks+secondTicks) (max firstPeak secondPeak) := by
  induction first with
  | refl => simpa only [Nat.zero_add,Nat.max_eq_right second.initial_live_le] using second
  | cons transition tail ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.max_assoc] using Execution.cons transition (ih second)

def tmStatement (instruction : Instruction K Q) : Turing.TM2.Stmt (fun _ : Option K => Bool) Q (Option Bool) :=
  let next (label : Q) := Turing.TM2.Stmt.load (fun _ => none) (.goto fun _ => label)
  match instruction with
  | .push stack bit label => .push stack (fun _ => bit) (next label)
  | .pop stack empty low high =>
    .pop stack (fun _ bit => bit)
      (.branch Option.isNone (next empty) (.branch (fun bit => bit == some false) (next low) (next high)))
  | .peek stack empty low high =>
    .peek stack (fun _ bit => bit)
      (.branch Option.isNone (next empty) (.branch (fun bit => bit == some false) (next low) (next high)))
  | .jump label => next label
  | .halt => .load (fun _ => none) .halt

def tmState (state : State K Q) : Turing.TM2.Cfg (fun _ : Option K => Bool) Q (Option Bool) :=
  ⟨state.pc,none,state.stk⟩

theorem tmStatement_step [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) :
    Turing.TM2.stepAux (tmStatement instruction) none state.stk = tmState (instructionStep instruction state) := by
  cases instruction with
  | push stack bit label => rfl
  | jump label => rfl
  | halt => rfl
  | pop stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [tmStatement,Turing.TM2.stepAux,instructionStep,tmState,observed]
    | some bit => cases bit <;> simp [tmStatement,Turing.TM2.stepAux,instructionStep,tmState,observed]
  | peek stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [tmStatement,Turing.TM2.stepAux,instructionStep,tmState,observed]
    | some bit => cases bit <;> simp [tmStatement,Turing.TM2.stepAux,instructionStep,tmState,observed]

theorem tm_step [DecidableEq K] (program : Program K Q) (state : State K Q) :
    Turing.TM2.step (fun label => tmStatement (program.code label)) (tmState state) =
      (step program state).map tmState := by
  cases position : state.pc with
  | none => simp [Turing.TM2.step,tmState,step,position]
  | some label =>
    simp only [Turing.TM2.step,tmState,position,step,Option.map_some]
    exact congrArg some (tmStatement_step (program.code label) state)

theorem Execution.tm_reaches [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) :
    Turing.TM2.Reaches (fun label => tmStatement (program.code label)) (tmState state) (tmState final) := by
  induction trace with
  | refl => exact Relation.ReflTransGen.refl
  | cons transition tail ih =>
    apply Relation.ReflTransGen.head _ ih
    change Turing.TM2.step _ _ = some _
    rw [tm_step,transition]
    rfl

theorem Execution.tm_evals [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) :
    Nonempty (StateTransition.EvalsToInTime
      (Turing.TM2.step fun label => tmStatement (program.code label))
      (tmState state) (some (tmState final)) ticks) := by
  induction trace with
  | refl => exact ⟨StateTransition.EvalsToInTime.refl _ _⟩
  | @cons state next final ticks peak transition tail ih =>
    obtain ⟨bound⟩ := ih
    have single : StateTransition.EvalsToInTime
        (Turing.TM2.step fun label => tmStatement (program.code label))
        (tmState state) (some (tmState next)) 1 := by
      refine ⟨⟨1, ?_⟩, le_rfl⟩
      change Turing.TM2.step _ _ = some _
      rw [tm_step, transition]
      rfl
    exact ⟨StateTransition.EvalsToInTime.trans _ 1 ticks _ _ _ single bound⟩

theorem Execution.tm_steps [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) :
    (fun current => current.bind (Turing.TM2.step fun label => tmStatement (program.code label)))^[ticks]
      (some (tmState state)) = some (tmState final) := by
  induction trace with
  | refl => rfl
  | cons transition tail ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some, tm_step, transition, Option.map_some] using ih

def leftStack : Option K₁ → Option (Sum K₁ K₂) := Option.map Sum.inl
def rightStack : Option K₂ → Option (Sum K₁ K₂) := Option.map Sum.inr

def leftStorage (storage : Option K₁ → List Bool) : Option (Sum K₁ K₂) → List Bool
  | none => storage none
  | some (.inl stack) => storage (some stack)
  | some (.inr _) => []

def rightStorage (storage : Option K₂ → List Bool) : Option (Sum K₁ K₂) → List Bool
  | none => storage none
  | some (.inl _) => []
  | some (.inr stack) => storage (some stack)

theorem leftStorage_at (storage : Option K₁ → List Bool) (stack : Option K₁) :
    leftStorage (K₂ := K₂) storage (leftStack stack) = storage stack := by
  cases stack <;> rfl

theorem rightStorage_at (storage : Option K₂ → List Bool) (stack : Option K₂) :
    rightStorage (K₁ := K₁) storage (rightStack stack) = storage stack := by
  cases stack <;> rfl

theorem leftStorage_update [DecidableEq K₁] [DecidableEq K₂]
    (storage : Option K₁ → List Bool) (stack : Option K₁) (value : List Bool) :
    leftStorage (K₂ := K₂) (Function.update storage stack value) =
      Function.update (leftStorage storage) (leftStack stack) value := by
  funext target
  cases stack <;> cases target with
  | none => simp [leftStorage, leftStack]
  | some target => cases target <;> simp [leftStorage, leftStack, Function.update_apply]

theorem rightStorage_update [DecidableEq K₁] [DecidableEq K₂]
    (storage : Option K₂ → List Bool) (stack : Option K₂) (value : List Bool) :
    rightStorage (K₁ := K₁) (Function.update storage stack value) =
      Function.update (rightStorage storage) (rightStack stack) value := by
  funext target
  cases stack <;> cases target with
  | none => simp [rightStorage, rightStack]
  | some target => cases target <;> simp [rightStorage, rightStack, Function.update_apply]

def leftInstruction (entry : Q₂) : Instruction K₁ Q₁ → Instruction (Sum K₁ K₂) (Sum Q₁ Q₂)
  | .push stack bit next => .push (leftStack stack) bit (.inl next)
  | .pop stack empty low high => .pop (leftStack stack) (.inl empty) (.inl low) (.inl high)
  | .peek stack empty low high => .peek (leftStack stack) (.inl empty) (.inl low) (.inl high)
  | .jump next => .jump (.inl next)
  | .halt => .jump (.inr entry)

def rightInstruction : Instruction K₂ Q₂ → Instruction (Sum K₁ K₂) (Sum Q₁ Q₂)
  | .push stack bit next => .push (rightStack stack) bit (.inr next)
  | .pop stack empty low high => .pop (rightStack stack) (.inr empty) (.inr low) (.inr high)
  | .peek stack empty low high => .peek (rightStack stack) (.inr empty) (.inr low) (.inr high)
  | .jump next => .jump (.inr next)
  | .halt => .halt

/-- Sequential composition shares the input/output stack and separates private work stacks. -/
def compose (first : Program K₁ Q₁) (second : Program K₂ Q₂) :
    Program (Sum K₁ K₂) (Sum Q₁ Q₂) where
  main := .inl first.main
  code := Sum.elim (fun label => leftInstruction second.main (first.code label))
    (fun label => rightInstruction (second.code label))

def leftState (entry : Q₂) (state : State K₁ Q₁) : State (Sum K₁ K₂) (Sum Q₁ Q₂) :=
  ⟨some (state.pc.elim (.inr entry) Sum.inl), leftStorage state.stk⟩

def rightState (state : State K₂ Q₂) : State (Sum K₁ K₂) (Sum Q₁ Q₂) :=
  ⟨state.pc.map Sum.inr, rightStorage state.stk⟩

theorem leftInstruction_step [DecidableEq K₁] [DecidableEq K₂]
    (entry : Q₂) (instruction : Instruction K₁ Q₁) (state : State K₁ Q₁) :
    instructionStep (leftInstruction (K₂ := K₂) entry instruction) (leftState entry state) =
      leftState entry (instructionStep instruction state) := by
  cases instruction with
  | push stack bit next =>
    simp only [leftInstruction, instructionStep, leftState, leftStorage_at, leftStorage_update,
      Option.elim_some]
  | pop stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [leftInstruction, instructionStep, leftState, leftStorage_at, leftStorage_update, observed]
    | some bit => cases bit <;>
      simp [leftInstruction, instructionStep, leftState, leftStorage_at, leftStorage_update, observed]
  | peek stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [leftInstruction, instructionStep, leftState, leftStorage_at, observed]
    | some bit => cases bit <;> simp [leftInstruction, instructionStep, leftState, leftStorage_at, observed]
  | jump next => rfl
  | halt => rfl

theorem rightInstruction_step [DecidableEq K₁] [DecidableEq K₂]
    (instruction : Instruction K₂ Q₂) (state : State K₂ Q₂) :
    instructionStep (rightInstruction (K₁ := K₁) (Q₁ := Q₁) instruction) (rightState state) =
      rightState (instructionStep instruction state) := by
  cases instruction with
  | push stack bit next =>
    simp only [rightInstruction, instructionStep, rightState, rightStorage_at, rightStorage_update,
      Option.map_some]
  | pop stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [rightInstruction, instructionStep, rightState, rightStorage_at, rightStorage_update, observed]
    | some bit => cases bit <;>
      simp [rightInstruction, instructionStep, rightState, rightStorage_at, rightStorage_update, observed]
  | peek stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [rightInstruction, instructionStep, rightState, rightStorage_at, observed]
    | some bit => cases bit <;> simp [rightInstruction, instructionStep, rightState, rightStorage_at, observed]
  | jump next => rfl
  | halt => rfl

theorem compose_left_step [DecidableEq K₁] [DecidableEq K₂]
    (first : Program K₁ Q₁) (second : Program K₂ Q₂) {state next}
    (transition : step first state = some next) :
    step (compose first second) (leftState second.main state) = some (leftState second.main next) := by
  cases position : state.pc with
  | none => simp [step, position] at transition
  | some label =>
    have next_eq : instructionStep (first.code label) state = next := by
      simpa [step, position] using transition
    simp only [step, leftState, position, Option.elim_some, Option.map_some, compose, Sum.elim_inl]
    exact congrArg some ((leftInstruction_step second.main (first.code label) state).trans
      (congrArg (leftState second.main) next_eq))

theorem compose_right_step [DecidableEq K₁] [DecidableEq K₂]
    (first : Program K₁ Q₁) (second : Program K₂ Q₂) (state : State K₂ Q₂) :
    step (compose first second) (rightState (K₁ := K₁) (Q₁ := Q₁) state) =
      (step second state).map rightState := by
  cases position : state.pc with
  | none => simp [step, rightState, position]
  | some label =>
    simp only [step, rightState, position, Option.map_some, compose, Sum.elim_inr]
    exact congrArg some (rightInstruction_step (second.code label) state)

theorem live_leftState [Fintype K₁] [Fintype K₂] (entry : Q₂) (state : State K₁ Q₁) :
    live (leftState (K₂ := K₂) entry state) = live state := by
  simp [live, Fintype.sum_option, Fintype.sum_sum_type, leftState, leftStorage]

theorem live_rightState [Fintype K₁] [Fintype K₂] (state : State K₂ Q₂) :
    live (rightState (K₁ := K₁) (Q₁ := Q₁) state) = live state := by
  simp [live, Fintype.sum_option, Fintype.sum_sum_type, rightState, rightStorage]

theorem Execution.compose_left [Fintype K₁] [Fintype K₂] [DecidableEq K₁] [DecidableEq K₂]
    {first : Program K₁ Q₁} (second : Program K₂ Q₂)
    {state final ticks peak} (trace : Execution first state final ticks peak) :
    Execution (compose first second) (leftState second.main state) (leftState second.main final) ticks peak := by
  induction trace with
  | refl state => simpa only [live_leftState] using
      Execution.refl (program := compose first second) (leftState second.main state)
  | cons transition tail ih =>
    simpa only [live_leftState] using Execution.cons (compose_left_step first second transition) ih

theorem Execution.compose_right [Fintype K₁] [Fintype K₂] [DecidableEq K₁] [DecidableEq K₂]
    (first : Program K₁ Q₁) {second : Program K₂ Q₂}
    {state final ticks peak} (trace : Execution second state final ticks peak) :
    Execution (compose first second) (rightState state) (rightState final) ticks peak := by
  induction trace with
  | refl state => simpa only [live_rightState] using Execution.refl (rightState (K₁ := K₁) (Q₁ := Q₁) state)
  | @cons state next final ticks peak transition tail ih =>
    have lifted : step (compose first second) (rightState state) = some (rightState next) := by
      rw [compose_right_step, transition]
      rfl
    simpa only [live_rightState] using Execution.cons lifted ih

theorem leftState_initial (first : Program K₁ Q₁) (second : Program K₂ Q₂) (input : List Bool) :
    leftState second.main (initial first input) = initial (compose first second) input := by
  simp only [leftState, initial, compose, Option.elim_some]
  congr 1
  funext stack
  cases stack with
  | none => rfl
  | some stack => cases stack <;> rfl

theorem boundary (second : Program K₂ Q₂) (output : List Bool) :
    leftState (K₁ := K₁) (Q₁ := Q₁) second.main (terminal output) = rightState (initial second output) := by
  simp only [leftState, rightState, terminal, initial, Option.elim_none, Option.map_some]
  congr 1
  funext stack
  cases stack with
  | none => rfl
  | some stack => cases stack <;> rfl

theorem rightState_terminal (output : List Bool) :
    rightState (K₁ := K₁) (K₂ := K₂) (Q₁ := Q₁) (Q₂ := Q₂) (terminal output) = terminal output := by
  simp only [rightState, terminal, Option.map_none]
  congr 1
  funext stack
  cases stack with
  | none => rfl
  | some stack => cases stack <;> rfl

/-- Complete runs compose with the sum of transition counts and the maximum bit storage. -/
theorem Execution.compose [Fintype K₁] [Fintype K₂] [DecidableEq K₁] [DecidableEq K₂]
    {first : Program K₁ Q₁} {second : Program K₂ Q₂}
    {input intermediate output firstTicks firstPeak secondTicks secondPeak}
    (firstRun : Execution first (initial first input) (terminal intermediate) firstTicks firstPeak)
    (secondRun : Execution second (initial second intermediate) (terminal output) secondTicks secondPeak) :
    Execution (compose first second) (initial (compose first second) input) (terminal output)
      (firstTicks + secondTicks) (max firstPeak secondPeak) := by
  have leftRun := firstRun.compose_left second
  have rightRun := secondRun.compose_right first
  rw [leftState_initial, boundary] at leftRun
  rw [rightState_terminal] at rightRun
  exact leftRun.append rightRun

theorem live_initial [Fintype K] (program : Program K Q) (input : List Bool) :
    live (initial program input) = input.length := by
  simp [live, initial, Fintype.sum_option]

theorem live_terminal [Fintype K] (output : List Bool) :
    live (terminal (K := K) (Q := Q) output) = output.length := by
  simp [live, terminal, Fintype.sum_option]

theorem live_update [Fintype K] [DecidableEq K] (state : State K Q)
    (position : Option Q) (stack : Option K) (value : List Bool) :
    live (⟨position, Function.update state.stk stack value⟩ : State K Q) + (state.stk stack).length =
      live state + value.length := by
  have lengths : (fun target => (Function.update state.stk stack value target).length) =
      Function.update (fun target => (state.stk target).length) stack value.length := by
    funext target
    by_cases h : target = stack <;> simp [h]
  have original := Finset.sum_update_of_mem (Finset.mem_univ stack)
    (fun target => (state.stk target).length) (state.stk stack).length
  simp only [Function.update_eq_self] at original
  simp only [live, lengths, Finset.sum_update_of_mem (Finset.mem_univ stack)]
  omega

theorem instructionStep_live [Fintype K] [DecidableEq K]
    (instruction : Instruction K Q) (state : State K Q) :
    live (instructionStep instruction state) ≤ live state + 1 := by
  cases instruction with
  | push stack bit next =>
    have bound := live_update state (some next) stack (bit :: state.stk stack)
    simp only [instructionStep, List.length_cons] at *
    omega
  | pop stack empty low high =>
    have bound := live_update state
      (some (match (state.stk stack).head? with | none => empty | some false => low | some true => high))
      stack (state.stk stack).tail
    have shorter : (state.stk stack).tail.length = (state.stk stack).length - 1 := List.length_tail
    simp only [instructionStep] at *
    omega
  | jump next => exact Nat.le_add_right _ _
  | halt => exact Nat.le_add_right _ _
  | peek stack empty low high => exact Nat.le_add_right _ _

theorem step_live [Fintype K] [DecidableEq K] (program : Program K Q) {state next}
    (transition : step program state = some next) : live next ≤ live state + 1 := by
  cases position : state.pc with
  | none => simp [step, position] at transition
  | some label =>
    have next_eq : instructionStep (program.code label) state = next := by
      simpa [step, position] using transition
    rw [← next_eq]
    exact instructionStep_live _ _

theorem Execution.peak_le [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) :
    peak ≤ live state + ticks := by
  induction trace with
  | refl => omega
  | cons transition tail ih =>
    have growth := step_live program transition
    exact max_le (by omega) (by omega)

theorem Execution.output_length_le [Fintype K] [DecidableEq K] {program : Program K Q}
    {input output ticks peak}
    (trace : Execution program (initial program input) (terminal output) ticks peak) :
    output.length ≤ input.length + ticks := by
  have finalBound := trace.final_live_le.trans trace.peak_le
  simpa only [live_initial, live_terminal] using finalBound

/-- The finite binary-stack program as mathlib's bundled finite TM2. -/
def finiteTM [Fintype K] [DecidableEq K] [Fintype Q] (program : Program K Q) : Turing.FinTM2 where
  K := Option K
  k₀ := none
  k₁ := none
  Γ := fun _ => Bool
  Λ := Q
  main := program.main
  σ := Option Bool
  initialState := none
  m := fun label => tmStatement (program.code label)

theorem finiteTM_initial [Fintype K] [DecidableEq K] [Fintype Q]
    (program : Program K Q) (input : List Bool) :
    Turing.initList (finiteTM program) input = tmState (initial program input) := by
  simp only [Turing.initList, finiteTM, tmState, initial]
  congr 1
  funext stack
  cases stack <;> rfl

theorem finiteTM_terminal [Fintype K] [DecidableEq K] [Fintype Q]
    (program : Program K Q) (output : List Bool) :
    Turing.haltList (finiteTM program) output = tmState (terminal output) := by
  simp only [Turing.haltList, finiteTM, tmState, terminal]
  congr 1
  funext stack
  cases stack <;> rfl

theorem Execution.finiteTM_outputs [Fintype K] [DecidableEq K] [Fintype Q] {program : Program K Q}
    {input output ticks peak}
    (trace : Execution program (initial program input) (terminal output) ticks peak) :
    Nonempty (Turing.TM2OutputsInTime (finiteTM program) input (some output) ticks) := by
  change Nonempty (StateTransition.EvalsToInTime (finiteTM program).step
    (Turing.initList (finiteTM program) input) (some (Turing.haltList (finiteTM program) output)) ticks)
  rw [finiteTM_initial, finiteTM_terminal]
  exact trace.tm_evals

/-- A concrete program computes a bit-string function within a polynomial transition bound. -/
def Computes [Fintype K] [DecidableEq K] (program : Program K Q)
    (function : List Bool → List Bool) (time : Polynomial Nat) : Prop :=
  ∀ input, ∃ ticks peak,
    Execution program (initial program input) (terminal (function input)) ticks peak ∧
      ticks ≤ time.eval input.length

theorem polynomial_eval_mono (polynomial : Polynomial Nat) : Monotone polynomial.eval := by
  intro a b h
  induction polynomial using Polynomial.induction_on' with
  | add p q ih iq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add ih iq
  | monomial n coefficient =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h n)

theorem Computes.output_length_le [Fintype K] [DecidableEq K]
    {program : Program K Q} {function time} (computation : Computes program function time) (input) :
    (function input).length ≤ input.length + time.eval input.length := by
  obtain ⟨ticks, peak, trace, bound⟩ := computation input
  exact trace.output_length_le.trans (Nat.add_le_add_left bound _)

theorem Computes.compose [Fintype K₁] [Fintype K₂] [DecidableEq K₁] [DecidableEq K₂]
    {first : Program K₁ Q₁} {second : Program K₂ Q₂} {f g p q}
    (firstComputation : Computes first f p) (secondComputation : Computes second g q) :
    Computes (StackMachine.compose first second) (g ∘ f) (p + q.comp (Polynomial.X + p)) := by
  intro input
  obtain ⟨firstTicks, firstPeak, firstRun, firstBound⟩ := firstComputation input
  obtain ⟨secondTicks, secondPeak, secondRun, secondBound⟩ := secondComputation (f input)
  refine ⟨firstTicks + secondTicks, max firstPeak secondPeak, firstRun.compose secondRun, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X]
  exact Nat.add_le_add firstBound (secondBound.trans
    (polynomial_eval_mono q (firstComputation.output_length_le input)))

/-- This realization uses the concrete machine and the proved step correspondence. -/
theorem Computes.tm_polytime [Fintype K] [DecidableEq K] [Fintype Q]
    {program : Program K Q} {function time} (computation : Computes program function time) :
    Nonempty (Turing.TM2ComputableInPolyTime id id function) := by
  classical
  have outputs (input : List Bool) :
      Nonempty (Turing.TM2OutputsInTime (finiteTM program) input (some (function input))
        (time.eval input.length)) := by
    obtain ⟨ticks, peak, trace, bound⟩ := computation input
    obtain ⟨result⟩ := trace.finiteTM_outputs
    exact ⟨⟨result.toEvalsTo, result.steps_le_m.trans bound⟩⟩
  refine ⟨{
    tm := finiteTM program
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := time
    outputsFun := ?_ }⟩
  intro input
  change Turing.TM2OutputsInTime (finiteTM program) (input.map id)
    (some ((function input).map id)) (time.eval input.length)
  dsimp only [Turing.TM2OutputsInTime, finiteTM]
  rw [List.map_id, List.map_id]
  exact Classical.choice (outputs input)

/-- Maximum number of primitive statement nodes visited in one TM2 transition. -/
def statementDepth : Turing.TM2.Stmt (fun _ : Option K => Bool) Q (Option Bool) → Nat
  | .push _ _ next | .peek _ _ next | .pop _ _ next | .load _ next => 1 + statementDepth next
  | .branch _ low high => 1 + max (statementDepth low) (statementDepth high)
  | .goto _ | .halt => 1

theorem tmStatement_depth (instruction : Instruction K Q) : statementDepth (tmStatement instruction) ≤ 5 := by
  cases instruction <;> simp [tmStatement, statementDepth]

/-- Total resident statement nodes, including both sides of each branch. -/
def statementSize : Turing.TM2.Stmt (fun _ : Option K => Bool) Q (Option Bool) → Nat
  | .push _ _ next | .peek _ _ next | .pop _ _ next | .load _ next => 1 + statementSize next
  | .branch _ low high => 1 + statementSize low + statementSize high
  | .goto _ | .halt => 1

theorem tmStatement_size (instruction : Instruction K Q) : statementSize (tmStatement instruction) ≤ 9 := by
  cases instruction <;> simp [tmStatement, statementSize]

theorem finiteTM_resident [Fintype Q] (program : Program K Q) :
    (∑ label, statementSize (tmStatement (program.code label))) ≤ 9 * Fintype.card Q := by
  calc
    _ ≤ ∑ _label : Q, 9 := Finset.sum_le_sum fun _ _ => tmStatement_size _
    _ = _ := by simp [Nat.mul_comm]

def identity : Program Empty Unit := ⟨(), fun _ => .halt⟩

theorem identity_computes : Computes identity id 1 := by
  intro input
  refine ⟨1, input.length, ?_, by simp⟩
  have last : Execution identity (terminal input) (terminal input) 0 input.length := by
    simpa only [live_terminal] using Execution.refl (program := identity) (terminal input)
  have transition : step identity (initial identity input) = some (terminal input) := rfl
  simpa only [live_initial, Nat.max_self, Nat.zero_add, id_eq] using Execution.cons transition last

/-- Linking keeps every stack shared between two finite-control blocks. -/
def linkLeftInstruction (entry : Q₂) : Instruction K Q₁ → Instruction K (Sum Q₁ Q₂)
  | .push stack bit next => .push stack bit (.inl next)
  | .pop stack empty low high => .pop stack (.inl empty) (.inl low) (.inl high)
  | .peek stack empty low high => .peek stack (.inl empty) (.inl low) (.inl high)
  | .jump next => .jump (.inl next)
  | .halt => .jump (.inr entry)

def linkRightInstruction : Instruction K Q₂ → Instruction K (Sum Q₁ Q₂)
  | .push stack bit next => .push stack bit (.inr next)
  | .pop stack empty low high => .pop stack (.inr empty) (.inr low) (.inr high)
  | .peek stack empty low high => .peek stack (.inr empty) (.inr low) (.inr high)
  | .jump next => .jump (.inr next)
  | .halt => .halt

def link (first : Program K Q₁) (second : Program K Q₂) : Program K (Sum Q₁ Q₂) where
  main := .inl first.main
  code := Sum.elim (fun label => linkLeftInstruction second.main (first.code label))
    (fun label => linkRightInstruction (second.code label))

def linkLeftState (entry : Q₂) (state : State K Q₁) : State K (Sum Q₁ Q₂) :=
  ⟨some (state.pc.elim (.inr entry) Sum.inl), state.stk⟩

def linkRightState (state : State K Q₂) : State K (Sum Q₁ Q₂) :=
  ⟨state.pc.map Sum.inr, state.stk⟩

theorem linkLeftInstruction_step [DecidableEq K] (entry : Q₂)
    (instruction : Instruction K Q₁) (state : State K Q₁) :
    instructionStep (linkLeftInstruction entry instruction) (linkLeftState entry state) =
      linkLeftState entry (instructionStep instruction state) := by
  cases instruction with
  | push stack bit next => rfl
  | pop stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [linkLeftInstruction, instructionStep, linkLeftState, observed]
    | some bit => cases bit <;> simp [linkLeftInstruction, instructionStep, linkLeftState, observed]
  | peek stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [linkLeftInstruction, instructionStep, linkLeftState, observed]
    | some bit => cases bit <;> simp [linkLeftInstruction, instructionStep, linkLeftState, observed]
  | jump next => rfl
  | halt => rfl

theorem linkRightInstruction_step [DecidableEq K] (instruction : Instruction K Q₂) (state : State K Q₂) :
    instructionStep (linkRightInstruction (Q₁ := Q₁) instruction) (linkRightState state) =
      linkRightState (instructionStep instruction state) := by
  cases instruction with
  | push stack bit next => rfl
  | pop stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [linkRightInstruction, instructionStep, linkRightState, observed]
    | some bit => cases bit <;> simp [linkRightInstruction, instructionStep, linkRightState, observed]
  | peek stack empty low high =>
    cases observed : (state.stk stack).head? with
    | none => simp [linkRightInstruction, instructionStep, linkRightState, observed]
    | some bit => cases bit <;> simp [linkRightInstruction, instructionStep, linkRightState, observed]
  | jump next => rfl
  | halt => rfl

theorem link_left_step [DecidableEq K] (first : Program K Q₁) (second : Program K Q₂) {state next}
    (transition : step first state = some next) :
    step (link first second) (linkLeftState second.main state) = some (linkLeftState second.main next) := by
  cases position : state.pc with
  | none => simp [step, position] at transition
  | some label =>
    have next_eq : instructionStep (first.code label) state = next := by
      simpa [step, position] using transition
    simp only [step, linkLeftState, position, Option.elim_some, Option.map_some, link, Sum.elim_inl]
    exact congrArg some ((linkLeftInstruction_step second.main (first.code label) state).trans
      (congrArg (linkLeftState second.main) next_eq))

theorem link_right_step [DecidableEq K] (first : Program K Q₁) (second : Program K Q₂) (state : State K Q₂) :
    step (link first second) (linkRightState (Q₁ := Q₁) state) = (step second state).map linkRightState := by
  cases position : state.pc with
  | none => simp [step, linkRightState, position]
  | some label =>
    simp only [step, linkRightState, position, Option.map_some, link, Sum.elim_inr]
    exact congrArg some (linkRightInstruction_step (second.code label) state)

theorem Execution.link_left [Fintype K] [DecidableEq K]
    {first : Program K Q₁} (second : Program K Q₂)
    {state final ticks peak} (trace : Execution first state final ticks peak) :
    Execution (link first second) (linkLeftState second.main state) (linkLeftState second.main final) ticks peak := by
  induction trace with
  | refl state => exact Execution.refl _
  | cons transition tail ih => exact Execution.cons (link_left_step first second transition) ih

theorem Execution.link_right [Fintype K] [DecidableEq K]
    (first : Program K Q₁) {second : Program K Q₂}
    {state final ticks peak} (trace : Execution second state final ticks peak) :
    Execution (link first second) (linkRightState state) (linkRightState final) ticks peak := by
  induction trace with
  | refl state => exact Execution.refl _
  | @cons state next final ticks peak transition tail ih =>
    have lifted : step (link first second) (linkRightState state) = some (linkRightState next) := by
      rw [link_right_step, transition]
      rfl
    exact Execution.cons lifted ih

/-- A block boundary preserves arbitrary data on every shared stack. -/
theorem Execution.link [Fintype K] [DecidableEq K]
    {first : Program K Q₁} {second : Program K Q₂}
    {input middle output : Option K → List Bool} {firstTicks firstPeak secondTicks secondPeak}
    (firstRun : Execution first ⟨some first.main, input⟩ ⟨none, middle⟩ firstTicks firstPeak)
    (secondRun : Execution second ⟨some second.main, middle⟩ ⟨none, output⟩ secondTicks secondPeak) :
    Execution (link first second) ⟨some (link first second).main, input⟩ ⟨none, output⟩
      (firstTicks+secondTicks) (max firstPeak secondPeak) := by
  exact (firstRun.link_left second).append (secondRun.link_right first)

end Controller.Complexity.StackMachine
