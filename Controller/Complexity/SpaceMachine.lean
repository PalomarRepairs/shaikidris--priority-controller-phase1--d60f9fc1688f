module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ReadOnlyInput

@[expose] public section

/-! Finite-control binary transducers with two-way read-only input, finitely
many binary work stacks and append-only output. Output is retained in reverse
emission order and is never inspected by a transition. Workspace counts only
the work stacks; immutable input and write-only output have separate measures. -/
namespace Controller.Complexity.SpaceMachine
open scoped BigOperators

inductive Instruction (K Q : Type)
  | push (stack : K) (bit : Bool) (next : Q)
  | pop (stack : K) (empty low high : Q)
  | peek (stack : K) (empty low high : Q)
  | readInput (eof low high : Q)
  | atStart (yes no : Q)
  | left (next : Q)
  | right (next : Q)
  | emit (bit : Bool) (next : Q)
  | jump (next : Q)
  | halt

structure Program (K Q : Type) where
  main : Q
  code : Q → Instruction K Q

structure State (K Q : Type) where
  pc : Option Q
  tape : ReadOnlyInput.Tape
  work : K → List Bool
  output : List Bool

def initial (program : Program K Q) (input : List Bool) : State K Q :=
  ⟨some program.main,ReadOnlyInput.start input,fun _ => [],[]⟩

def advance (state : State K Q) (next : Q) : State K Q := { state with pc := some next }

def observed (empty low high : Q) : Option Bool → Q
  | none => empty
  | some false => low
  | some true => high

def instructionStep [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) : State K Q :=
  match instruction with
  | .push port bit next => { advance state next with work := Function.update state.work port (bit :: state.work port) }
  | .pop port empty low high =>
    { advance state (observed empty low high (state.work port).head?) with
      work := Function.update state.work port (state.work port).tail }
  | .peek port empty low high => advance state (observed empty low high (state.work port).head?)
  | .readInput eof low high => advance state (observed eof low high (ReadOnlyInput.symbol state.tape))
  | .atStart yes no => advance state (if state.tape.left.isEmpty then yes else no)
  | .left next => { advance state next with tape := ReadOnlyInput.moveLeft state.tape }
  | .right next => { advance state next with tape := ReadOnlyInput.moveRight state.tape }
  | .emit bit next => { advance state next with output := bit :: state.output }
  | .jump next => advance state next
  | .halt => { state with pc := none }

def step [DecidableEq K] (program : Program K Q) (state : State K Q) : Option (State K Q) :=
  state.pc.map fun label => instructionStep (program.code label) state

def workspace [Fintype K] (state : State K Q) : Nat := ∑ port, (state.work port).length
def emitted : Instruction K Q → Option Bool
  | .emit bit _ => some bit
  | _ => none

def eraseOutput (state : State K Q) : State K Q := { state with output := [] }

theorem instruction_word [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) :
    ReadOnlyInput.word (instructionStep instruction state).tape=ReadOnlyInput.word state.tape := by
  cases instruction <;> simp [instructionStep,advance]

theorem instruction_output [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) :
    (instructionStep instruction state).output=(emitted instruction).elim state.output (fun bit => bit :: state.output) := by
  cases instruction <;> rfl

/-- Output history cannot affect finite control, the input head or workspace. -/
theorem instruction_eraseOutput [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) :
    eraseOutput (instructionStep instruction (eraseOutput state))=eraseOutput (instructionStep instruction state) := by
  cases instruction <;> rfl

theorem step_eraseOutput [DecidableEq K] (program : Program K Q) (state : State K Q) :
    (step program (eraseOutput state)).map eraseOutput=(step program state).map eraseOutput := by
  cases position : state.pc with
  | none => simp [step,eraseOutput,position]
  | some label =>
    simpa only [step,eraseOutput,position,Option.map_some] using
      congrArg some (instruction_eraseOutput (program.code label) state)

theorem step_word [DecidableEq K] {program : Program K Q} {state next}
    (transition : step program state=some next) : ReadOnlyInput.word next.tape=ReadOnlyInput.word state.tape := by
  cases position : state.pc with
  | none => simp [step,position] at transition
  | some label =>
    have eq : instructionStep (program.code label) state=next := by simpa [step,position] using transition
    rw [← eq]
    exact instruction_word _ _

theorem instruction_output_le [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) :
    (instructionStep instruction state).output.length ≤ state.output.length+1 := by
  rw [instruction_output]
  cases emitted instruction <;> simp

theorem instruction_output_ge [DecidableEq K] (instruction : Instruction K Q) (state : State K Q) :
    state.output.length ≤ (instructionStep instruction state).output.length := by
  rw [instruction_output]
  cases emitted instruction <;> simp

inductive Execution [Fintype K] [DecidableEq K] (program : Program K Q) :
    State K Q → State K Q → Nat → Nat → Prop
  | refl (state) : Execution program state state 0 (workspace state)
  | cons {state next final ticks peak} : step program state=some next →
      Execution program next final ticks peak → Execution program state final (ticks+1) (max (workspace state) peak)

theorem Execution.initial_workspace_le [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) : workspace state ≤ peak := by
  cases trace with
  | refl => rfl
  | cons => exact Nat.le_max_left _ _

theorem Execution.final_workspace_le [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) : workspace final ≤ peak := by
  induction trace with
  | refl => rfl
  | cons transition rest ih => exact ih.trans (Nat.le_max_right _ _)

theorem Execution.input_preserved [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) :
    ReadOnlyInput.word final.tape=ReadOnlyInput.word state.tape := by
  induction trace with
  | refl => rfl
  | cons transition rest ih => exact ih.trans (step_word transition)

theorem Execution.append [Fintype K] [DecidableEq K] {program : Program K Q}
    {state middle final firstTicks secondTicks firstPeak secondPeak}
    (first : Execution program state middle firstTicks firstPeak)
    (second : Execution program middle final secondTicks secondPeak) :
    Execution program state final (firstTicks+secondTicks) (max firstPeak secondPeak) := by
  induction first with
  | refl => simpa only [Nat.zero_add,Nat.max_eq_right second.initial_workspace_le] using second
  | cons transition rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.max_assoc] using Execution.cons transition (ih second)

theorem step_output_bounds [DecidableEq K] {program : Program K Q} {state next}
    (transition : step program state=some next) :
    state.output.length ≤ next.output.length ∧ next.output.length ≤ state.output.length+1 := by
  cases position : state.pc with
  | none => simp [step,position] at transition
  | some label =>
    have eq : instructionStep (program.code label) state=next := by simpa [step,position] using transition
    rw [← eq]
    exact ⟨instruction_output_ge _ _,instruction_output_le _ _⟩

theorem Execution.output_bounds [Fintype K] [DecidableEq K] {program : Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) :
    state.output.length ≤ final.output.length ∧ final.output.length ≤ state.output.length+ticks := by
  induction trace with
  | refl => exact ⟨le_rfl,le_rfl⟩
  | cons transition rest ih =>
    have single := step_output_bounds transition
    constructor <;> omega

end Controller.Complexity.SpaceMachine
