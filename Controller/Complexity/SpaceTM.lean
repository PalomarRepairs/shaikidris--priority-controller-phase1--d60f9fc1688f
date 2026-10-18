module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMachine

@[expose] public section

/-! Literal finite TM2 realization of the read-only-input/write-only-output
transducer. Two input stacks represent one immutable two-way tape; the output
stack is only pushed. Work storage is exactly the sum over designated work
stacks, separate from the preserved input and emitted output. -/
namespace Controller.Complexity.SpaceTM
open SpaceMachine
open scoped BigOperators

abbrev Port (K : Type) := Option (K ⊕ Bool)
def workPort (port : K) : Port K := some (.inl port)
def leftPort : Port K := some (.inr false)
def rightPort : Port K := some (.inr true)

def storage (state : SpaceMachine.State K Q) : Port K → List Bool
  | none => state.output
  | some (.inl port) => state.work port
  | some (.inr false) => state.tape.left
  | some (.inr true) => state.tape.right

def configuration (state : SpaceMachine.State K Q) : Turing.TM2.Cfg (fun _ : Port K => Bool) Q (Option Bool) :=
  ⟨state.pc,none,storage state⟩

def next (label : Q) : Turing.TM2.Stmt (fun _ : Port K => Bool) Q (Option Bool) :=
  .load (fun _ => none) (.goto fun _ => label)

def branch (empty low high : Q) : Turing.TM2.Stmt (fun _ : Port K => Bool) Q (Option Bool) :=
  .branch Option.isNone (next empty) (.branch (fun bit => bit==some false) (next low) (next high))

def statement : SpaceMachine.Instruction K Q → Turing.TM2.Stmt (fun _ : Port K => Bool) Q (Option Bool)
  | .push port bit label => .push (workPort port) (fun _ => bit) (next label)
  | .pop port empty low high => .pop (workPort port) (fun _ bit => bit) (branch empty low high)
  | .peek port empty low high => .peek (workPort port) (fun _ bit => bit) (branch empty low high)
  | .readInput eof low high => .peek rightPort (fun _ bit => bit) (branch eof low high)
  | .atStart yes no => .peek leftPort (fun _ bit => bit) (.branch Option.isNone (next yes) (next no))
  | .left label => .pop leftPort (fun _ bit => bit)
      (.branch Option.isNone (next label) (.push rightPort (fun bit => bit.getD false) (next label)))
  | .right label => .pop rightPort (fun _ bit => bit)
      (.branch Option.isNone (next label) (.push leftPort (fun bit => bit.getD false) (next label)))
  | .emit bit label => .push none (fun _ => bit) (next label)
  | .jump label => next label
  | .halt => .load (fun _ => none) .halt

theorem storage_work [DecidableEq K] (state : SpaceMachine.State K Q) (pc : Option Q) (port : K) (bits : List Bool) :
    storage { state with pc := pc, work := Function.update state.work port bits }=
      Function.update (storage state) (workPort port) bits := by
  funext address
  cases address with
  | none => simp [storage,workPort]
  | some selected => cases selected with
    | inl selected =>
      by_cases same : selected=port <;> simp [storage,workPort,Function.update_apply,same]
    | inr bit => cases bit <;> simp [storage,workPort]

theorem storage_output [DecidableEq K] (state : SpaceMachine.State K Q) (pc : Option Q) (bits : List Bool) :
    storage { state with pc := pc, output := bits }=Function.update (storage state) none bits := by
  funext address
  cases address with
  | none => simp [storage]
  | some selected => cases selected with
    | inl port => simp [storage]
    | inr bit => cases bit <;> simp [storage]

theorem storage_tape [DecidableEq K] (state : SpaceMachine.State K Q) (pc : Option Q) (left right : List Bool) :
    storage { state with pc := pc, tape := ⟨left,right⟩ }=
      Function.update (Function.update (storage state) leftPort left) rightPort right := by
  funext address
  cases address with
  | none => simp [storage,leftPort,rightPort]
  | some selected => cases selected with
    | inl selected => simp [storage,leftPort,rightPort]
    | inr bit => cases bit <;> simp [storage,leftPort,rightPort]

theorem storage_pc (state : SpaceMachine.State K Q) (pc : Option Q) : storage { state with pc := pc }=storage state := rfl

theorem statement_step [DecidableEq K] (instruction : SpaceMachine.Instruction K Q) (state : SpaceMachine.State K Q) :
    Turing.TM2.stepAux (statement instruction) none (storage state)=configuration (instructionStep instruction state) := by
  cases instruction with
  | push port bit label =>
    simp only [statement,next,Turing.TM2.stepAux,configuration,instructionStep,advance]
    rw [storage_work state (some label)]
    rfl
  | emit bit label =>
    simp only [statement,next,Turing.TM2.stepAux,configuration,instructionStep,advance]
    rw [storage_output state (some label)]
    rfl
  | jump label => rfl
  | halt => rfl
  | pop port empty low high =>
    cases contents : state.work port with
    | nil => simp [statement,branch,next,Turing.TM2.stepAux,configuration,instructionStep,advance,storage_work,storage,workPort,contents,observed]
    | cons bit rest => cases bit <;>
        simp [statement,branch,next,Turing.TM2.stepAux,configuration,instructionStep,advance,storage_work,storage,workPort,contents,observed]
  | peek port empty low high =>
    cases observedBit : (state.work port).head? with
    | none => simp [statement,branch,next,Turing.TM2.stepAux,configuration,instructionStep,advance,storage_pc state,storage,workPort,observedBit,observed]
    | some bit => cases bit <;> simp [statement,branch,next,Turing.TM2.stepAux,configuration,instructionStep,advance,storage_pc state,storage,workPort,observedBit,observed]
  | readInput eof low high =>
    cases observedBit : state.tape.right.head? with
    | none => simp [statement,branch,next,Turing.TM2.stepAux,configuration,instructionStep,advance,storage_pc state,storage,rightPort,ReadOnlyInput.symbol,observedBit,observed]
    | some bit => cases bit <;> simp [statement,branch,next,Turing.TM2.stepAux,configuration,instructionStep,advance,storage_pc state,storage,rightPort,ReadOnlyInput.symbol,observedBit,observed]
  | atStart yes no =>
    cases contents : state.tape.left with
    | nil => simp [statement,next,Turing.TM2.stepAux,configuration,instructionStep,advance,storage_pc state,storage,leftPort,contents]
    | cons bit rest => simp [statement,next,Turing.TM2.stepAux,configuration,instructionStep,advance,storage_pc state,storage,leftPort,contents]
  | left label =>
    cases contents : state.tape.left with
    | nil =>
      simp only [statement,next,Turing.TM2.stepAux,configuration,instructionStep,advance,ReadOnlyInput.moveLeft,contents,
        storage_pc state,storage,leftPort,List.head?_nil,List.tail_nil,Option.isNone_none,Bool.cond_true]
      congr 1
      simpa only [storage,leftPort,contents] using Function.update_eq_self leftPort (storage state)
    | cons bit rest => cases bit <;>
        simp [statement,next,Turing.TM2.stepAux,configuration,instructionStep,advance,ReadOnlyInput.moveLeft,contents,storage_tape,storage,leftPort,rightPort]
  | right label =>
    cases contents : state.tape.right with
    | nil =>
      simp only [statement,next,Turing.TM2.stepAux,configuration,instructionStep,advance,ReadOnlyInput.moveRight,contents,
        storage_pc state,storage,rightPort,List.head?_nil,List.tail_nil,Option.isNone_none,Bool.cond_true]
      congr 1
      simpa only [storage,rightPort,contents] using Function.update_eq_self rightPort (storage state)
    | cons bit rest => cases bit <;>
        simp [statement,next,Turing.TM2.stepAux,configuration,instructionStep,advance,ReadOnlyInput.moveRight,contents,storage_tape,storage,leftPort,rightPort,
          Function.update_comm (show (some (.inr true) : Port K) ≠ some (.inr false) by simp)]

def workspace [Fintype K] (state : Turing.TM2.Cfg (fun _ : Port K => Bool) Q (Option Bool)) :=
  ∑ port : K, (state.stk (workPort port)).length

theorem workspace_configuration [Fintype K] (state : SpaceMachine.State K Q) :
    workspace (configuration state)=SpaceMachine.workspace state := rfl

theorem statement_size (instruction : SpaceMachine.Instruction K Q) :
    StackMachine.statementSize (statement instruction) ≤ 9 := by
  cases instruction <;> simp [statement,next,branch,StackMachine.statementSize]

theorem statement_depth (instruction : SpaceMachine.Instruction K Q) :
    StackMachine.statementDepth (statement instruction) ≤ 5 := by
  cases instruction <;> simp [statement,next,branch,StackMachine.statementDepth]

theorem resident [Fintype Q] (program : SpaceMachine.Program K Q) :
    (∑ label, StackMachine.statementSize (statement (program.code label))) ≤ 9*Fintype.card Q := by
  calc
    _ ≤ ∑ _label : Q, 9 := Finset.sum_le_sum fun _ _ => statement_size _
    _ = _ := by simp [Nat.mul_comm]

theorem total_storage [Fintype K] (state : SpaceMachine.State K Q) :
    StackMachine.live (⟨state.pc,storage state⟩ : StackMachine.State (K ⊕ Bool) Q)=
      (ReadOnlyInput.word state.tape).length+SpaceMachine.workspace state+state.output.length := by
  simp [StackMachine.live,storage,Fintype.sum_option,Fintype.sum_sum_type,
    SpaceMachine.workspace,ReadOnlyInput.word]
  omega

theorem step [DecidableEq K] (program : SpaceMachine.Program K Q) (state : SpaceMachine.State K Q) :
    Turing.TM2.step (fun label => statement (program.code label)) (configuration state)=
      (SpaceMachine.step program state).map configuration := by
  cases position : state.pc with
  | none => simp [Turing.TM2.step,configuration,SpaceMachine.step,position]
  | some label =>
    simp only [Turing.TM2.step,configuration,position,SpaceMachine.step,Option.map_some]
    exact congrArg some (statement_step (program.code label) state)

def machine [Fintype K] [DecidableEq K] [Fintype Q] (program : SpaceMachine.Program K Q) : Turing.FinTM2 where
  K := Port K
  k₀ := rightPort
  k₁ := none
  Γ := fun _ => Bool
  Λ := Q
  main := program.main
  σ := Option Bool
  initialState := none
  m := fun label => statement (program.code label)

theorem initial [Fintype K] [DecidableEq K] [Fintype Q]
    (program : SpaceMachine.Program K Q) (input : List Bool) :
    Turing.initList (machine program) input=configuration (SpaceMachine.initial program input) := by
  simp only [Turing.initList,machine,configuration,SpaceMachine.initial,ReadOnlyInput.start]
  congr 1
  funext address
  cases address with
  | none => simp [storage,rightPort]
  | some selected => cases selected with
    | inl selected => simp [storage,rightPort]
    | inr bit =>
      cases bit
      · simp [storage,rightPort]
      · simp [storage,rightPort]
        rfl

inductive Execution [Fintype K] [DecidableEq K] (program : SpaceMachine.Program K Q) :
    Turing.TM2.Cfg (fun _ : Port K => Bool) Q (Option Bool) →
    Turing.TM2.Cfg (fun _ : Port K => Bool) Q (Option Bool) → Nat → Nat → Prop
  | refl (state) : Execution program state state 0 (workspace state)
  | cons {state next final ticks peak} : Turing.TM2.step (fun label => statement (program.code label)) state=some next →
      Execution program next final ticks peak → Execution program state final (ticks+1) (max (workspace state) peak)

theorem simulation [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak} (trace : SpaceMachine.Execution program state final ticks peak) :
    Execution program (configuration state) (configuration final) ticks peak := by
  induction trace with
  | refl state => exact Execution.refl _
  | @cons state middle final ticks peak transition rest ih =>
    have compiled := step program state
    rw [transition] at compiled
    exact Execution.cons compiled ih

theorem evals [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak} (trace : Execution program state final ticks peak) :
    Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step fun label => statement (program.code label))
      state (some final) ticks) := by
  induction trace with
  | refl state => exact ⟨StateTransition.EvalsToInTime.refl _ _⟩
  | @cons state middle final ticks peak transition rest ih =>
    obtain ⟨tail⟩ := ih
    have first : StateTransition.EvalsToInTime (Turing.TM2.step fun label => statement (program.code label))
        state (some middle) 1 := ⟨⟨1,transition⟩,le_rfl⟩
    exact ⟨StateTransition.EvalsToInTime.trans _ 1 ticks _ _ _ first tail⟩

end Controller.Complexity.SpaceTM
