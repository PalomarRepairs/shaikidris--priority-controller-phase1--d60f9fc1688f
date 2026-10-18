module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceBuffers

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Physical erasure of an injectively indexed finite family of work banks.
Every discarded bit is popped, all unselected work is retained, and the
workspace peak is exactly the original workspace. Fixed control enumerates
the banks, so resetting introduces no input-sized list or unary counter. -/
namespace Controller.Complexity.SpaceErase
open SpaceMachine

abbrev Label (n : Nat) := Fin (n+1) × Bool
def cursor (n index : Nat) : Label n := (⟨min index n,by omega⟩,false)
def location (index : Fin n) (phase : Fin 2) : Label n :=
  (⟨index.val,by omega⟩,phase.val==1)

def program (targets : Fin n ↪ K) : SpaceMachine.Program K (Label n) where
  main := cursor n 0
  code label :=
    if inside : label.1.val<n then
      if label.2 then .jump (cursor n (label.1.val+1))
      else .pop (targets ⟨label.1.val,inside⟩) (label.1,true) (label.1,false) (label.1,false)
    else .halt

theorem label_card (n : Nat) : Fintype.card (Label n)=2*(n+1) := by simp [Label,Nat.mul_comm]

theorem cursor_val (n index : Nat) (bound : index ≤ n) : (cursor n index).1.val=index := by
  simp [cursor,Nat.min_eq_left bound]

theorem block_code (targets : Fin n ↪ K) (index : Fin n) (phase : Fin 2) :
    (program targets).code (location index phase)=
      SpaceControl.instruction (location index) (some (cursor n (index.val+1)))
        ((SpaceBuffers.clearProgram (targets index)).code phase) := by
  fin_cases phase <;> simp [program,location,index.isLt,SpaceControl.instruction,SpaceBuffers.clearProgram]

theorem block [Fintype K] [DecidableEq K] (targets : Fin n ↪ K) (index : Fin n)
    (tape : ReadOnlyInput.Tape) (output : List Bool) (bank : K → List Bool) :
    SpaceMachine.Execution (program targets) ⟨some (cursor n index.val),tape,bank,output⟩
      ⟨some (cursor n (index.val+1)),tape,Function.update bank (targets index) [],output⟩
      ((bank (targets index)).length+2) (SpaceBuffers.mass bank) := by
  let input : SpaceMachine.State K (Fin 2) := ⟨some (SpaceBuffers.clearProgram (targets index)).main,tape,bank,output⟩
  have actual := SpaceBuffers.clear_execution (targets index) input rfl
  have compiled := SpaceControl.execution (SpaceBuffers.clearProgram (targets index)) (program targets)
    (location index) (some (cursor n (index.val+1))) (block_code targets index) actual
  have entry : location index (SpaceBuffers.clearProgram (targets index)).main=cursor n index.val := by
    simp [location,SpaceBuffers.clearProgram,cursor]
  simpa only [SpaceControl.state,input,Option.elim_some,Option.elim_none,Function.comp_apply,entry,workspace,SpaceBuffers.mass] using compiled

theorem suffix [Fintype K] [DecidableEq K] (targets : Fin n ↪ K)
    (tape : ReadOnlyInput.Tape) (output : List Bool) (count index : Nat) (endIndex : index+count=n)
    (bank : K → List Bool) :
    ∃ final ticks,
      SpaceMachine.Execution (program targets) ⟨some (cursor n index),tape,bank,output⟩
        ⟨none,tape,final,output⟩ ticks (SpaceBuffers.mass bank) ∧
      (∀ selected : Fin n, index ≤ selected.val → final (targets selected)=[]) ∧
      (∀ port, (∀ selected : Fin n, index ≤ selected.val → port ≠ targets selected) → final port=bank port) ∧
      ticks ≤ SpaceBuffers.mass bank+2*count+1 := by
  induction count generalizing index bank with
  | zero =>
    have atEnd : index=n := by omega
    subst index
    have haltStep : SpaceMachine.step (program targets) (⟨some (cursor n n),tape,bank,output⟩ : SpaceMachine.State K (Label n))=
        some ⟨none,tape,bank,output⟩ := by simp [SpaceMachine.step,program,cursor,instructionStep]
    refine ⟨bank,1,?_,?_,fun _ _ => rfl,by omega⟩
    · simpa only [workspace,SpaceBuffers.mass,Nat.max_self] using Execution.cons haltStep (Execution.refl _)
    · intro selected impossible
      omega
  | succ count ih =>
    have inside : index<n := by omega
    let selected : Fin n := ⟨index,inside⟩
    let middle := Function.update bank (targets selected) []
    obtain ⟨final,ticks,tail,cleared,retained,time⟩ := ih (index+1) (by omega) middle
    have first := block targets selected tape output bank
    have complete := first.append tail
    have mass := SpaceBuffers.mass_update bank (targets selected) []
    have peak : max (SpaceBuffers.mass bank) (SpaceBuffers.mass middle)=SpaceBuffers.mass bank := by
      simp only [List.length_nil,Nat.add_zero] at mass
      dsimp only [middle]
      omega
    rw [peak] at complete
    refine ⟨final,_,complete,?_,?_,?_⟩
    · intro chosen after
      by_cases same : chosen=selected
      · subst chosen
        have outside : ∀ later : Fin n, index+1 ≤ later.val → targets selected ≠ targets later := by
          intro later laterBound equal
          have same := targets.injective equal
          have values := congrArg Fin.val same
          dsimp only [selected] at values
          omega
        rw [retained (targets selected) outside]
        simp [middle]
      · have greater : index+1 ≤ chosen.val := by
          have different : chosen.val ≠ index := by
            intro equal
            exact same (Fin.ext equal)
          omega
        exact cleared chosen greater
    · intro port outside
      rw [retained port (fun chosen after => outside chosen (by omega))]
      have different := outside selected le_rfl
      simp [middle,different]
    · dsimp only [middle] at time ⊢
      simp only [List.length_nil,Nat.add_zero] at mass
      omega

theorem execution [Fintype K] [DecidableEq K] (targets : Fin n ↪ K)
    (input : SpaceMachine.State K (Label n)) (entry : input.pc=some (program targets).main) :
    ∃ final ticks,
      SpaceMachine.Execution (program targets) input ⟨none,input.tape,final,input.output⟩ ticks (workspace input) ∧
      (∀ selected, final (targets selected)=[]) ∧
      (∀ port, (∀ selected, port ≠ targets selected) → final port=input.work port) ∧
      ticks ≤ workspace input+2*n+1 := by
  obtain ⟨final,ticks,actual,cleared,retained,time⟩ := suffix targets input.tape input.output n 0 (by omega) input.work
  have ready : (⟨some (cursor n 0),input.tape,input.work,input.output⟩ : SpaceMachine.State K (Label n))=input := by
    cases input with
    | mk pc tape bank output => cases entry; rfl
  rw [ready] at actual
  exact ⟨final,ticks,actual,fun selected => cleared selected (by omega),
    fun port outside => retained port (fun selected _ => outside selected),time⟩

end Controller.Complexity.SpaceErase
