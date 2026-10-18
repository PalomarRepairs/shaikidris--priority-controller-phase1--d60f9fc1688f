module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FiniteTrace
public import Mathlib.Data.Fintype.Vector

@[expose] public section

/-! Bounded readable configurations of a write-only-output transducer.
The input head has only input.length+1 positions. Each work stack is a bounded
binary vector with its own finite length. Output history is excluded only after
the operational output-blindness theorem has been proved. -/
namespace Controller.Complexity.SpaceConfigurations
open SpaceMachine
open scoped BigOperators

abbrev Word (bound : Nat) := (length : Fin (bound+1)) × List.Vector Bool length.val
abbrev Core (K Q : Type) (inputLength bound : Nat) := Option Q × Fin (inputLength+1) × (K → Word bound)

def word (bits : List Bool) (bound : bits.length ≤ limit) : Word limit :=
  ⟨⟨bits.length,by omega⟩,⟨bits,rfl⟩⟩

def unpack (input : List Bool) (core : Core K Q input.length bound) : SpaceMachine.State K Q :=
  ⟨core.1,⟨(input.take core.2.1.val).reverse,input.drop core.2.1.val⟩,fun port => (core.2.2 port).2.val,[]⟩

theorem work_length_le [Fintype K] (state : SpaceMachine.State K Q) (port : K) :
    (state.work port).length ≤ workspace state := by
  change (state.work port).length ≤ ∑ selected, (state.work selected).length
  exact Finset.single_le_sum (fun selected _ => Nat.zero_le (state.work selected).length) (Finset.mem_univ port)

def pack [Fintype K] (input : List Bool) (state : SpaceMachine.State K Q)
    (sameInput : ReadOnlyInput.word state.tape=input) (bounded : workspace state ≤ bound) : Core K Q input.length bound :=
  ⟨state.pc,⟨ReadOnlyInput.position state.tape,by
      have head := ReadOnlyInput.position_le state.tape
      rw [sameInput] at head
      omega⟩,
    fun port => word (state.work port) ((work_length_le state port).trans bounded)⟩

theorem unpack_pack [Fintype K] (input : List Bool) (state : SpaceMachine.State K Q)
    (sameInput : ReadOnlyInput.word state.tape=input) (bounded : workspace state ≤ bound) :
    unpack input (pack input state sameInput bounded)=eraseOutput state := by
  have left := ReadOnlyInput.left_eq state.tape
  have right := ReadOnlyInput.right_eq state.tape
  rw [sameInput] at left right
  have tape : (⟨(input.take (ReadOnlyInput.position state.tape)).reverse,
      input.drop (ReadOnlyInput.position state.tape)⟩ : ReadOnlyInput.Tape)=state.tape := by
    exact (congrArg₂ ReadOnlyInput.Tape.mk left.symm right.symm).trans (by cases state.tape; rfl)
  change (⟨state.pc,⟨(input.take (ReadOnlyInput.position state.tape)).reverse,
    input.drop (ReadOnlyInput.position state.tape)⟩,state.work,[]⟩ : SpaceMachine.State K Q)=eraseOutput state
  rw [tape]
  rfl

def step [Fintype K] [DecidableEq K] (program : SpaceMachine.Program K Q) (input : List Bool) (bound : Nat)
    (core : Core K Q input.length bound) : Option (Core K Q input.length bound) := do
  let next ← (SpaceMachine.step program (unpack input core)).map eraseOutput
  if sameInput : ReadOnlyInput.word next.tape=input then
    if bounded : workspace next ≤ bound then some (pack input next sameInput bounded) else none
  else none

theorem pack_eraseOutput [Fintype K] (input : List Bool) (state : SpaceMachine.State K Q)
    (sameInput : ReadOnlyInput.word state.tape=input) (bounded : workspace state ≤ bound) :
    pack input (eraseOutput state) sameInput bounded=pack input state sameInput bounded := rfl

theorem transition [Fintype K] [DecidableEq K] (program : SpaceMachine.Program K Q) (input : List Bool)
    (state next : SpaceMachine.State K Q)
    (firstInput : ReadOnlyInput.word state.tape=input) (nextInput : ReadOnlyInput.word next.tape=input)
    (firstBound : workspace state ≤ bound) (nextBound : workspace next ≤ bound)
    (actual : SpaceMachine.step program state=some next) :
    step program input bound (pack input state firstInput firstBound)=some (pack input next nextInput nextBound) := by
  have normalized := step_eraseOutput program state
  rw [actual,Option.map_some] at normalized
  simp only [step,unpack_pack,normalized,Bind.bind,Option.bind]
  have sameInput : ReadOnlyInput.word (eraseOutput next).tape=input := nextInput
  have bounded : workspace (eraseOutput next) ≤ bound := nextBound
  simp only [dite_eq_left sameInput,dite_eq_left bounded]
  rfl

theorem path [Fintype K] [DecidableEq K] {program : SpaceMachine.Program K Q}
    {state final ticks peak} (trace : SpaceMachine.Execution program state final ticks peak)
    (input : List Bool) (sameInput : ReadOnlyInput.word state.tape=input) (bounded : peak ≤ bound) :
    FiniteTrace.Path (step program input bound)
      (pack input state sameInput (trace.initial_workspace_le.trans bounded))
      (pack input final (trace.input_preserved.trans sameInput) (trace.final_workspace_le.trans bounded)) ticks := by
  induction trace with
  | refl state => exact FiniteTrace.Path.refl _
  | @cons state middle final ticks peak actual rest ih =>
    have nextInput := (SpaceMachine.step_word actual).trans sameInput
    have tailBound : peak ≤ bound := (Nat.le_max_right _ _).trans bounded
    have single := transition program input state middle sameInput nextInput
      ((Nat.le_max_left _ _).trans bounded) (rest.initial_workspace_le.trans tailBound) actual
    exact FiniteTrace.Path.cons single (ih nextInput tailBound)

theorem halting_time [Fintype K] [DecidableEq K] [Fintype Q] {program : SpaceMachine.Program K Q}
    {state final ticks peak} (trace : SpaceMachine.Execution program state final ticks peak)
    (halted : final.pc=none) : ticks<Fintype.card (Core K Q (ReadOnlyInput.word state.tape).length peak) := by
  have compiled := path trace (ReadOnlyInput.word state.tape) rfl (Nat.le_refl peak)
  apply FiniteTrace.ticks_lt_card compiled
  simp only [step,unpack_pack,SpaceMachine.step,eraseOutput,halted,Option.map_none,Bind.bind,Option.bind]

theorem word_card (bound : Nat) : Fintype.card (Word bound) ≤ (bound+1)*2^bound := by
  have vectorCard (length : Nat) : Fintype.card (List.Vector Bool length)=2^length := by
    rw [Fintype.card_congr (Equiv.vectorEquivFin Bool length)]
    simp
  change Fintype.card ((length : Fin (bound+1)) × List.Vector Bool length.val) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _length : Fin (bound+1), 2^bound := by
      apply Finset.sum_le_sum
      intro length _
      rw [vectorCard]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    _ = _ := by simp

theorem core_card [Fintype K] [DecidableEq K] [Fintype Q] (inputLength bound : Nat) :
    Fintype.card (Core K Q inputLength bound) ≤
      (Fintype.card Q+1)*(inputLength+1)*((bound+1)*2^bound)^Fintype.card K := by
  simp only [Core,Fintype.card_prod,Fintype.card_option,Fintype.card_fin,Fintype.card_fun]
  have work := Nat.pow_le_pow_left (word_card bound) (Fintype.card K)
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left ((Fintype.card Q+1)*(inputLength+1)) work

theorem time_bound [Fintype K] [DecidableEq K] [Fintype Q] {program : SpaceMachine.Program K Q}
    {state final ticks peak} (trace : SpaceMachine.Execution program state final ticks peak)
    (halted : final.pc=none) : ticks<
      (Fintype.card Q+1)*((ReadOnlyInput.word state.tape).length+1)*((peak+1)*2^peak)^Fintype.card K :=
  (halting_time trace halted).trans_le (core_card _ _)

end Controller.Complexity.SpaceConfigurations
