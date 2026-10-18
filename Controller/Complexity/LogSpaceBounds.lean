module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceConfigurations
public import Controller.Complexity.SpaceTM
public import Mathlib.Data.Nat.Log

@[expose] public section

/-! A halting logarithmic-workspace transducer has polynomial time and output
length. The bound follows from executed output blindness and finite readable
configurations; polynomial time is not assumed in the workspace contract. -/
namespace Controller.Complexity.LogSpaceBounds
open SpaceMachine

def bits (length : Nat) := Nat.log 2 (length+2)+1
def degree (constant banks : Nat) := 2*constant*banks
def timeBound (labels banks constant length : Nat) :=
  (labels+1)*2^(degree constant banks)*(length+2)^(degree constant banks+1)
noncomputable def timePolynomial (labels banks constant : Nat) : Polynomial Nat :=
  Polynomial.C ((labels+1)*2^(degree constant banks))*(Polynomial.X+2)^(degree constant banks+1)

theorem time_eval (labels banks constant length : Nat) :
    (timePolynomial labels banks constant).eval length=timeBound labels banks constant length := by
  simp [timePolynomial,timeBound]

theorem overhead (size : Nat) : size+1 ≤ 2^size := by
  induction size with
  | zero => decide
  | succ size ih => rw [Nat.pow_succ]; omega

theorem choices (size : Nat) : (size+1)*2^size ≤ 2^(2*size) := by
  calc
    _ ≤ 2^size*2^size := Nat.mul_le_mul_right _ (overhead size)
    _ = _ := by rw [← Nat.pow_add]; congr 1; omega

theorem exponential (banks constant length peak : Nat) (bounded : peak ≤ constant*bits length) :
    ((peak+1)*2^peak)^banks ≤ (2*(length+2))^(degree constant banks) := by
  have power := Nat.pow_le_pow_left (choices peak) banks
  rw [← Nat.pow_mul] at power
  have exponent : (2*peak)*banks ≤ bits length*(degree constant banks) := by
    have bound := Nat.mul_le_mul_right banks (Nat.mul_le_mul_left 2 bounded)
    simpa only [degree,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bound
  have base : 2^(bits length) ≤ 2*(length+2) := by
    have logarithm := Nat.pow_log_le_self 2 (show length+2 ≠ 0 by omega)
    unfold bits
    rw [Nat.pow_succ]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 2 logarithm
  calc
    _ ≤ 2^((2*peak)*banks) := power
    _ ≤ 2^(bits length*degree constant banks) := Nat.pow_le_pow_right (by decide) exponent
    _ = (2^(bits length))^(degree constant banks) := Nat.pow_mul _ _ _
    _ ≤ _ := Nat.pow_le_pow_left base _

theorem configuration_bound (labels banks constant length peak : Nat) (bounded : peak ≤ constant*bits length) :
    (labels+1)*(length+1)*((peak+1)*2^peak)^banks ≤ timeBound labels banks constant length := by
  calc
    _ ≤ (labels+1)*(length+2)*(2*(length+2))^(degree constant banks) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (exponential banks constant length peak bounded)
    _ = _ := by unfold timeBound; rw [Nat.mul_pow,Nat.pow_succ]; ac_rfl

theorem running_time [Fintype K] [DecidableEq K] [Fintype Q] {program : SpaceMachine.Program K Q}
    {state final ticks peak constant} (trace : SpaceMachine.Execution program state final ticks peak)
    (halted : final.pc=none) (bounded : peak ≤ constant*bits (ReadOnlyInput.word state.tape).length) :
    ticks ≤ timeBound (Fintype.card Q) (Fintype.card K) constant (ReadOnlyInput.word state.tape).length :=
  (SpaceConfigurations.time_bound trace halted).le.trans (configuration_bound _ _ _ _ _ bounded)

/-- A finite actual transducer computes its output stream within a logarithmic
work-bit bound. Finite control is part of the predicate; its enumeration is
needed for configuration counting, while the execution relation does not need it.
Halting and the output relation are proved for every input. -/
def Computes [Fintype K] [DecidableEq K] (program : SpaceMachine.Program K Q)
    (function : List Bool → List Bool) (constant : Nat) : Prop :=
  Finite Q ∧ ∀ input, ∃ final ticks peak, SpaceMachine.Execution program (initial program input) final ticks peak ∧
    final.pc=none ∧ final.output.reverse=function input ∧ peak ≤ constant*bits input.length

theorem Computes.output_length [Fintype K] [DecidableEq K] [Fintype Q]
    {program : SpaceMachine.Program K Q} {function constant} (computed : Computes program function constant)
    (input : List Bool) :
    (function input).length ≤ timeBound (Fintype.card Q) (Fintype.card K) constant input.length := by
  obtain ⟨final,ticks,peak,trace,halted,output,bounded⟩ := computed.2 input
  have emitted := trace.output_bounds.2
  have time := running_time trace halted (by simpa only [initial,ReadOnlyInput.word_start] using bounded)
  rw [← output,List.length_reverse]
  simp only [initial,List.length_nil,Nat.zero_add] at emitted
  exact emitted.trans time

theorem Computes.executed_time [Fintype K] [DecidableEq K] [Fintype Q]
    {program : SpaceMachine.Program K Q} {function constant} (computed : Computes program function constant)
    (input : List Bool) :
    ∃ final ticks peak, SpaceTM.Execution program (SpaceTM.configuration (initial program input))
      (SpaceTM.configuration final) ticks peak ∧ final.pc=none ∧ final.output.reverse=function input ∧
      peak ≤ constant*bits input.length ∧
      ticks ≤ (timePolynomial (Fintype.card Q) (Fintype.card K) constant).eval input.length := by
  obtain ⟨final,ticks,peak,trace,halted,output,bounded⟩ := computed.2 input
  have time := running_time trace halted (by simpa only [initial,ReadOnlyInput.word_start] using bounded)
  exact ⟨final,ticks,peak,SpaceTM.simulation trace,halted,output,bounded,by rwa [time_eval]⟩

end Controller.Complexity.LogSpaceBounds
