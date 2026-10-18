module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.LogSpaceBounds
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Polynomially bounded intermediate output has logarithmic address size
in the original input length. Constants depend only on the fixed transducer;
the output-length premise comes from its actual halting logspace computation. -/
namespace Controller.Complexity.SpaceLogGrowth

theorem polynomial (output input coefficient degree : Nat)
    (bounded : output ≤ coefficient*(input+2)^degree) :
    LogSpaceBounds.bits output ≤ (coefficient+degree+2)*LogSpaceBounds.bits input := by
  have bitsPositive : 1 ≤ LogSpaceBounds.bits input := by unfold LogSpaceBounds.bits; omega
  have base : input+2 ≤ 2^(LogSpaceBounds.bits input) := by
    simpa only [LogSpaceBounds.bits,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) (input+2)).le
  have power := Nat.pow_le_pow_left base degree
  have positive : 0<(input+2)^degree := Nat.pow_pos (by omega)
  have twice : 2 ≤ 2*(input+2)^degree := by omega
  have framed : output+2 ≤ (coefficient+2)*(input+2)^degree := by
    calc
      _ ≤ coefficient*(input+2)^degree+2*(input+2)^degree := Nat.add_le_add bounded twice
      _ = _ := by ring
  have constant : coefficient+2 ≤ 2^(coefficient+1) := by
    simpa only [Nat.add_assoc] using LogSpaceBounds.overhead (coefficient+1)
  have scaled : coefficient+1 ≤ (coefficient+1)*LogSpaceBounds.bits input := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (coefficient+1) bitsPositive
  have exponent : coefficient+1+degree*LogSpaceBounds.bits input ≤
      (coefficient+degree+1)*LogSpaceBounds.bits input := by
    calc
      _ ≤ (coefficient+1)*LogSpaceBounds.bits input+degree*LogSpaceBounds.bits input := Nat.add_le_add_right scaled _
      _ = _ := by ring
  have encoded : output+2 ≤ 2^((coefficient+degree+1)*LogSpaceBounds.bits input) := by
    calc
      _ ≤ (coefficient+2)*(input+2)^degree := framed
      _ ≤ 2^(coefficient+1)*(2^(LogSpaceBounds.bits input))^degree := Nat.mul_le_mul constant power
      _ = 2^(coefficient+1+degree*LogSpaceBounds.bits input) := by
        rw [← Nat.pow_mul,← Nat.pow_add,Nat.mul_comm (LogSpaceBounds.bits input) degree]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) exponent
  have logarithm := Nat.log_mono_right (b:=2) encoded
  rw [Nat.log_pow (by decide)] at logarithm
  calc
    _ ≤ (coefficient+degree+1)*LogSpaceBounds.bits input+1 := Nat.add_le_add_right logarithm 1
    _ ≤ (coefficient+degree+1)*LogSpaceBounds.bits input+LogSpaceBounds.bits input := Nat.add_le_add_left bitsPositive _
    _ = _ := by ring

def constant (labels banks coefficient : Nat) :=
  (labels+1)*2^(LogSpaceBounds.degree coefficient banks)+LogSpaceBounds.degree coefficient banks+3

theorem output_bits [Fintype K] [Fintype Q] [DecidableEq K]
    {program : SpaceMachine.Program K Q} {function coefficient}
    (computed : LogSpaceBounds.Computes program function coefficient) (input : List Bool) :
    LogSpaceBounds.bits (function input).length ≤
      constant (Fintype.card Q) (Fintype.card K) coefficient*LogSpaceBounds.bits input.length := by
  have bounded := computed.output_length input
  have result := polynomial (function input).length input.length
    ((Fintype.card Q+1)*2^(LogSpaceBounds.degree coefficient (Fintype.card K)))
    (LogSpaceBounds.degree coefficient (Fintype.card K)+1) bounded
  simpa only [constant,Nat.add_assoc] using result

end Controller.Complexity.SpaceLogGrowth
