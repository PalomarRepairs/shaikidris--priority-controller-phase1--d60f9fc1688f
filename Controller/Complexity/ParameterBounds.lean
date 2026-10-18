module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ParameterMajorant
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Explicit original-parameter bounds for sequential fixed-parameter
computation. The first output length is charged before the second runtime
is substituted. No coefficient is assumed monotone. -/
namespace Controller.Complexity.ParameterBounds

def degree (first second : Nat) := first+(first+1)*second
def coefficient (first second parameter : Nat → Nat) (secondDegree : Nat) (k : Nat) :=
  first k+ParameterMajorant.maximum second (parameter k)*(first k+1)^secondDegree

theorem length_bound {length ticks coefficient degree : Nat}
    (time : ticks ≤ coefficient*(length+1)^degree) :
    length+ticks+1 ≤ (coefficient+1)*(length+1)^(degree+1) := by
  have base : length+1 ≤ (length+1)^(degree+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ length+1 by omega) (show 1 ≤ degree+1 by omega)
  have power := Nat.pow_le_pow_right (show 1 ≤ length+1 by omega) (show degree ≤ degree+1 by omega)
  have scaled := Nat.mul_le_mul_left coefficient power
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem composed {first second parameter : Nat → Nat} {firstDegree secondDegree k middle length firstTicks secondTicks : Nat}
    (firstTime : firstTicks ≤ first k*(length+1)^firstDegree)
    (middleLength : middle ≤ length+firstTicks)
    (nextParameter : targetParameter ≤ parameter k)
    (secondTime : secondTicks ≤ second targetParameter*(middle+1)^secondDegree) :
    firstTicks+secondTicks ≤ coefficient first second parameter secondDegree k*
      (length+1)^(degree firstDegree secondDegree) := by
  have output : middle+1 ≤ (first k+1)*(length+1)^(firstDegree+1) :=
    (show middle+1 ≤ length+firstTicks+1 by omega).trans (length_bound firstTime)
  have later := Nat.mul_le_mul (ParameterMajorant.bounded second nextParameter) (Nat.pow_le_pow_left output secondDegree)
  have expanded :
      ParameterMajorant.maximum second (parameter k)*((first k+1)*(length+1)^(firstDegree+1))^secondDegree=
        (ParameterMajorant.maximum second (parameter k)*(first k+1)^secondDegree)*
          (length+1)^((firstDegree+1)*secondDegree) := by rw [Nat.mul_pow,← Nat.pow_mul]; ring
  rw [expanded] at later
  have earlyPower := Nat.pow_le_pow_right (show 1 ≤ length+1 by omega)
    (show firstDegree ≤ degree firstDegree secondDegree by unfold degree; omega)
  have laterPower := Nat.pow_le_pow_right (show 1 ≤ length+1 by omega)
    (show (firstDegree+1)*secondDegree ≤ degree firstDegree secondDegree by unfold degree; omega)
  have early := firstTime.trans (Nat.mul_le_mul_left (first k) earlyPower)
  have late := secondTime.trans (later.trans (Nat.mul_le_mul_left _ laterPower))
  simpa only [coefficient,Nat.add_mul] using Nat.add_le_add early late

theorem computable_coefficient {first second parameter : Nat → Nat}
    (firstComputed : Computable first) (secondComputed : Computable second) (parameterComputed : Computable parameter)
    (secondDegree : Nat) : Computable (coefficient first second parameter secondDegree) := by
  have sum := Primrec.nat_add.to_comp.comp firstComputed (Computable.const (1 : Nat))
  exact Primrec.nat_add.to_comp.comp firstComputed
    (Primrec.nat_mul.to_comp.comp ((ParameterMajorant.computable secondComputed).comp parameterComputed)
      (ParameterMajorant.computable_power sum secondDegree))

end Controller.Complexity.ParameterBounds
