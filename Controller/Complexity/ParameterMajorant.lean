module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Mathlib.Computability.Partrec

@[expose] public section

/-! Computable monotone majorants for arbitrary computable parameter bounds.
The finite prefix maximum removes monotonicity assumptions in executed
parameterized reduction composition. -/
namespace Controller.Complexity.ParameterMajorant

def maximum (function : Nat → Nat) : Nat → Nat
  | 0 => function 0
  | n+1 => max (maximum function n) (function (n+1))

theorem current_le (function : Nat → Nat) (n : Nat) : function n ≤ maximum function n := by
  cases n with
  | zero => rfl
  | succ n => exact Nat.le_max_right _ _

theorem monotone (function : Nat → Nat) : Monotone (maximum function) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_max_left _ _

theorem bounded (function : Nat → Nat) {a b : Nat} (bound : a ≤ b) : function a ≤ maximum function b :=
  (current_le function a).trans (monotone function bound)

theorem recursive (function : Nat → Nat) (n : Nat) :
    maximum function n=Nat.rec (function 0) (fun previous value => max value (function (previous+1))) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [maximum,ih]

theorem computable {function : Nat → Nat} (computed : Computable function) : Computable (maximum function) := by
  have stage : Computable₂ (fun (_ : Nat) (pair : Nat × Nat) => max pair.2 (function (pair.1+1))) :=
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (computed.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))).to₂
  exact (Computable.nat_rec Computable.id (Computable.const (function 0)) stage).of_eq
    (fun n => (recursive function n).symm)

theorem computable_power {function : Nat → Nat} (computed : Computable function) (power : Nat) :
    Computable (fun n => function n^power) := by
  induction power with
  | zero => simpa using (Computable.const (1 : Nat))
  | succ power ih => simpa only [Nat.pow_succ] using Primrec.nat_mul.to_comp.comp ih computed

end Controller.Complexity.ParameterMajorant
