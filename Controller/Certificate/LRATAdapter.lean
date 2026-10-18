module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Relabel
public import Controller.Resolution.Soundness
public import Std.Tactic.BVDecide.LRAT.Checker

@[expose] public section

/-! Sound certificate backends for an exact typed CNF. LRAT actions are checked
by the pinned Std checker. Ordinary resolution retains its separate checker;
no resolution-to-LRAT conversion is asserted. -/
namespace Controller.Certificate
open Controller.CNF

/-- Every declared finite variable has its own external natural identifier.
Unused variables remain in the declared type and do not need clause occurrences. -/
structure FiniteIdentifiers (varCount : ℕ) where
  identify : Fin varCount → ℕ
  injective : Function.Injective identify

namespace FiniteIdentifiers

def canonical (varCount : ℕ) : FiniteIdentifiers varCount :=
  ⟨Fin.val, fun _ _ equal => Fin.ext equal⟩

def encode (identifiers : FiniteIdentifiers varCount)
    (source : FiniteFormula varCount) : Formula ℕ := relabel identifiers.identify source

theorem encode_unsatisfiable_iff (identifiers : FiniteIdentifiers varCount)
    (source : FiniteFormula varCount) :
    Unsatisfiable (identifiers.encode source) ↔ Unsatisfiable source :=
  unsatisfiable_relabel_iff identifiers.injective source
end FiniteIdentifiers

namespace LRATAdapter
abbrev Actions := Array Std.Tactic.BVDecide.LRAT.IntAction

/-- The checker receives precisely the relabelled original ordered clause array. -/
def check (identifiers : FiniteIdentifiers varCount) (source : FiniteFormula varCount)
    (actions : Actions) : Bool :=
  Std.Tactic.BVDecide.LRAT.check actions (OrderedFormula.toStd (identifiers.encode source))

theorem check_sound (identifiers : FiniteIdentifiers varCount)
    (source : FiniteFormula varCount) (actions : Actions)
    (accepted : check identifiers source actions = true) : Unsatisfiable source := by
  have checked : Std.Sat.CNF.Unsat (OrderedFormula.toStd (identifiers.encode source)) :=
    Std.Tactic.BVDecide.LRAT.check_sound actions (OrderedFormula.toStd (identifiers.encode source)) accepted
  exact (identifiers.encode_unsatisfiable_iff source).mp
    ((unsatisfiable_iff_packedUnsat _).mpr checked)
end LRATAdapter

/-- Backend tags distinguish trace languages and their actual soundness proofs. -/
inductive Certificate (varCount : ℕ) where
  | resolution (trace : Controller.Resolution.Trace varCount)
  | lrat (actions : LRATAdapter.Actions)

def checkTyped (source : FiniteFormula varCount) : Certificate varCount → Bool
  | .resolution trace => Controller.Resolution.check source trace
  | .lrat actions => LRATAdapter.check (FiniteIdentifiers.canonical varCount) source actions

theorem checkTyped_sound (source : FiniteFormula varCount) (certificate : Certificate varCount)
    (accepted : checkTyped source certificate = true) : Unsatisfiable source := by
  cases certificate with
  | resolution trace => exact Controller.Resolution.check_sound accepted
  | lrat actions => exact LRATAdapter.check_sound _ _ _ accepted

end Controller.Certificate
