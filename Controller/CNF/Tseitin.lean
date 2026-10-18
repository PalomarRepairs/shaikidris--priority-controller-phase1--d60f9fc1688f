module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.CNF.Gates

@[expose] public section

/-! Unique extension for a complete acyclic gate circuit.

`AcyclicCircuit r v` allocates all `r` free roots first, then allocates each gate
output freshly. Its input literals can mention only earlier variables. The roots
include every independent interface input, such as an unconstrained bridge wire.
Signed relabeling transports this allocation to arbitrary external variable IDs.
-/

namespace Controller.CNF

def extendAssignment (a : Fin v → Bool) (phase value : Bool) : Fin (v + 1) → Bool :=
  Fin.lastCases (value == phase) a

@[simp] theorem extendAssignment_old (a : Fin v → Bool) (phase value : Bool) (i : Fin v) :
    extendAssignment a phase value i.castSucc = a i := by simp [extendAssignment]

@[simp] theorem extendAssignment_last (a : Fin v → Bool) (phase value : Bool) :
    extendAssignment a phase value (Fin.last v) = (value == phase) := by simp [extendAssignment]

@[simp] theorem extendAssignment_restrict (a : Fin v → Bool) (phase value : Bool) :
    extendAssignment a phase value ∘ Fin.castSucc = a := by
  funext i
  simp

@[simp] theorem extendAssignment_output (a : Fin v → Bool) (phase value : Bool) :
    literalValue (extendAssignment a phase value) (Fin.last v, phase) = value := by
  simp only [literalValue, extendAssignment_last]
  cases phase <;> cases value <;> rfl

inductive AcyclicCircuit (r : Nat) : Nat → Type where
  | roots : AcyclicCircuit r r
  | snoc {v : Nat} (previous : AcyclicCircuit r v) (gate : Gate (Fin v)) (phase : Bool) :
      AcyclicCircuit r (v + 1)

namespace AcyclicCircuit

def rootIndex : AcyclicCircuit r v → Fin r → Fin v
  | .roots, i => i
  | .snoc c _ _, i => (c.rootIndex i).castSucc

def rootValues (c : AcyclicCircuit r v) (a : Fin v → Bool) : Fin r → Bool :=
  a ∘ c.rootIndex

def evaluate : AcyclicCircuit r v → (Fin r → Bool) → (Fin v → Bool)
  | .roots, a => a
  | .snoc c g phase, a => extendAssignment (c.evaluate a) phase (g.eval (c.evaluate a))

def formula : AcyclicCircuit r v → FiniteFormula v
  | .roots => Controller.CNF.OrderedFormula.empty
  | .snoc c g phase =>
    CNF.relabel Fin.castSucc c.formula ++ (g.relabel Fin.castSucc).block (Fin.last _, phase)

def gateCount : AcyclicCircuit r v → Nat
  | .roots => 0
  | .snoc c _ _ => c.gateCount + 1

theorem variable_count (c : AcyclicCircuit r v) : r + c.gateCount = v := by
  induction c with
  | roots => rfl
  | snoc c g phase ih =>
    change r + (c.gateCount + 1) = _
    rw [← Nat.add_assoc, ih]

theorem fresh_output (i : Fin v) : i.castSucc ≠ Fin.last v := by
  intro h
  have hv := congrArg Fin.val h
  exact Nat.ne_of_lt i.isLt hv

/-- Adding a gate appends its defining rows and preserves every previous row. -/
theorem formula_snoc_rows (c : AcyclicCircuit r v) (g : Gate (Fin v)) (phase : Bool) :
    (c.snoc g phase).formula.clauses =
      c.formula.clauses.map (Controller.CNF.OrderedFormula.Clause.relabel Fin.castSucc) ++
        ((g.relabel Fin.castSucc).block (Fin.last v, phase)).clauses := rfl

theorem roots_le (c : AcyclicCircuit r v) : r ≤ v := by
  induction c with
  | roots => exact Nat.le_refl _
  | snoc c g phase ih => exact Nat.le_succ_of_le ih

theorem rootIndex_injective (c : AcyclicCircuit r v) : Function.Injective c.rootIndex := by
  induction c with
  | roots => exact fun _ _ h => h
  | snoc c g phase ih =>
    intro i j h
    apply ih
    have hv := congrArg Fin.val h
    exact Fin.ext hv

theorem evaluate_root (c : AcyclicCircuit r v) (a : Fin r → Bool) (i : Fin r) :
    c.evaluate a (c.rootIndex i) = a i := by
  induction c with
  | roots => rfl
  | snoc c g phase ih => simpa [evaluate, rootIndex] using ih

@[simp] theorem rootValues_evaluate (c : AcyclicCircuit r v) (a : Fin r → Bool) :
    c.rootValues (c.evaluate a) = a := by
  funext i
  exact evaluate_root c a i

theorem snoc_satisfies (c : AcyclicCircuit r v) (g : Gate (Fin v)) (phase : Bool)
    (a : Fin (v + 1) → Bool) :
    Satisfies a (c.snoc g phase).formula ↔
      Satisfies (a ∘ Fin.castSucc) c.formula ∧
        literalValue a (Fin.last v, phase) = g.eval (a ∘ Fin.castSucc) := by
  simp only [formula, satisfies_append, satisfies_relabel, Gate.block_correct, Gate.eval_relabel]

theorem evaluate_satisfies (c : AcyclicCircuit r v) (a : Fin r → Bool) :
    Satisfies (c.evaluate a) c.formula := by
  induction c with
  | roots => exact satisfies_empty _
  | snoc c g phase ih =>
    rw [snoc_satisfies]
    simp only [evaluate, extendAssignment_restrict, extendAssignment_output]
    exact ⟨ih, trivial⟩

theorem eq_evaluate_of_satisfies (c : AcyclicCircuit r v) (roots : Fin r → Bool)
    (a : Fin v → Bool) (hroots : c.rootValues a = roots) (ha : Satisfies a c.formula) :
    a = c.evaluate roots := by
  induction c with
  | roots => exact hroots
  | snoc c g phase ih =>
    obtain ⟨hprevious, hgate⟩ := (snoc_satisfies c g phase a).mp ha
    have hroots' : c.rootValues (a ∘ Fin.castSucc) = roots := hroots
    have hp : a ∘ Fin.castSucc = c.evaluate roots := ih _ hroots' hprevious
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [evaluate, extendAssignment_last]
      apply value_from_signed.mp
      change literalValue a (Fin.last _, phase) = g.eval (c.evaluate roots)
      simpa only [hp] using hgate
    · simpa only [evaluate, extendAssignment_old, Function.comp_apply] using congrFun hp j

theorem existsUnique_extension (c : AcyclicCircuit r v) (roots : Fin r → Bool) :
    ∃! a : Fin v → Bool, c.rootValues a = roots ∧ Satisfies a c.formula := by
  refine ⟨c.evaluate roots, ⟨rootValues_evaluate c roots, evaluate_satisfies c roots⟩, ?_⟩
  intro a h
  exact eq_evaluate_of_satisfies c roots a h.1 h.2

/-- Arbitrary added assertions constrain the roots through their unique gate extension. -/
theorem assertion_projection (c : AcyclicCircuit r v) (assertions : FiniteFormula v)
    (roots : Fin r → Bool) :
    (∃ a, c.rootValues a = roots ∧ Satisfies a (c.formula ++ assertions)) ↔
      Satisfies (c.evaluate roots) assertions := by
  constructor
  · rintro ⟨a, hroot, ha⟩
    obtain ⟨hg, hx⟩ := (satisfies_append a c.formula assertions).mp ha
    have heq := eq_evaluate_of_satisfies c roots a hroot hg
    simpa only [heq] using hx
  · intro h
    exact ⟨c.evaluate roots, rootValues_evaluate c roots,
      (satisfies_append _ _ _).mpr ⟨evaluate_satisfies c roots, h⟩⟩

end AcyclicCircuit

def signedPushforward (e : α ≃ β) (phase : α → Bool) (a : α → Bool) : β → Bool :=
  fun i => a (e.symm i) == phase (e.symm i)

@[simp] theorem signedPushforward_pullback (e : α ≃ β) (phase : α → Bool) (a : β → Bool) :
    signedPushforward e phase (signedPullback e phase a) = a := by
  funext i
  simp only [signedPushforward, signedPullback, Equiv.apply_symm_apply]
  cases a i <;> cases phase (e.symm i) <;> rfl

@[simp] theorem signedPullback_pushforward (e : α ≃ β) (phase : α → Bool) (a : α → Bool) :
    signedPullback e phase (signedPushforward e phase a) = a :=
  signedPullback_inverse e phase a

theorem AcyclicCircuit.existsUnique_signed_extension (c : AcyclicCircuit r v)
    (e : Fin v ≃ β) (phase : Fin v → Bool) (roots : Fin r → Bool) :
    ∃! a : β → Bool,
      c.rootValues (signedPullback e phase a) = roots ∧
        Satisfies a (signedRelabel e phase c.formula) := by
  refine ⟨signedPushforward e phase (c.evaluate roots), ?_, ?_⟩
  · dsimp only
    rw [satisfies_signedRelabel, signedPullback_pushforward]
    exact ⟨c.rootValues_evaluate roots, c.evaluate_satisfies roots⟩
  · intro a h
    have hg := (satisfies_signedRelabel e phase a c.formula).mp h.2
    have heq := c.eq_evaluate_of_satisfies roots (signedPullback e phase a) h.1 hg
    have hp := congrArg (signedPushforward e phase) heq
    simpa only [signedPushforward_pullback] using hp

end Controller.CNF
