module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Basic.Assignments

@[expose] public section

/-!
# Literal priority-controller evaluation

The selector carries the conjunction of the enable and all preceding XOR masks.
At each bus it computes the local request, the bus flag, and the literal XOR
mask. The final qualifier is evaluated separately from the accumulated mask.
The optional override affects only the first flag; every later flag is computed
from its local requests.
-/

namespace Controller.Physical

/-- Independent enable and request inputs of a controller with at least one bus.
The request arguments are bus, then channel. -/
structure PrimaryInput (n b : ℕ) where
  positiveBuses : 0 < b
  enable : Assignment n
  request : Fin b → Assignment n

/-- The first bus, whose existence is part of the physical input type. -/
def PrimaryInput.firstBus {n b : ℕ} (input : PrimaryInput n b) : Fin b :=
  ⟨0, input.positiveBuses⟩

/-- The Boolean OR of all channel values; the empty OR is false. -/
def anyTrue {n : ℕ} (a : Assignment n) : Bool :=
  decide (∃ i, a i = true)

/-- Truth of the channel OR is equivalent to a witnessing channel. -/
@[simp] theorem anyTrue_eq_true {n : ℕ} (a : Assignment n) :
    anyTrue a = true ↔ ∃ i, a i = true := by
  simp [anyTrue]

/-- A false channel OR makes every channel value false. -/
theorem eq_false_of_anyTrue_eq_false {n : ℕ} {a : Assignment n}
    (h : anyTrue a = false) (i : Channel n) : a i = false := by
  apply Bool.eq_false_iff.mpr
  intro hi
  have : anyTrue a = true := (anyTrue_eq_true a).mpr ⟨i, hi⟩
  simp [h] at this

/-- The local request after all preceding masks have been applied. -/
def stageTerms {n : ℕ} (active request : Assignment n) : Assignment n :=
  fun i => active i && request i

/-- The healthy flag selected by the local requests. -/
def stageFlag {n : ℕ} (active request : Assignment n) : Bool :=
  anyTrue (stageTerms active request)

/-- The source's XOR mask, including its negated local-request input. -/
def stageMask {n : ℕ} (flag : Bool) (terms : Assignment n) : Assignment n :=
  fun i => flag ^^ !(terms i)

/-- Add the current literal XOR mask to the accumulated enable-and-mask value. -/
def nextActive {n : ℕ} (active request : Assignment n) (flag : Bool) : Assignment n :=
  fun i => active i && stageMask flag (stageTerms active request) i

/-- A dimension-indexed trace of the literal selector recurrence. -/
structure SelectorRun (n b : ℕ) where
  flags : Fin b → Bool
  activeBefore : Fin b → Assignment n
  terms : Fin b → Assignment n
  masks : Fin b → Assignment n
  finalActive : Assignment n

/-- Execute the literal recurrence. An override supplies only the first flag.
The zero-bus case is used for suffix induction, not as a physical controller. -/
def runMasks {n : ℕ} : (b : ℕ) → Assignment n → (Fin b → Assignment n) →
    Option Bool → SelectorRun n b
  | 0, active, _, _ =>
      { flags := Fin.elim0
        activeBefore := Fin.elim0
        terms := Fin.elim0
        masks := Fin.elim0
        finalActive := active }
  | b + 1, active, request, override =>
      let flag := override.getD (stageFlag active (request 0))
      let rest := runMasks b (nextActive active (request 0) flag)
        (fun j => request j.succ) none
      { flags := Fin.cases flag rest.flags
        activeBefore := Fin.cases active rest.activeBefore
        terms := Fin.cases (stageTerms active (request 0)) rest.terms
        masks := Fin.cases (stageMask flag (stageTerms active (request 0))) rest.masks
        finalActive := rest.finalActive }

/-- A run with no remaining buses leaves its initial mask unchanged. -/
@[simp] theorem runMasks_zero_final {n : ℕ} (active : Assignment n)
    (request : Fin 0 → Assignment n) (override : Option Bool) :
    (runMasks 0 active request override).finalActive = active := rfl

/-- The supplied first override is exactly the first flag. -/
@[simp] theorem runMasks_some_first {n b : ℕ} (active : Assignment n)
    (request : Fin (b + 1) → Assignment n) (first : Bool) :
    (runMasks (b + 1) active request (some first)).flags 0 = first := rfl

/-- Without an override the first flag is the OR of its local requests. -/
@[simp] theorem runMasks_none_first {n b : ℕ} (active : Assignment n)
    (request : Fin (b + 1) → Assignment n) :
    (runMasks (b + 1) active request none).flags 0 =
      stageFlag active (request 0) := rfl

/-- Every recorded local term has the source's accumulated-mask form. -/
theorem runMasks_terms_eq {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (override : Option Bool) (j : Fin b) :
    (runMasks b active request override).terms j =
      stageTerms ((runMasks b active request override).activeBefore j) (request j) := by
  induction b generalizing active override with
  | zero => exact Fin.elim0 j
  | succ b ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · exact ih _ _ _ k

/-- Every recorded mask is the XOR of its flag and the negated local term. -/
theorem runMasks_masks_eq {n : ℕ} (b : ℕ) (active : Assignment n)
    (request : Fin b → Assignment n) (override : Option Bool) (j : Fin b) :
    (runMasks b active request override).masks j =
      stageMask ((runMasks b active request override).flags j)
        ((runMasks b active request override).terms j) := by
  induction b generalizing active override with
  | zero => exact Fin.elim0 j
  | succ b ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · exact ih _ _ _ k

/-- A qualifier requires enablement and every request whose bus flag is true. -/
def qualifiers {n b : ℕ} (enable : Assignment n) (request : Fin b → Assignment n)
    (flags : Fin b → Bool) : Assignment n :=
  fun i => enable i && decide (∀ j, flags j = true → request j i = true)

/-- The qualifier definition as a conjunction of its exact source conditions. -/
@[simp] theorem qualifiers_eq_true {n b : ℕ} (enable : Assignment n)
    (request : Fin b → Assignment n) (flags : Fin b → Bool) (i : Channel n) :
    qualifiers enable request flags i = true ↔
      enable i = true ∧ ∀ j, flags j = true → request j i = true := by
  simp [qualifiers]

/-- The completely healthy selector trace. -/
def healthyRun {n b : ℕ} (input : PrimaryInput n b) : SelectorRun n b :=
  runMasks b input.enable input.request none

/-- A trace with an explicitly supplied first flag and otherwise healthy stages. -/
def runFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : SelectorRun n b :=
  runMasks b input.enable input.request (some first)

/-- The healthy first flag is the OR of the enabled first-bus requests. -/
theorem healthyRun_firstFlag {n b : ℕ} (input : PrimaryInput n b) :
    (healthyRun input).flags input.firstBus =
      stageFlag input.enable (input.request input.firstBus) := by
  cases b with
  | zero => exact (Nat.lt_irrefl 0 input.positiveBuses).elim
  | succ b => rfl

/-- A physical first-flag override supplies exactly the flag on the first bus. -/
theorem runFromFirst_firstFlag {n b : ℕ} (input : PrimaryInput n b) (first : Bool) :
    (runFromFirst input first).flags input.firstBus = first := by
  cases b with
  | zero => exact (Nat.lt_irrefl 0 input.positiveBuses).elim
  | succ b => rfl

/-- Supplying the healthy first flag reproduces the entire healthy selector trace. -/
theorem runFromFirst_healthy_firstFlag {n b : ℕ} (input : PrimaryInput n b) :
    runFromFirst input ((healthyRun input).flags input.firstBus) = healthyRun input := by
  cases b with
  | zero => exact (Nat.lt_irrefl 0 input.positiveBuses).elim
  | succ b => rfl

/-- Healthy qualifiers, computed independently of the final accumulated mask. -/
def healthyQualifiers {n b : ℕ} (input : PrimaryInput n b) : Assignment n :=
  qualifiers input.enable input.request (healthyRun input).flags

/-- Qualifiers under a supplied first flag and the literal ensuing recurrence. -/
def qualifiersFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : Assignment n :=
  qualifiers input.enable input.request (runFromFirst input first).flags

/-- Observations are arbitrary Boolean functions of the qualifier vector. -/
def ObservationsDiffer {n q : ℕ} (outputs : Fin q → Assignment n → Bool)
    (healthy faulty : Assignment n) : Prop :=
  ∃ k, outputs k healthy ≠ outputs k faulty

/-- An empty family of observations cannot detect a difference. -/
@[simp] theorem not_observationsDiffer_empty {n : ℕ}
    (outputs : Fin 0 → Assignment n → Bool) (healthy faulty : Assignment n) :
    ¬ ObservationsDiffer outputs healthy faulty := by
  simp [ObservationsDiffer]

end Controller.Physical
