module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Reductions.DualHorn
public import Controller.Decoder.Eval
public import Controller.Physical.DetectionBridge

@[expose] public section

/-!
# Stored decoder for dual-Horn clause violations

Every declared source variable receives a channel, including unused variables.
Two additional channels are the target and helper. The topological table has
one input per channel, one normalized violation node per source row, one
helper guard and one final OR. Source row positions are never merged.
-/
namespace Controller.Reductions.DualHorn

open Controller.CNF Controller.Decoder Controller.Horn.Worklist

def sourceChannel (i : Fin n) : Channel (n + 2) := ⟨i.val, by omega⟩
def targetChannel (n : ℕ) : Channel (n + 2) := ⟨n, by omega⟩
def helperChannel (n : ℕ) : Channel (n + 2) := ⟨n + 1, by omega⟩

def channelRule (rule : Rule (Fin n)) : Rule (Channel (n + 2)) :=
  match rule with
  | .skip => .skip
  | .positive labels => .positive (labels.map sourceChannel)
  | .negative head labels => .negative (sourceChannel head) (labels.map sourceChannel)

/-- Term zero is the helper guard; subsequent terms retain source row order. -/
def storedRule (formula : FiniteFormula n) (term : Fin (formula.clauses.size + 1)) :
    Rule (Channel (n + 2)) :=
  if first : term.val = 0 then .negative (targetChannel n) [helperChannel n]
  else channelRule (compileClause formula.clauses[term.val - 1])

def violationGate (rule : Rule (Channel (n + 2))) (available : ℕ)
    (inputBound : n + 2 ≤ available) : Gate (n + 2) available :=
  match rule with
  | .skip => .zero
  | .positive labels => .guard ⟨n, by omega⟩ labels
  | .negative head labels => .guard ⟨head.val, by omega⟩ labels

/-- Explicit stored topological construction; no gate producer is assumed. -/
def decoder (formula : FiniteFormula n) : DAG (n + 2) where
  nodeCount := n + formula.clauses.size + 4
  node := fun index =>
    if input : index.val < n + 2 then .input ⟨index.val, input⟩
    else if term : index.val < n + formula.clauses.size + 3 then
      violationGate (storedRule formula ⟨index.val - (n + 2), by omega⟩)
        index.val (by omega)
    else .disj (List.ofFn fun row : Fin (formula.clauses.size + 1) =>
      ⟨n + 2 + row.val, by omega⟩)
  roots := [⟨n + formula.clauses.size + 3, by omega⟩]

@[simp] theorem decoder_node_count (formula : FiniteFormula n) :
    (decoder formula).nodeCount = n + formula.clauses.size + 4 := rfl

theorem decoder_guarded (formula : FiniteFormula n) : (decoder formula).Guarded := by
  intro index
  simp only [decoder]
  split
  · rfl
  · split
    · unfold violationGate
      split <;> rfl
    · rfl


private theorem decoder_input (formula : FiniteFormula n) (values : Assignment (n + 2))
    (channel : Channel (n + 2)) :
    (decoder formula).eval values ⟨channel.val, by change channel.val < n + formula.clauses.size + 4; omega⟩ =
      values channel := by
  rw [DAG.eval_eq]
  simp [decoder, Gate.eval, channel.isLt]

/-- Each stored term evaluates to the exact normalized row violation. -/
theorem decoder_term (formula : FiniteFormula n) (values : Assignment (n + 2))
    (term : Fin (formula.clauses.size + 1)) :
    (decoder formula).eval values
      ⟨n + 2 + term.val, by change n + 2 + term.val < n + formula.clauses.size + 4; omega⟩ =
      violation (values (targetChannel n)) values (storedRule formula term) := by
  rw [DAG.eval_eq]
  have notInput : ¬n + 2 + term.val < n + 2 := by omega
  have isTerm : n + 2 + term.val < n + formula.clauses.size + 3 := by omega
  simp only [decoder, notInput, dite_false, isTerm, dite_true]
  have same : (⟨n + 2 + term.val - (n + 2), by omega⟩ : Fin (formula.clauses.size + 1)) = term := by
    apply Fin.ext; simp
  rw [same]
  cases row : storedRule formula term with
  | skip => simp [violationGate, Gate.eval, violation]
  | positive labels =>
    change ((decoder formula).eval values ⟨n, by change n < n + formula.clauses.size + 4; omega⟩ &&
      !(labels.any values)) = (values (targetChannel n) && !(labels.any values))
    exact congrArg (fun value => value && !(labels.any values))
      (decoder_input formula values (targetChannel n))
  | negative head labels =>
    change ((decoder formula).eval values ⟨head.val, by change head.val < n + formula.clauses.size + 4; omega⟩ &&
      !(labels.any values)) = (values head && !(labels.any values))
    rw [decoder_input formula values head]

/-- The final OR is the helper term and every source-row violation. -/
theorem decoder_output (formula : FiniteFormula n) (values : Assignment (n + 2)) :
    (decoder formula).eval values
      ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩ =
      (List.ofFn fun term : Fin (formula.clauses.size + 1) =>
        violation (values (targetChannel n)) values (storedRule formula term)).any id := by
  rw [DAG.eval_eq]
  have notInput : ¬n + formula.clauses.size + 3 < n + 2 := by omega
  simp only [decoder, notInput, dite_false, lt_self_iff_false, Gate.eval]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨node, ⟨term, rfl⟩, active⟩
    exact ⟨_, ⟨term, rfl⟩, (decoder_term formula values term).symm ▸ active⟩
  · rintro ⟨value, ⟨term, rfl⟩, active⟩
    exact ⟨_, ⟨term, rfl⟩, (decoder_term formula values term) ▸ active⟩


@[simp] theorem storedRule_first (formula : FiniteFormula n) :
    storedRule formula (0 : Fin (formula.clauses.size + 1)) = .negative (targetChannel n) [helperChannel n] := by
  simp [storedRule]

@[simp] theorem storedRule_next (formula : FiniteFormula n) (row : Fin formula.clauses.size) :
    storedRule formula row.succ = channelRule (compileClause formula.clauses[row.val]) := by
  simp [storedRule]

theorem channelRule_violation (rule : Rule (Fin n)) (target : Bool)
    (values : Assignment (n + 2)) :
    violation target values (channelRule rule) =
      violation target (fun i => values (sourceChannel i)) rule := by
  cases rule <;> simp [channelRule, violation, List.any_map, Function.comp_def]

/-- The stored decoder has exactly the source models on its detecting cofactor. -/
theorem decoder_zero_iff (formula : FiniteFormula n) (horn : Controller.Horn.DualHorn formula)
    (values : Assignment (n + 2)) (targetOne : values (targetChannel n) = true) :
    (decoder formula).eval values
      ⟨n + formula.clauses.size + 3, by change n + formula.clauses.size + 3 < n + formula.clauses.size + 4; omega⟩ = false ↔
      values (helperChannel n) = true ∧ Satisfies (fun i => values (sourceChannel i)) formula := by
  rw [decoder_output]
  have allTerms :
      (List.ofFn fun term : Fin (formula.clauses.size + 1) =>
        violation (values (targetChannel n)) values (storedRule formula term)).any id = false ↔
      ∀ term : Fin (formula.clauses.size + 1),
        violation (values (targetChannel n)) values (storedRule formula term) = false := by
    simp only [List.any_eq_false, List.mem_ofFn]
    constructor
    · intro zeros term
      have falseValue := zeros _ ⟨term, rfl⟩
      cases h : violation (values (targetChannel n)) values (storedRule formula term) <;> simp_all
    · intro zeros value witness
      obtain ⟨term, rfl⟩ := witness
      rw [zeros term]
      decide
  rw [allTerms]
  constructor
  · intro zeros
    have helperZero := zeros (0 : Fin (formula.clauses.size + 1))
    have helperOne : values (helperChannel n) = true := by
      cases h : values (helperChannel n) <;>
        simp [storedRule_first, violation, targetOne, h] at helperZero ⊢
    refine ⟨helperOne, (compileFormula_holds_iff formula horn _).mp ?_⟩
    intro row
    have zero := zeros row.succ
    rw [storedRule_next, channelRule_violation, targetOne] at zero
    simpa only [compileFormula, Array.getElem_map] using
      (violation_false_iff _ _).mp zero
  · rintro ⟨helperOne, model⟩
    have rows := (compileFormula_holds_iff formula horn _).mpr model
    intro term
    refine Fin.cases ?_ (fun row => ?_) term
    · simp [storedRule_first, violation, targetOne, helperOne]
    · rw [storedRule_next, channelRule_violation, targetOne]
      apply (violation_false_iff _ _).mpr
      simpa only [compileFormula, Array.getElem_map] using rows row

end Controller.Reductions.DualHorn
