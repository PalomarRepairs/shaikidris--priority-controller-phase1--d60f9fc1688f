module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.ForestTraversal
public import Controller.Horn.WorklistAccept

@[expose] public section

/-! Compact zero queries retain only literal-support coordinates. Extending
unused coordinates by true recovers the greatest original model, while the
existence-only decoder fixes them false. The fetched worklist endpoint below
charges the actual compact serialized formula; source compilation and final
channel emission are separate operations. -/
namespace Controller.Cost.ForestGreatestZero
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Decoder.SparseFormula
variable {α : Type*} [LinearOrder α]

/-- Unused source coordinates are absent from every emitted clause. -/
def liftTrue (formula : Formula α)
    (values : Fin ((support formula).card + 1) → Bool) (coordinate : α) : Bool :=
  if coordinate ∈ support formula then values (index formula coordinate) else true

theorem liftTrue_model (formula : Formula α)
    (values : Fin ((support formula).card + 1) → Bool)
    (model : Satisfies values (compact formula)) :
    Satisfies (liftTrue formula values) formula := by
  apply (satisfies_agree formula (values ∘ index formula) (liftTrue formula values) ?_).mp
    ((satisfies_relabel _ _ _).mp model)
  intro coordinate present
  simp only [Function.comp_apply, liftTrue, ite_eq_left present]

theorem liftTrue_greatest (formula : Formula α)
    (values : Fin ((support formula).card + 1) → Bool)
    (upper : ∀ assignment, Satisfies assignment (compact formula) → Controller.Horn.Below assignment values) :
    ∀ assignment, Satisfies assignment formula → Controller.Horn.Below assignment (liftTrue formula values) := by
  intro assignment model coordinate positive
  by_cases present : coordinate ∈ support formula
  · have compactModel : Satisfies (compactAssignment formula assignment) (compact formula) := by
      apply (satisfies_relabel _ _ _).mpr
      apply (satisfies_agree formula assignment (compactAssignment formula assignment ∘ index formula) ?_).mp model
      intro source member
      exact (compactAssignment_index formula assignment source member).symm
    have retained := upper _ compactModel (index formula coordinate)
      (by simpa only [compactAssignment_index formula assignment coordinate present] using positive)
    simpa only [liftTrue, ite_eq_left present] using retained
  · simp only [liftTrue, ite_eq_right present]

/-- The executable compact worklist yields a model dominating every original
model. Its dummy slot and every omitted original variable remain distinct
from actual channel/guard occurrences in the source representation. -/
theorem compact_worklist_lifted (formula : Formula α) (dual : Controller.Horn.DualHorn formula)
    (values : Vector Bool ((support formula).card + 1))
    (returned : Controller.Horn.Worklist.solveFormula (compact formula) = some values) :
    Satisfies (liftTrue formula (fun slot => values[slot.val])) formula ∧
      ∀ assignment, Satisfies assignment formula →
        Controller.Horn.Below assignment (liftTrue formula (fun slot => values[slot.val])) := by
  obtain ⟨model, upper⟩ := Controller.Horn.Worklist.solveFormula_some_model
    (compact formula) (compact_dualHorn formula dual) values returned
  exact ⟨liftTrue_model formula _ model, liftTrue_greatest formula _ upper⟩

/-- This physical endpoint includes cold serialized input loading, normalized
rows, repeated incidences, FIFO propagation and tagged model output. Bounds
apply to actual compact rows; they do not count a supplied support enumeration
as a free operation. -/
theorem compact_cold_execution (formula : Formula α) (dual : Controller.Horn.DualHorn formula)
    (state : Controller.Cost.State width 8) (suffix : List (Controller.Cost.Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width)
      (compact formula).clauses.toList).toList ++ suffix)
    (position : state.pc = Controller.Cost.word width 0)
    (running : state.halted = false)
    (wordBound : 400 * Controller.Cost.Horn.inputSize (compact formula) < 2 ^ width) :
    ∃ final ticks peak,
      Controller.Cost.Execution (Controller.Horn.WorklistAccept.program width
        (compact formula).clauses.toList) state final ticks peak ∧
      final.halted = true ∧ final.stack = suffix ∧
      final.output = Controller.Horn.WorklistAccept.resultWords width
        (Controller.Horn.Worklist.solveFormula (compact formula)) ++ state.output ∧
      ticks ≤ 131 * Controller.Cost.Horn.inputSize (compact formula) ∧
      Controller.Cost.programWords (Controller.Horn.WorklistAccept.program width
        (compact formula).clauses.toList) + peak ≤ state.liveWords +
          1421 * Controller.Cost.Horn.inputSize (compact formula) :=
  Controller.Cost.Horn.solveFormula_indexed_word_linear (compact formula)
    (compact_dualHorn formula dual) state suffix emptyHeap input position running wordBound

/-- Project the actually returned greatest compact vector through the exact
finite-variable relabeling and the forward-only forest zero rows. -/
theorem forest_zero_projection (graph : DAG n) (guarded : graph.Guarded)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount)
    (values : Vector Bool ((support (graph.finiteForestZeroSystem b target root)).card + 1))
    (returned : Controller.Horn.Worklist.solveFormula (graph.compactForestZeroSystem b target root) = some values) :
    let assignment := liftTrue (graph.finiteForestZeroSystem b target root)
      (fun slot => values[slot.val]) ∘ graph.zeroIndex
    (Admissible b target (graph.zeroChannelSet assignment) ∧
      graph.eval (assignmentOfSet (graph.zeroChannelSet assignment)) root = false) ∧
      ∀ K, Admissible b target K → graph.eval (assignmentOfSet K) root = false →
        K ⊆ graph.zeroChannelSet assignment := by
  let formula := graph.finiteForestZeroSystem b target root
  have dual : Controller.Horn.DualHorn formula :=
    relabel_dualHorn graph.zeroIndex _ (graph.forestZeroSystem_dualHorn guarded b target root)
  obtain ⟨model, upper⟩ := compact_worklist_lifted formula dual values returned
  let assignment := liftTrue formula (fun slot => values[slot.val]) ∘ graph.zeroIndex
  have sourceModel : Satisfies assignment (graph.zeroSystem b target root ∅ ∅) :=
    (graph.forestZeroSystem_equivalent b target root assignment).mp
      ((satisfies_relabel graph.zeroIndex _ _).mp model)
  have sourceUpper : ∀ other, Satisfies other (graph.zeroSystem b target root ∅ ∅) →
      Controller.Horn.Below other assignment := by
    intro other satisfied coordinate positive
    have finiteModel : Satisfies (other ∘ graph.zeroIndex.symm) formula := by
      apply (satisfies_relabel graph.zeroIndex _ _).mpr
      simpa only [Function.comp_assoc, Equiv.symm_apply_apply, Function.comp_def] using
        (graph.forestZeroSystem_equivalent b target root other).mpr satisfied
    have bound := upper _ finiteModel (graph.zeroIndex coordinate)
      (by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using positive)
    exact bound
  obtain ⟨sound, greatest⟩ := graph.greatest_model_projects_to_greatest_zero guarded
    b target root ∅ ∅ assignment sourceModel sourceUpper
  exact ⟨⟨sound.1, sound.2.2⟩, fun K eligible zero =>
    greatest K eligible (by simp [ExtendsFixed]) zero⟩

end Controller.Cost.ForestGreatestZero
