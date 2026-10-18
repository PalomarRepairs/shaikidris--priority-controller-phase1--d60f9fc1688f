module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.Decoder
public import Mathlib.Data.Finset.Union

@[expose] public section

/-! Healthy-zero support summaries on the stored guarded DAG. The one-bus
target guard kills the whole support; it is not merely a deletion of the
target leaf. A surviving head constructs an admissible detecting input. -/
namespace Controller.NativeProof.DecoderSupport
open Controller

def support (graph : Decoder.DAG n) (b : Nat) (target : Channel n)
    (node : Fin graph.nodeCount) : Finset (Channel n) :=
  match graph.node node with
  | .zero => ∅
  | .input channel => {channel}
  | .disj children => children.toFinset.biUnion fun child =>
      support graph b target (graph.childIndex node child)
  | .guard child labels =>
      if b = 1 ∧ target ∈ labels then ∅
      else support graph b target (graph.childIndex node child) \ labels.toFinset
  | .liveAnd _ _ => ∅
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt node _

/-- A surviving support head makes the singleton (or one-bus target-plus-head)
candidate true. The result applies to intermediate nodes as an implication,
without identifying arbitrary intermediate truth with support membership. -/
theorem surviving_true (graph : Decoder.DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (node : Fin graph.nodeCount) (head : Channel n)
    (survives : head ∈ support graph b target node) :
    graph.eval (assignmentOfSet (Controller.Decoder.trueCandidate b target head)) node = true := by
  suffices general : ∀ bound, ∀ current : Fin graph.nodeCount, current.val = bound →
      head ∈ support graph b target current →
      graph.eval (assignmentOfSet (Controller.Decoder.trueCandidate b target head)) current = true by
    exact general node.val node rfl survives
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
    intro current position member
    rw [support] at member
    cases shape : graph.node current with
    | zero => simp [shape] at member
    | input channel =>
      have same : head = channel := by simpa [shape] using member
      rw [graph.eval_input _ _ _ shape]
      exact (assignmentOfSet_eq_true _ channel).mpr
        (same ▸ Controller.Decoder.head_mem_trueCandidate b target head)
    | disj children =>
      simp only [shape, Finset.mem_biUnion, List.mem_toFinset] at member
      obtain ⟨child, listed, tail⟩ := member
      rw [graph.eval_disj _ _ _ shape]
      exact List.any_eq_true.mpr ⟨child, listed,
        ih child.val (by simpa only [position] using child.isLt)
          (graph.childIndex current child) rfl tail⟩
    | guard child labels =>
      simp only [shape] at member
      split at member
      next killed => simp at member
      next allowed =>
        have tail := (Finset.mem_sdiff.mp member).1
        have headAbsent : head ∉ labels := by
          simpa only [List.mem_toFinset] using (Finset.mem_sdiff.mp member).2
        have childTrue := ih child.val (by simpa only [position] using child.isLt)
          (graph.childIndex current child) rfl tail
        rw [graph.eval_guard _ _ _ _ shape]
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false]
        refine ⟨childTrue, ?_⟩
        intro channel listed active
        have candidate := (assignmentOfSet_eq_true _ channel).mp active
        by_cases one : b = 1
        · have targetAbsent : target ∉ labels := fun present => allowed ⟨one, present⟩
          simp only [Controller.Decoder.trueCandidate, ite_eq_left one, Finset.mem_insert,
            Finset.mem_singleton] at candidate
          rcases candidate with same | same
          · exact headAbsent (same ▸ listed)
          · exact targetAbsent (same ▸ listed)
        · have same : channel = head := by
            simpa only [Controller.Decoder.trueCandidate, ite_eq_right one, Finset.mem_singleton] using candidate
          exact headAbsent (same ▸ listed)
    | liveAnd left right =>
      have permitted := guarded current
      simp [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] at permitted

/-- Every true node on an admissible channel set has a surviving true support
head. This is the semantic implication represented by the native summary. -/
theorem true_has_support (graph : Controller.Decoder.DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (eligible : Admissible b target K) (node : Fin graph.nodeCount)
    (active : graph.eval (assignmentOfSet K) node = true) :
    ∃ head ∈ support graph b target node, head ∈ K := by
  suffices general : ∀ bound, ∀ current : Fin graph.nodeCount, current.val = bound →
      graph.eval (assignmentOfSet K) current = true →
      ∃ head ∈ support graph b target current, head ∈ K by
    exact general node.val node rfl active
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
    intro current position currentTrue
    cases shape : graph.node current with
    | zero =>
      rw [graph.eval_zero _ _ shape] at currentTrue
      exact False.elim (Bool.false_ne_true currentTrue)
    | input channel =>
      rw [graph.eval_input _ _ _ shape] at currentTrue
      refine ⟨channel, ?_, (assignmentOfSet_eq_true _ _).mp currentTrue⟩
      rw [support]
      simp [shape]
    | disj children =>
      rw [graph.eval_disj _ _ _ shape] at currentTrue
      obtain ⟨child, listed, childTrue⟩ := List.any_eq_true.mp currentTrue
      obtain ⟨head, survives, present⟩ := ih child.val
        (by simpa only [position] using child.isLt) (graph.childIndex current child) rfl childTrue
      refine ⟨head, ?_, present⟩
      rw [support]
      simp only [shape, Finset.mem_biUnion, List.mem_toFinset]
      exact ⟨child, listed, survives⟩
    | guard child labels =>
      rw [graph.eval_guard _ _ _ _ shape] at currentTrue
      obtain ⟨childTrue, guardFalse⟩ := Bool.and_eq_true_iff.mp currentTrue
      have labelsAbsent : ∀ channel ∈ labels, channel ∉ K := by
        simpa only [Bool.not_eq_true', List.any_eq_false, assignmentOfSet_eq_true] using guardFalse
      have allowed : ¬(b = 1 ∧ target ∈ labels) := by
        rintro ⟨one, listed⟩
        exact labelsAbsent target listed (eligible.2 one)
      obtain ⟨head, survives, present⟩ := ih child.val
        (by simpa only [position] using child.isLt) (graph.childIndex current child) rfl childTrue
      refine ⟨head, ?_, present⟩
      rw [support]
      simp only [shape, ite_eq_right allowed, Finset.mem_sdiff, List.mem_toFinset]
      exact ⟨survives, fun listed => labelsAbsent head listed present⟩
    | liveAnd left right =>
      have permitted := guarded current
      simp [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] at permitted

theorem empty_support_false (graph : Controller.Decoder.DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (eligible : Admissible b target K) (node : Fin graph.nodeCount)
    (empty : support graph b target node = ∅) :
    graph.eval (assignmentOfSet K) node = false := by
  apply Bool.eq_false_of_not_eq_true
  intro active
  obtain ⟨head, survives, _⟩ := true_has_support graph guarded b target K eligible node active
  simp [empty] at survives

/-- A healthy-zero selected output cannot have surviving support under
discrepancy absence. This semantic argument does not use compiler output. -/
theorem root_support_empty (parameters : Native.Parameters)
    (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected)
    (output : Fin parameters.decoder.roots.length) (accepted : output ∈ selected)
    (healthy : parameters.observations output
      (assignmentOfSet {parameters.bridge.target}) = false) :
    support parameters.decoder parameters.buses parameters.bridge.target
      (parameters.decoder.roots.get output) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro head survives
  have faulty := surviving_true parameters.decoder guarded parameters.buses
    parameters.bridge.target (parameters.decoder.roots.get output) head survives
  have same := absent output accepted
    (Controller.Decoder.trueCandidate parameters.buses parameters.bridge.target head)
    (Controller.Decoder.trueCandidate_admissible _ _ _)
  change parameters.decoder.eval _ (parameters.decoder.roots.get output) = _ at same
  rw [faulty, healthy] at same
  exact Bool.false_ne_true same.symm

theorem source_unsat_root_support_empty (parameters : Native.Parameters)
    (raw : parameters.layout = .raw) (guarded : parameters.decoder.Guarded)
    (drive : parameters.drive = true)
    (unsat : CNF.Unsatisfiable (Native.SourceController.formula parameters))
    (output : Fin parameters.decoder.roots.length)
    (healthy : parameters.observations output
      (assignmentOfSet {parameters.bridge.target}) = false) :
    support parameters.decoder parameters.buses parameters.bridge.target
      (parameters.decoder.roots.get output) = ∅ :=
  root_support_empty parameters guarded {output}
    (Decoder.source_unsat_noDiscrepancy parameters raw drive unsat {output}) output
    (Finset.mem_singleton_self _) healthy

end Controller.NativeProof.DecoderSupport
