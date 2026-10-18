module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.CompilerGateTrace

@[expose] public section

/-! Combined source traversal traces for every cached prefix-builder step.
Gate incidence mapping, cell copies, outer appends and builder updates are
charged together. Fixed template/word formation and array/RAM realization
remain separate. -/
namespace Controller.Cost.CompilerPrefixTrace
open Controller.Decoder Controller.Cost.GateProgram Controller.Cost.DAGProgram
open Controller.Cost.CompilerBuilder Controller.Cost.CompilerAppendTrace
open Controller.Cost.CompilerGateTrace

def Trace (graph : DAG n) (width base : Nat) :
    (length : Nat) → length ≤ graph.nodeCount → Nat → Prop
  | 0, _, visits => visits = 0
  | length + 1, bound, visits =>
    let earlier := prefixBuilder graph width base length (by omega)
    let gate := graph.node ⟨length, by omega⟩
    let chunk := gateCode width earlier.cursor gate
    ∃ previous mapped copied,
      Trace graph width base length (by omega) previous ∧
      GateTrace width earlier.cursor gate chunk mapped ∧
      BuilderTrace earlier chunk (earlier.append chunk) copied ∧
      visits = previous + mapped + copied

theorem prefix_linear (graph : DAG n) (width base : Nat) :
    ∀ length (bound : length ≤ graph.nodeCount),
      ∃ visits, Trace graph width base length bound visits ∧
        visits ≤ 61 * prefixWork graph length bound := by
  intro length
  induction length with
  | zero => intro bound; exact ⟨0, rfl, by simp [prefixWork]⟩
  | succ length ih =>
    intro bound
    have earlierBound : length ≤ graph.nodeCount := by omega
    obtain ⟨previous, previousTrace, previousBound⟩ := ih earlierBound
    let earlier := prefixBuilder graph width base length earlierBound
    let gate := graph.node ⟨length, by omega⟩
    let chunk := gateCode width earlier.cursor gate
    refine ⟨previous + traversalCost gate + (3 * chunk.length + 1), ?_, ?_⟩
    · exact ⟨previous, traversalCost gate, 3 * chunk.length + 1, previousTrace,
        gate_exists width earlier.cursor gate, builder_exists earlier chunk, rfl⟩
    · have gateBound := traversalCost_le gate
      have chunkBound := gateCode_length_le width earlier.cursor gate
      change chunk.length ≤ 12 * (1 + gate.children.length + gate.guardLabels.length) at chunkBound
      change previous + traversalCost gate + (3 * chunk.length + 1) ≤
        61 * (prefixWork graph length earlierBound + 1 + gate.children.length + gate.guardLabels.length)
      omega

theorem full_linear (graph : DAG n) (width base : Nat) :
    ∃ visits, Trace graph width base graph.nodeCount (Nat.le_refl _) visits ∧
      visits ≤ 61 * graph.countedSize ∧
      (prefixBuilder graph width base graph.nodeCount (Nat.le_refl _)).reversed.reverse =
        prefixCode graph width base graph.nodeCount (Nat.le_refl _) := by
  obtain ⟨visits, trace, bound⟩ := prefix_linear graph width base graph.nodeCount (Nat.le_refl _)
  have fullWork : prefixWork graph graph.nodeCount (Nat.le_refl _) ≤ graph.countedSize := by
    rw [prefixWork_eq]
    have equality : graph.nodeCount +
        (List.ofFn fun index : Fin graph.nodeCount => (graph.node (index.castLE (Nat.le_refl _))).children.length).sum +
        (List.ofFn fun index : Fin graph.nodeCount => (graph.node (index.castLE (Nat.le_refl _))).guardLabels.length).sum =
        graph.nodeCount + graph.childIncidences + graph.guardIncidences := by
      simp only [Fin.castLE, DAG.childIncidences, DAG.guardIncidences]
    rw [equality, DAG.countedSize_eq]; omega
  exact ⟨visits, trace, bound.trans (Nat.mul_le_mul_left 61 fullWork),
    (prefixBuilder_correct graph width base graph.nodeCount (Nat.le_refl _)).2⟩

end Controller.Cost.CompilerPrefixTrace
