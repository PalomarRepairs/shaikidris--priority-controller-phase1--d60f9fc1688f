module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedHealthyCandidates
public import Controller.Decoder.Extend

@[expose] public section

/-! Candidate witness tags record exactly the root truths encountered by the shared loop. -/
namespace Controller.Cost.SharedWitnessMeaning
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram

def seenAt (graph : DAG n) (values : Assignment n) (head : Nat) (excluded : Bool)
    (root : Fin graph.nodeCount) : Bool :=
  if bound : head < n then
    let channel : Fin n := ⟨head, bound⟩
    !(values channel || excluded) && graph.eval (SharedCandidateProbe.enabled values channel) root
  else false

def seen (graph : DAG n) (values : Assignment n) (head : Nat) (flags : List Bool)
    (root : Fin graph.nodeCount) : Bool :=
  match flags with
  | [] => false
  | flag :: rest => seenAt graph values head flag root || seen graph values (head + 1) rest root

theorem step_length (graph : DAG n) (values : Assignment n) (head : Nat) (flag : Bool)
    (witnesses : List (Word width)) (lengths : witnesses.length = graph.roots.length) :
    (SharedHeadLoop.witnessStep graph values head flag witnesses).length = graph.roots.length := by
  unfold SharedHeadLoop.witnessStep
  split
  · dsimp only
    split
    · exact lengths
    · simp [SharedRootAggregate.updated, List.length_zipWith, lengths]
  · exact lengths

theorem fold_length (graph : DAG n) (values : Assignment n) (head : Nat) (flags : List Bool)
    (witnesses : List (Word width)) (lengths : witnesses.length = graph.roots.length) :
    (SharedHeadLoop.witnessFold graph values head flags witnesses).length = graph.roots.length := by
  induction flags generalizing head witnesses with
  | nil => exact lengths
  | cons flag rest ih => exact ih (head + 1) _ (step_length graph values head flag witnesses lengths)

set_option maxHeartbeats 2000000 in
theorem step_tag (graph : DAG n) (values : Assignment n) (head : Nat) (flag : Bool)
    (witnesses : List (Word width)) (lengths : witnesses.length = graph.roots.length)
    (index : Fin graph.roots.length) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    (SharedHeadLoop.witnessStep graph values head flag witnesses)[index.val]'(by rw [step_length graph values head flag witnesses lengths]; exact index.isLt) ≠ word width (n + 1) ↔
      witnesses[index.val]'(by rw [lengths]; exact index.isLt) ≠ word width (n + 1) ∨
        seenAt graph values head flag graph.roots[index.val] = true := by
  have size := graph.countedSize_eq
  by_cases bound : head < n
  · have headFits : head < 2 ^ width := by omega
    have sentinelFits : n + 1 < 2 ^ width := by omega
    have distinct : word width head ≠ word width (n + 1) := by
      intro equal
      have numbers := congrArg Fin.val equal
      simp only [word, Nat.mod_eq_of_lt headFits, Nat.mod_eq_of_lt sentinelFits] at numbers
      omega
    simp only [SharedHeadLoop.witnessStep, seenAt, dite_eq_left bound]
    split
    · simp_all
    · simp only [SharedRootAggregate.updated, List.getElem_zipWith, List.getElem_map]
      cases value : graph.eval (SharedCandidateProbe.enabled values ⟨head, bound⟩) graph.roots[index.val] <;>
        simp_all
  · simp [SharedHeadLoop.witnessStep, seenAt, bound]

set_option maxHeartbeats 2000000 in
theorem fold_tag (graph : DAG n) (values : Assignment n) (head : Nat) (flags : List Bool)
    (witnesses : List (Word width)) (lengths : witnesses.length = graph.roots.length)
    (index : Fin graph.roots.length) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    (SharedHeadLoop.witnessFold graph values head flags witnesses)[index.val]'(by rw [fold_length graph values head flags witnesses lengths]; exact index.isLt) ≠ word width (n + 1) ↔
      witnesses[index.val]'(by rw [lengths]; exact index.isLt) ≠ word width (n + 1) ∨
        seen graph values head flags graph.roots[index.val] = true := by
  induction flags generalizing head witnesses with
  | nil => simp [SharedHeadLoop.witnessFold, seen]
  | cons flag rest ih =>
    have nextLengths := step_length graph values head flag witnesses lengths
    have next := ih (head + 1) (SharedHeadLoop.witnessStep graph values head flag witnesses) nextLengths
    have step := step_tag graph values head flag witnesses lengths index capacity
    simpa only [SharedHeadLoop.witnessFold, seen, step, Bool.or_eq_true, or_assoc] using next

set_option maxHeartbeats 2000000 in
theorem baseline_tag (graph : DAG n) (values : Assignment n) (width : Nat)
    (index : Fin graph.roots.length) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    (SharedBaselineInitialize.witnesses graph values width)[index.val]'(by simp) ≠ word width (n + 1) ↔
      (List.finRange n).any values = true ∧ graph.eval values graph.roots[index.val] = true := by
  have size := graph.countedSize_eq
  have nFits : n < 2 ^ width := by omega
  have sentinelFits : n + 1 < 2 ^ width := by omega
  have distinct : word width n ≠ word width (n + 1) := by
    intro equal
    have numbers := congrArg Fin.val equal
    simp only [word, Nat.mod_eq_of_lt nFits, Nat.mod_eq_of_lt sentinelFits] at numbers
    omega
  cases nonempty : (List.finRange n).any values with
  | false => simp [SharedBaselineInitialize.witnesses, nonempty]
  | true =>
    simp only [SharedBaselineInitialize.witnesses, nonempty, ite_true, SharedRootAggregate.updated,
      List.getElem_zipWith, List.getElem_map, List.getElem_replicate]
    cases value : graph.eval values graph.roots[index.val] <;> simp [value, distinct]

theorem candidate_tag (graph : DAG n) (values : Assignment n) (flags : List Bool) (width : Nat)
    (index : Fin graph.roots.length) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    (SharedHeadLoop.witnessFold graph values 0 flags (SharedBaselineInitialize.witnesses graph values width))[index.val]'(by
      rw [fold_length graph values 0 flags _ (by simp)]; exact index.isLt) ≠ word width (n + 1) ↔
      ((List.finRange n).any values = true ∧ graph.eval values graph.roots[index.val] = true) ∨
        seen graph values 0 flags graph.roots[index.val] = true := by
  rw [fold_tag graph values 0 flags _ (by simp) index capacity, baseline_tag graph values width index capacity]

theorem seen_indexed (graph : DAG n) (values : Assignment n) (head : Nat) (flags : List Bool)
    (root : Fin graph.nodeCount) :
    seen graph values head flags root = true ↔
      ∃ (index : Nat) (valid : index < flags.length),
        seenAt graph values (head + index) (flags[index]'valid) root = true := by
  induction flags generalizing head with
  | nil => simp [seen]
  | cons flag rest ih =>
    rw [seen, Bool.or_eq_true, ih]
    constructor
    · rintro (firstTruth | ⟨index, valid, truth⟩)
      · exact ⟨0, by simp, by simpa using firstTruth⟩
      · refine ⟨index + 1, by simp; omega, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using truth
    · rintro ⟨index, valid, truth⟩
      cases index with
      | zero => exact Or.inl (by simpa using truth)
      | succ index =>
        refine Or.inr ⟨index, by simp only [List.length_cons] at valid; omega, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using truth

theorem seen_set (graph : DAG n) (T F : Finset (Fin n)) (root : Fin graph.nodeCount) :
    seen graph (assignmentOfSet T) 0 ((List.finRange n).map (assignmentOfSet F)) root = true ↔
      ∃ channel : Fin n, channel ∉ T ∧ channel ∉ F ∧
        graph.eval (assignmentOfSet (insert channel T)) root = true := by
  rw [seen_indexed]
  constructor
  · rintro ⟨index, valid, truth⟩
    have bound : index < n := by simpa using valid
    let channel : Fin n := ⟨index, bound⟩
    have observed : (!(assignmentOfSet T channel || assignmentOfSet F channel) &&
        graph.eval (SharedCandidateProbe.enabled (assignmentOfSet T) channel) root) = true := by
      simpa [seenAt, bound, channel] using truth
    have pair : (!(assignmentOfSet T channel || assignmentOfSet F channel)) = true ∧
        graph.eval (SharedCandidateProbe.enabled (assignmentOfSet T) channel) root = true := by
      simpa only [Bool.and_eq_true] using observed
    obtain ⟨allowed, active⟩ := pair
    have absent : channel ∉ T ∧ channel ∉ F := by simpa [assignmentOfSet] using allowed
    exact ⟨channel, absent.1, absent.2, by simpa only [SharedCandidateProbe.enabled_set] using active⟩
  · rintro ⟨channel, notTrue, notFalse, active⟩
    refine ⟨channel.val, by simp, ?_⟩
    simpa [seenAt, channel.isLt, assignmentOfSet, notTrue, notFalse, SharedCandidateProbe.enabled_set] using active

theorem candidate_set_tag (graph : DAG n) (T F : Finset (Fin n)) (width : Nat)
    (index : Fin graph.roots.length) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    (SharedHeadLoop.witnessFold graph (assignmentOfSet T) 0 ((List.finRange n).map (assignmentOfSet F))
      (SharedBaselineInitialize.witnesses graph (assignmentOfSet T) width))[index.val]'(by
        rw [fold_length graph (assignmentOfSet T) 0 _ _ (by simp)]; exact index.isLt) ≠ word width (n + 1) ↔
      graph.eval (assignmentOfSet T) graph.roots[index.val] = true ∨
        ∃ channel : Fin n, channel ∉ T ∧ channel ∉ F ∧
          graph.eval (assignmentOfSet (insert channel T)) graph.roots[index.val] = true := by
  rw [candidate_tag graph (assignmentOfSet T) _ width index capacity, seen_set]
  have baseline : ((List.finRange n).any (assignmentOfSet T) = true ∧
      graph.eval (assignmentOfSet T) graph.roots[index.val] = true) ↔
      graph.eval (assignmentOfSet T) graph.roots[index.val] = true := by
    constructor
    · exact And.right
    · intro active
      exact ⟨by rw [SharedBaselineNonempty.any_set]; simpa using graph.nonempty_of_eval_true T graph.roots[index.val] active, active⟩
  rw [baseline]

theorem extension_tag (graph : DAG n) (guarded : graph.Guarded)
    (b : Nat) (target : Fin n) (T F : Finset (Fin n)) (width : Nat)
    (index : Fin graph.roots.length) (consistent : FixedConsistent (extensionBase b target T) F)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    (SharedHeadLoop.witnessFold graph (assignmentOfSet (extensionBase b target T)) 0
      ((List.finRange n).map (assignmentOfSet F))
      (SharedBaselineInitialize.witnesses graph (assignmentOfSet (extensionBase b target T)) width))[index.val]'(by
        rw [fold_length graph (assignmentOfSet (extensionBase b target T)) 0 _ _ (by simp)]; exact index.isLt) ≠ word width (n + 1) ↔
      ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) graph.roots[index.val] = true := by
  rw [candidate_set_tag graph (extensionBase b target T) F width index capacity,
    graph.admissible_fixed_true_iff_candidate guarded b target T F graph.roots[index.val] consistent]
  simp [extensionCandidates, and_assoc]

end Controller.Cost.SharedWitnessMeaning
