module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessMeaning

@[expose] public section

/-! Returned witness tags identify the actual baseline or head candidate that made a root true. -/
namespace Controller.Cost.SharedWitnessDecode
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.SharedWitnessMeaning

def rootWord (graph : DAG n) (words : List (Word width))
    (lengths : words.length = graph.roots.length) (index : Fin graph.roots.length) : Word width :=
  words[index.val]'(by rw [lengths]; exact index.isLt)

set_option maxHeartbeats 2000000 in
theorem step_source (graph : DAG n) (values : Assignment n) (head : Nat) (flag : Bool)
    (words : List (Word width)) (lengths : words.length = graph.roots.length) (index : Fin graph.roots.length) :
    rootWord graph (SharedHeadLoop.witnessStep graph values head flag words)
      (step_length graph values head flag words lengths) index = rootWord graph words lengths index ∨
    (seenAt graph values head flag graph.roots[index.val] = true ∧
      rootWord graph (SharedHeadLoop.witnessStep graph values head flag words)
        (step_length graph values head flag words lengths) index = word width head) := by
  by_cases bound : head < n
  · simp only [rootWord, SharedHeadLoop.witnessStep, seenAt, dite_eq_left bound]
    split
    · simp_all
    · simp only [SharedRootAggregate.updated, List.getElem_zipWith, List.getElem_map]
      cases truth : graph.eval (SharedCandidateProbe.enabled values ⟨head, bound⟩) graph.roots[index.val] <;> simp_all
  · simp [rootWord, SharedHeadLoop.witnessStep, seenAt, bound]

set_option maxHeartbeats 2000000 in
theorem fold_source (graph : DAG n) (values : Assignment n) (head : Nat) (flags : List Bool)
    (words : List (Word width)) (lengths : words.length = graph.roots.length) (index : Fin graph.roots.length) :
    rootWord graph (SharedHeadLoop.witnessFold graph values head flags words)
      (fold_length graph values head flags words lengths) index = rootWord graph words lengths index ∨
    ∃ (offset : Nat) (valid : offset < flags.length),
      seenAt graph values (head + offset) (flags[offset]'valid) graph.roots[index.val] = true ∧
      rootWord graph (SharedHeadLoop.witnessFold graph values head flags words)
        (fold_length graph values head flags words lengths) index = word width (head + offset) := by
  induction flags generalizing head words with
  | nil => exact Or.inl rfl
  | cons flag rest ih =>
    have next := ih (head + 1) (SharedHeadLoop.witnessStep graph values head flag words)
      (step_length graph values head flag words lengths)
    rcases next with old | ⟨offset, valid, active, tag⟩
    · rcases step_source graph values head flag words lengths index with unchanged | ⟨active, tag⟩
      · exact Or.inl (old.trans unchanged)
      · exact Or.inr ⟨0, by simp, by simpa using active, by simpa only [SharedHeadLoop.witnessFold, Nat.add_zero] using old.trans tag⟩
    · refine Or.inr ⟨offset + 1, by simp; omega, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using active
      · simpa [SharedHeadLoop.witnessFold, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tag

def tag (graph : DAG n) (T F : Finset (Fin n)) (width : Nat) (index : Fin graph.roots.length) : Word width :=
  rootWord graph (SharedHeadLoop.witnessFold graph (assignmentOfSet T) 0
    ((List.finRange n).map (assignmentOfSet F)) (SharedBaselineInitialize.witnesses graph (assignmentOfSet T) width))
    (fold_length graph (assignmentOfSet T) 0 _ _ (by simp)) index

set_option maxHeartbeats 2000000 in
theorem baseline_source (graph : DAG n) (values : Assignment n) (width : Nat) (index : Fin graph.roots.length) :
    rootWord graph (SharedBaselineInitialize.witnesses graph values width) (by simp) index = word width (n + 1) ∨
      (rootWord graph (SharedBaselineInitialize.witnesses graph values width) (by simp) index = word width n ∧
        graph.eval values graph.roots[index.val] = true) := by
  cases nonempty : (List.finRange n).any values with
  | false => simp [rootWord, SharedBaselineInitialize.witnesses, nonempty]
  | true =>
    simp only [rootWord, SharedBaselineInitialize.witnesses, nonempty, ite_true, SharedRootAggregate.updated,
      List.getElem_zipWith, List.getElem_map, List.getElem_replicate]
    cases truth : graph.eval values graph.roots[index.val] <;> simp [truth]

set_option maxHeartbeats 2000000 in
theorem candidate_source (graph : DAG n) (T F : Finset (Fin n)) (width : Nat) (index : Fin graph.roots.length)
    (found : tag graph T F width index ≠ word width (n + 1)) :
    (tag graph T F width index = word width n ∧ graph.eval (assignmentOfSet T) graph.roots[index.val] = true) ∨
      ∃ channel : Fin n, channel ∉ T ∧ channel ∉ F ∧ tag graph T F width index = word width channel.val ∧
        graph.eval (assignmentOfSet (insert channel T)) graph.roots[index.val] = true := by
  have source := fold_source graph (assignmentOfSet T) 0 ((List.finRange n).map (assignmentOfSet F))
    (SharedBaselineInitialize.witnesses graph (assignmentOfSet T) width) (by simp) index
  rcases source with old | ⟨offset, valid, active, returned⟩
  · rcases baseline_source graph (assignmentOfSet T) width index with absent | ⟨baseline, truth⟩
    · exact False.elim (found (old.trans absent))
    · exact Or.inl ⟨old.trans baseline, truth⟩
  · have bound : offset < n := by simpa using valid
    let channel : Fin n := ⟨offset, bound⟩
    have observed : (!(assignmentOfSet T channel || assignmentOfSet F channel) &&
        graph.eval (SharedCandidateProbe.enabled (assignmentOfSet T) channel) graph.roots[index.val]) = true := by
      simpa [seenAt, bound, channel] using active
    have pair : (!(assignmentOfSet T channel || assignmentOfSet F channel)) = true ∧
        graph.eval (SharedCandidateProbe.enabled (assignmentOfSet T) channel) graph.roots[index.val] = true := by
      simpa only [Bool.and_eq_true] using observed
    have absent : channel ∉ T ∧ channel ∉ F := by simpa [assignmentOfSet] using pair.1
    exact Or.inr ⟨channel, absent.1, absent.2, by simpa [tag, channel] using returned,
      by simpa only [SharedCandidateProbe.enabled_set] using pair.2⟩

def decode (T : Finset (Fin n)) (value : Word width) : Finset (Fin n) :=
  if bound : value.val < n then insert ⟨value.val, bound⟩ T else T

theorem decode_baseline (T : Finset (Fin n)) (fits : n < 2 ^ width) : decode T (word width n) = T := by
  simp [decode, word, Nat.mod_eq_of_lt fits]

theorem decode_channel (T : Finset (Fin n)) (channel : Fin n) (fits : n < 2 ^ width) :
    decode T (word width channel.val) = insert channel T := by
  simp [decode, word, Nat.mod_eq_of_lt (by omega : channel.val < 2 ^ width), channel.isLt]

theorem decoded_true (graph : DAG n) (T F : Finset (Fin n)) (width : Nat) (index : Fin graph.roots.length)
    (consistent : FixedConsistent T F) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (found : tag graph T F width index ≠ word width (n + 1)) :
    ExtendsFixed T F (decode T (tag graph T F width index)) ∧
      graph.eval (assignmentOfSet (decode T (tag graph T F width index))) graph.roots[index.val] = true := by
  have size := graph.countedSize_eq
  have fits : n < 2 ^ width := by omega
  rcases candidate_source graph T F width index found with ⟨baseline, truth⟩ | ⟨channel, notTrue, notFalse, returned, truth⟩
  · rw [baseline, decode_baseline T fits]
    exact ⟨extendsFixed_self consistent, truth⟩
  · rw [returned, decode_channel T channel fits]
    exact ⟨⟨Finset.subset_insert _ _, Finset.disjoint_insert_left.mpr ⟨notFalse, consistent⟩⟩, truth⟩

theorem decoded_extension (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (width : Nat) (index : Fin graph.roots.length) (consistent : FixedConsistent (extensionBase b target T) F)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (found : tag graph (extensionBase b target T) F width index ≠ word width (n + 1)) :
    let K := decode (extensionBase b target T) (tag graph (extensionBase b target T) F width index)
    Admissible b target K ∧ ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) graph.roots[index.val] = true := by
  obtain ⟨extension, truth⟩ := decoded_true graph (extensionBase b target T) F width index consistent capacity found
  obtain ⟨fixed, forced⟩ := extensionBase_extends b target T F _ extension
  exact ⟨⟨graph.nonempty_of_eval_true _ _ truth, forced⟩, fixed, truth⟩

end Controller.Cost.SharedWitnessDecode
