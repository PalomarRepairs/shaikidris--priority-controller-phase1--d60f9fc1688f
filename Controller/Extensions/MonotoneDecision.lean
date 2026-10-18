module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralDecision

@[expose] public section

/-! Direct monotone witnesses: the full set for a healthy-zero output, and
a singleton for a healthy-one output with more than one available bus. -/
namespace Controller.Extensions.MonotoneDecision
open Controller.Decoder Controller.Decoder.DAG Controller.Extensions.GateBasis
open Controller.Extensions.LiteralScan

variable {n : Nat}

inductive Descriptor (n : Nat) where
  | full
  | single (channel : Channel n)

def Descriptor.set : Descriptor n → Finset (Channel n)
  | .full => Finset.univ
  | .single c => {c}

def singletonBit (graph : DAG n) (root : Fin graph.nodeCount) (c : Nat) : Bool :=
  if h : c < n then graph.eval (assignmentOfSet {⟨c, h⟩}) root else false

@[simp] theorem singletonBit_channel (graph : DAG n) (root : Fin graph.nodeCount) (c : Channel n) :
    singletonBit graph root c.val = graph.eval (assignmentOfSet {c}) root := by simp [singletonBit, c.isLt]

def decision (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) : Option (Descriptor n) :=
  if singletonBit graph root target.val then
    if b = 1 then none
    else (LiteralDecision.toChannel (firstHit (fun c => !singletonBit graph root c) 0 n)).map Descriptor.single
  else if graph.eval (assignmentOfSet Finset.univ) root then some .full else none

theorem decision_eq (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) :
    decision graph b target root =
      if graph.eval (assignmentOfSet {target}) root then
        if b = 1 then none else ((List.finRange n).find? (fun c => !graph.eval (assignmentOfSet {c}) root)).map Descriptor.single
      else if graph.eval (assignmentOfSet Finset.univ) root then some .full else none := by
  rw [decision, singletonBit_channel,
    LiteralDecision.toChannel_find (fun c => !graph.eval (assignmentOfSet {c}) root)
      (fun c => !singletonBit graph root c) (by intro c; rw [singletonBit_channel])]

theorem decision_some (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount)
    (d : Descriptor n) (returned : decision graph b target root = some d) :
    Admissible b target d.set ∧
      graph.eval (assignmentOfSet d.set) root ≠ graph.eval (assignmentOfSet {target}) root := by
  rw [decision_eq] at returned
  split at returned
  next healthy =>
    split at returned
    · simp at returned
    next notOne =>
      obtain ⟨c, found, rfl⟩ := Option.map_eq_some_iff.mp returned
      have bit : graph.eval (assignmentOfSet {c}) root = false := by simpa using List.find?_some found
      exact ⟨⟨Finset.singleton_nonempty _, fun one => (notOne one).elim⟩,
        by change graph.eval (assignmentOfSet {c}) root ≠ graph.eval (assignmentOfSet {target}) root
           rw [bit, healthy]; decide⟩
  next unhealthy =>
    split at returned
    next full =>
      cases returned
      exact ⟨⟨⟨target, Finset.mem_univ _⟩, fun _ => Finset.mem_univ _⟩,
        by simpa only [Descriptor.set, full] using Ne.symm unhealthy⟩
    · simp at returned

theorem decision_none_iff (graph : DAG n) (noGuards : NoNegativeGuards graph)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) :
    decision graph b target root = none ↔ ¬∃ K, Admissible b target K ∧
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  constructor
  · intro missing ⟨K, eligible, different⟩
    rw [decision_eq] at missing
    cases healthy : graph.eval (assignmentOfSet {target}) root with
    | false =>
      have truth : graph.eval (assignmentOfSet K) root = true := by cases h : graph.eval (assignmentOfSet K) root <;> simp_all
      have full := (monotone_true_full graph noGuards b target root).mp ⟨K, eligible, truth⟩
      simp [healthy, full] at missing
    | true =>
      have zero : graph.eval (assignmentOfSet K) root = false := by cases h : graph.eval (assignmentOfSet K) root <;> simp_all
      obtain ⟨c, bit⟩ := (monotone_false_minimal graph noGuards b target root).mp ⟨K, eligible, zero⟩
      by_cases one : b = 1
      · have truth := eval_monotone graph noGuards {target} K
          (by simpa only [Finset.singleton_subset_iff] using eligible.2 one) root healthy
        simp [zero] at truth
      · have low : graph.eval (assignmentOfSet {c}) root = false := by simpa [trueCandidate, one] using bit
        have absent : (List.finRange n).find? (fun d => !graph.eval (assignmentOfSet {d}) root) = none := by
          simpa [healthy, one] using missing
        have rejects := List.find?_eq_none.mp absent c (List.mem_finRange c)
        exact rejects (by simp [low])
  · intro absent
    cases h : decision graph b target root with
    | none => rfl
    | some d => exact (absent ⟨d.set, decision_some graph b target root d h⟩).elim

def search (graph : DAG n) (b : Nat) (target : Channel n) : Option (Finset (Channel n)) :=
  firstSuccess (fun root => (decision graph b target root).map Descriptor.set) graph.roots

theorem search_some (graph : DAG n) (b : Nat) (target : Channel n) (K : Finset (Channel n))
    (found : search graph b target = some K) : Admissible b target K ∧ ∃ root ∈ graph.roots,
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  obtain ⟨root, member, returned⟩ := firstSuccess_some _ _ K found
  obtain ⟨d, chosen, rfl⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨eligible, different⟩ := decision_some graph b target root d chosen
  exact ⟨eligible, root, member, different⟩

theorem search_none_iff (graph : DAG n) (noGuards : NoNegativeGuards graph) (b : Nat) (target : Channel n) :
    search graph b target = none ↔ ¬∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  simp only [search, firstSuccess_none_iff, Option.map_eq_none_iff, decision_none_iff graph noGuards]
  aesop

end Controller.Extensions.MonotoneDecision
