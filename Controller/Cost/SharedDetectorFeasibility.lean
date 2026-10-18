module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorData

@[expose] public section

namespace Controller.Cost.SharedDetectorFeasibility
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.GateProgram

def AtRoot (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (position : Fin graph.roots.length) : Prop :=
  ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
    graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] ≠
      graph.eval (assignmentOfSet K) graph.roots[position.val]

theorem healthy_iff (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (position : Fin graph.roots.length)
    (healthy : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] = true) :
    AtRoot parameters graph T F position ↔ ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
      ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) graph.roots[position.val] = false := by
  unfold AtRoot
  rw [healthy]
  constructor
  · rintro ⟨K, eligible, fixed, different⟩
    refine ⟨K, eligible, fixed, ?_⟩
    cases value : graph.eval (assignmentOfSet K) graph.roots[position.val] <;> simp_all
  · rintro ⟨K, eligible, fixed, zero⟩
    exact ⟨K, eligible, fixed, by rw [zero]; decide⟩

theorem candidate_iff (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (position : Fin graph.roots.length) (width : Nat)
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (unhealthy : graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[position.val] = false) :
    SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F width position ≠
      word width (parameters.channels + 1) ↔ AtRoot parameters graph T F position := by
  have tags := SharedWitnessMeaning.extension_tag graph guarded parameters.buses parameters.bridge.target T F width
    position consistent capacity
  change (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F width position ≠
    word width (parameters.channels + 1) ↔ _) at tags
  rw [tags]
  unfold AtRoot
  rw [unhealthy]
  constructor
  · rintro ⟨K, eligible, fixed, truth⟩
    exact ⟨K, eligible, fixed, by rw [truth]; decide⟩
  · rintro ⟨K, eligible, fixed, different⟩
    refine ⟨K, eligible, fixed, ?_⟩
    cases value : graph.eval (assignmentOfSet K) graph.roots[position.val] <;> simp_all

end Controller.Cost.SharedDetectorFeasibility
