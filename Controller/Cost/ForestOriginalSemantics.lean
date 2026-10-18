module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestRootProjection

@[expose] public section

/-! Physical interpretation of the channel bits returned by the original-root
forest execution. The eligible set is the set encoded in the returned output. -/
namespace Controller.Cost.ForestOriginalSemantics
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {n width b : Nat}

theorem positive_output_physical (graph : DAG n) (bridge : Physical.Bridge n)
    (hb : 0 < b) (before after : List (Word width))
    (returned : positiveOutput width (healthyGraph graph bridge.target false)
      b bridge.target before after) :
    ∃ K : Finset (Channel n), Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge hb K) true ∧
      after = List.ofFn (fun channel : Channel n =>
        boolWord width (assignmentOfSet K channel)) ++ before := by
  obtain ⟨position, K, eligible, value, emitted⟩ := returned
  let family := healthyGraph graph bridge.target false
  have member : family.roots.get position ∈ family.roots := List.get_mem _ _
  have original := (Forest.healthyFamily_membership graph bridge.target false _).mp member
  obtain ⟨index, same⟩ := List.mem_iff_get.mp original.1
  refine ⟨K, eligible, ?_, emitted⟩
  apply (Physical.realizeBridge_detects_iff bridge hb K eligible graph.observations).mpr
  refine ⟨index, ?_⟩
  have faulty : graph.eval (assignmentOfSet K) (family.roots.get position) = true := by
    simpa only [family, healthyGraph, Forest.rootFamily_eval] using value
  change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get index) ≠
    graph.eval (assignmentOfSet K) (graph.roots.get index)
  rw [same, original.2, faulty]
  decide

theorem negative_output_physical (graph : DAG n) (forest : graph.FormulaForest)
    (bridge : Physical.Bridge n) (hb : 0 < b) (rows : List Row)
    (matched : RowsMatch graph rows) (output : List (Word width))
    (returned : negativeOutput width (healthyGraph graph bridge.target true) rows
      (healthyRootIds graph bridge.target true)
      (Forest.rootFamily_rows graph _ rows matched) b bridge.target output) :
    ∃ original : Fin graph.roots.length, ∃ K : Finset (Channel n),
      Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge hb K) true ∧
      ∃ previous : List (Word width),
        output = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  obtain ⟨position, _, witness⟩ := returned
  exact Forest.healthy_one_output_original graph forest rows matched b hb bridge
    _ _ output position witness

end Controller.Cost.ForestOriginalSemantics

namespace Controller.Cost.ForestOriginalSemantics
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
variable {n width b : Nat}

theorem original_decision_iff (graph : DAG n) (forest : graph.FormulaForest)
    (bridge : Physical.Bridge n) (hb : 0 < b) (rows : List Row)
    (matched : RowsMatch graph rows) :
    (positiveModel (healthyGraph graph bridge.target false) b bridge.target ∨
      negativeModel width (healthyGraph graph bridge.target true) rows
        (healthyRootIds graph bridge.target true)
        (Forest.rootFamily_rows graph _ rows matched) b bridge.target) ↔
      Physical.BridgeDetectable (b := b) bridge true graph.observations := by
  unfold healthyGraph healthyRootIds
  rw [Physical.bridge_detectable_iff_root bridge hb]
  simp only [true_and]
  rw [Forest.mixed_root_discrepancy]
  apply or_congr
  · constructor
    · rintro ⟨position, K, eligible, value⟩
      exact ⟨_, List.get_mem _ _, K, eligible,
        by simpa only [healthyGraph, Forest.rootFamily_eval] using value⟩
    · rintro ⟨root, member, K, eligible, value⟩
      obtain ⟨position, same⟩ := List.mem_iff_get.mp member
      refine ⟨position, K, eligible, ?_⟩
      simpa only [same, healthyGraph, Forest.rootFamily_eval] using value
  · unfold negativeModel
    rw [ForestZeroOutputImage.zero_stream_constructor_iff
      (Forest.rootFamily graph (Forest.healthyPositions graph bridge.target true))
      (Forest.rootFamily_guarded graph forest.1 _)]
    constructor
    · rintro ⟨K, eligible, position, value⟩
      exact ⟨_, List.get_mem _ _, K, eligible,
        by simpa only [healthyGraph, Forest.rootFamily_eval] using value⟩
    · rintro ⟨root, member, K, eligible, value⟩
      obtain ⟨position, same⟩ := List.mem_iff_get.mp member
      refine ⟨K, eligible, position, ?_⟩
      simpa only [same, healthyGraph, Forest.rootFamily_eval] using value

end Controller.Cost.ForestOriginalSemantics

namespace Controller.Cost.ForestOriginalSemantics
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
theorem original_physical_execution (graph : DAG n) (forest : graph.FormulaForest)
    (b : Nat) (bridge : Physical.Bridge n) (hb : 0 < b) (rows : List Row) (originalRoots : List Nat)
    (originalMatched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows originalMatched)
    (originalRootsMatch : RootsMatch graph originalRoots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (rest output : List (Word (chosenMixedWidth graph)))
    (address loaded temporary : Word (chosenMixedWidth graph))
    (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    ∃ answer : Bool, ∃ final ticks peak storePeak,
      Execution (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {bridge.target}))) (healthyGraph graph bridge.target false) (healthyGraph graph bridge.target true) rows (healthyRootIds graph bridge.target false) (healthyRootIds graph bridge.target true)
        (Forest.rootFamily_rows graph (Forest.healthyPositions graph bridge.target true) rows originalMatched) weights b bridge.target (original_descriptor_capacity graph forest bridge.target).1 (original_descriptor_capacity graph forest bridge.target).2) (classificationInitial (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {bridge.target}) bridge.target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth graph) (if answer then 1 else 0) ∧
      ticks ≤ 4721 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) + 450 ∧
      peak ≤ 169 * (n + graph.nodeCount + graph.roots.length + graph.childIncidences + graph.guardIncidences) +
        57 + rest.length + output.length ∧
      (runAll (source n rows) weights b bridge.target (healthyRootIds graph bridge.target false)).2.operations ≤ 4 * forestSize graph ∧
      (runAll (source n rows) weights b bridge.target (healthyRootIds graph bridge.target false)).2.arithmetic ≤ 8 * forestSize graph ∧
      StoreTrace weights (runAll (source n rows) weights b bridge.target (healthyRootIds graph bridge.target false)).1 b bridge.target
        ⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩
        (runAll (source n rows) weights b bridge.target (healthyRootIds graph bridge.target false)).2 storePeak ∧
      programWords (mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows originalRoots (assignmentOfSet {bridge.target})))
        (healthyGraph graph bridge.target false) (healthyGraph graph bridge.target true) rows
        (healthyRootIds graph bridge.target false) (healthyRootIds graph bridge.target true)
        (Forest.rootFamily_rows graph (Forest.healthyPositions graph bridge.target true) rows originalMatched)
        weights b bridge.target (original_descriptor_capacity graph forest bridge.target).1
        (original_descriptor_capacity graph forest bridge.target).2) + peak +
        (storePeak + sourceWords n rows + controlBudget (source n rows) graph.nodeCount +
          (6 * graph.nodeCount + 2 * graph.childIncidences + 2 * graph.guardIncidences +
            2 * (healthyGraph graph bridge.target false).roots.length + 5) +
            6 * (healthyGraph graph bridge.target false).roots.length + 7) ≤
          3558 * forestSize graph + 2106 + rest.length + output.length ∧
      (answer = true ↔ Physical.BridgeDetectable (b := b) bridge true graph.observations) ∧
      (answer = true → ∃ K : Finset (Channel n), Admissible b bridge.target K ∧
        Physical.BridgeInputDetects bridge true graph.observations
          (Physical.realizeBridge bridge hb K) true ∧
        ∃ previous : List (Word (chosenMixedWidth graph)),
          final.output = List.ofFn (fun channel : Channel n =>
            boolWord (chosenMixedWidth graph) (assignmentOfSet K channel)) ++ previous)
 := by
  obtain ⟨answer, final, ticks, peak, storePeak, trace, halted, tag, time, space,
    operations, arithmetic, stored, total, meaning, returned⟩ :=
    original_total_resource_execution graph forest b bridge.target rows originalRoots
      originalMatched heads originalRootsMatch weights nonnegative rest output
      address loaded temporary saved
  refine ⟨answer, final, ticks, peak, storePeak, trace, halted, tag, time, space,
    operations, arithmetic, stored, total,
    meaning.trans (original_decision_iff graph forest bridge hb rows originalMatched), ?_⟩
  intro yes
  rcases returned yes with positive | negative
  · obtain ⟨K, eligible, detects, emitted⟩ :=
      positive_output_physical graph bridge hb output final.output positive
    exact ⟨K, eligible, detects, output, emitted⟩
  · obtain ⟨index, K, eligible, detects, previous, emitted⟩ :=
      negative_output_physical graph forest bridge hb rows originalMatched final.output negative
    refine ⟨K, eligible, detects, word (chosenMixedWidth graph) 1 :: previous, ?_⟩
    simpa only [List.ofFn_eq_map, boolWord, ForestZeroChannelEmit.bitWord] using emitted

end Controller.Cost.ForestOriginalSemantics
