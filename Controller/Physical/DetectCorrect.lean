module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Detect
public import Controller.Physical.DetectionBridge

@[expose] public section

/-! Constructive physical correctness of the supplied-structure guarded
detector. Returned primary inputs detect the bridge fault, and an absent
result proves undetectability. Output indices count the original root list,
including repeated observations. -/
namespace Controller.Decoder.DAG

def observations (graph : Controller.Decoder.DAG n) :
    Fin graph.roots.length → Controller.Assignment n → Bool :=
  fun index assignment => graph.eval assignment (graph.roots.get index)

end Controller.Decoder.DAG

namespace Controller.Physical

theorem bridge_detectable_iff_root {n b : Nat} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (graph : Decoder.DAG n) :
    BridgeDetectable (b := b) bridge drive graph.observations ↔
      drive = true ∧ ∃ root ∈ graph.roots,
        ∃ K, Admissible b bridge.target K ∧
          graph.eval (assignmentOfSet K) root ≠
            graph.eval (assignmentOfSet {bridge.target}) root := by
  rw [bridge_detectable_iff_exists_output bridge hb]
  constructor
  · rintro ⟨hd, K, hK, index, differs⟩
    exact ⟨hd, graph.roots.get index, List.get_mem _ _, K, hK, differs⟩
  · rintro ⟨hd, root, present, K, hK, differs⟩
    obtain ⟨index, indexRoot⟩ := List.get_of_mem present
    refine ⟨hd, K, hK, index, ?_⟩
    change graph.eval (assignmentOfSet K) (graph.roots.get index) ≠
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get index)
    rw [indexRoot]
    exact differs

/-- A physical detecting test exists exactly when one observed branch query
succeeds. This semantic equivalence leaves executable propagation and costs
to their respective implementation and resource refinements. -/
theorem bridge_detectable_iff_branch_queries {n b : Nat} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (graph : Decoder.DAG n) (guarded : graph.Guarded) :
    BridgeDetectable (b := b) bridge drive graph.observations ↔
      drive = true ∧ ∃ root ∈ graph.roots,
        (if graph.eval (assignmentOfSet {bridge.target}) root then
          CNF.Satisfiable (graph.zeroSystem b bridge.target root ∅ ∅)
        else ∃ head, graph.eval (assignmentOfSet
          (Decoder.trueCandidate b bridge.target head)) root = true) := by
  rw [bridge_detectable_iff_root bridge hb]
  constructor
  · rintro ⟨hd, root, present, discrepancy⟩
    exact ⟨hd, root, present,
      (graph.discrepancy_iff_branches guarded b bridge.target root).mp discrepancy⟩
  · rintro ⟨hd, root, present, query⟩
    exact ⟨hd, root, present,
      (graph.discrepancy_iff_branches guarded b bridge.target root).mpr query⟩

/-- The supplied-structure detector returns actual primary inputs. The bridge
wire in every returned test is true. -/
def detectInput {n b : Nat} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (graph : Decoder.DAG n) : Option (PrimaryInput n b) :=
  (graph.detectSet b bridge.target drive).map (realizeBridge bridge hb)

theorem detectInput_none_iff {n b : Nat} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (graph : Decoder.DAG n) (guarded : graph.Guarded) :
    detectInput bridge hb drive graph = none ↔
      ¬ BridgeDetectable (b := b) bridge drive graph.observations := by
  rw [detectInput, Option.map_eq_none_iff, graph.detectSet_none_iff guarded,
    bridge_detectable_iff_root bridge hb]

theorem detectInput_some {n b : Nat} (bridge : Bridge n) (hb : 0 < b)
    (drive : Bool) (graph : Decoder.DAG n) (guarded : graph.Guarded)
    (input : PrimaryInput n b) (returned : detectInput bridge hb drive graph = some input) :
    BridgeInputDetects bridge drive graph.observations input true := by
  obtain ⟨K, found, rfl⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨rfl, eligible, root, present, differs⟩ :=
    graph.detectSet_some guarded b bridge.target drive K found
  apply (realizeBridge_detects_iff bridge hb K eligible graph.observations).mpr
  obtain ⟨index, indexRoot⟩ := List.get_of_mem present
  refine ⟨index, ?_⟩
  change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get index) ≠
    graph.eval (assignmentOfSet K) (graph.roots.get index)
  rw [indexRoot]
  exact Ne.symm differs

end Controller.Physical
