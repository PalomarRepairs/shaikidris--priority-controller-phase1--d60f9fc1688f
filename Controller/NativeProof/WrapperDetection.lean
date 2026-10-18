module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.Wrapper

@[expose] public section

/-! The selected detector changes only the root list of the stored guarded DAG. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Native Controller.Native.SourceController
variable {parameters : Parameters}

theorem eval_withRoots {n : Nat} (graph : Controller.Decoder.DAG n)
    (roots : List (Fin graph.nodeCount)) (values : Controller.Assignment n) (index : Fin graph.nodeCount) :
    (graph.withRoots roots).eval values index = graph.eval values index := by
  conv_lhs => rw [(graph.withRoots roots).eval_eq values index]
  conv_rhs => rw [graph.eval_eq values index]
  apply Controller.Decoder.Gate.eval_congr
  · intro channel member; rfl
  · intro child member
    exact eval_withRoots graph roots values (graph.childIndex index child)
termination_by index.val


def selectedGraph (parameters : Parameters) (outputs : List (Fin parameters.decoder.roots.length)) :
    Controller.Decoder.DAG parameters.channels :=
  parameters.decoder.withRoots (outputs.map parameters.decoder.roots.get)

def wrapperDetect (parameters : Parameters) (outputs : List (Fin parameters.decoder.roots.length)) :=
  (selectedGraph parameters outputs).detectSet parameters.buses parameters.bridge.target parameters.drive

theorem wrapperDetect_none_iff (parameters : Parameters) (guarded : parameters.decoder.Guarded)
    (outputs : List (Fin parameters.decoder.roots.length)) :
    wrapperDetect parameters outputs = none ↔
      (parameters.drive = true → Decoder.NoDiscrepancy parameters outputs.toFinset) := by
  rw [wrapperDetect, (selectedGraph parameters outputs).detectSet_none_iff (show (selectedGraph parameters outputs).Guarded from guarded)]
  constructor
  · intro absent drive output member K eligible
    apply Eq.symm
    by_contra different
    apply absent
    refine ⟨drive, parameters.decoder.roots.get output, ?_, K, eligible, ?_⟩
    · exact List.mem_map.mpr ⟨output, List.mem_toFinset.mp member, rfl⟩
    · simpa only [selectedGraph, eval_withRoots, Parameters.observations] using Ne.symm different
  · intro absent contradiction
    obtain ⟨drive, root, member, K, eligible, different⟩ := contradiction
    obtain ⟨output, accepted, same⟩ := List.mem_map.mp member
    subst root
    apply different
    simpa only [selectedGraph, eval_withRoots, Parameters.observations] using absent drive output (List.mem_toFinset.mpr accepted) K eligible

end Controller.NativeProof.Wrapper
