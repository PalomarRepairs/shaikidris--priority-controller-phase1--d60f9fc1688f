module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSelector
public import Controller.Extensions.SupportCandidate

@[expose] public section

/-! The output loop reuses one header slot for the current root identifier.
Changing that word leaves the healthy table and original root occurrences
intact, and does not change the selector callback's resident instructions. -/
namespace Controller.Extensions.ResolvedRootSource
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored

variable {width n m root : Nat} {rows : List Row} {roots : List Nat}

def packet (width n : Nat) (rows : List Row) (roots : List Nat)
    (healthy : Fin m → Bool) (root : Nat) : Array (Word width) :=
  (SupportCandidate.header width n rows roots healthy).set 4 (word width root) (by simp; omega)

@[simp] theorem packet_size (healthy : Fin m → Bool) :
    (packet width n rows roots healthy root).size = 5+m := by simp [packet]

theorem cache_set (header : Array (Word width)) (rows : List Row) (roots : List Nat)
    (slot : Nat) (valid : slot<header.size) (value : Word width) :
    (cacheHeap width header rows roots).set slot value (by simp; omega) =
      cacheHeap width (header.set slot value valid) rows roots := by
  simp only [cacheHeap,Controller.Cost.ForestCursorMaterialize.allocatedHeap,Array.size_set]
  rw [Array.set_append_left valid]

theorem update (healthy : Fin m → Bool) (before root : Nat) :
    (cacheHeap width (packet width n rows roots healthy before) rows roots).set 4 (word width root) (by simp; omega) =
      cacheHeap width (packet width n rows roots healthy root) rows roots := by
  rw [cache_set _ _ _ 4 (by simp; omega)]
  simp [packet,Array.set_set]

theorem root_cell (healthy : Fin m → Bool) (root : Nat) :
    (cacheHeap width (packet width n rows roots healthy root) rows roots)[4]? = some (word width root) := by
  unfold cacheHeap Controller.Cost.ForestCursorMaterialize.allocatedHeap
  rw [Array.getElem?_append_left (by simp; omega)]
  simp [packet]

theorem healthy_cell (healthy : Fin m → Bool) (root : Nat) (node : Fin m) :
    (cacheHeap width (packet width n rows roots healthy root) rows roots)[5+node.val]? =
      some (boolWord width (healthy node)) := by
  have headerCell := SupportCandidate.header_value (width := width) (n := n) (rows := rows) roots healthy node
  unfold cacheHeap Controller.Cost.ForestCursorMaterialize.allocatedHeap
  rw [Array.getElem?_append_left (by simpa using (show node.val < m from node.isLt))]
  simp only [packet,Array.getElem?_set,ite_eq_right (by omega : 4≠5+node.val)]
  exact headerCell

theorem plan_uniform (graph : DAG n) (left right : Array (Word width)) (rows : List Row) (roots : List Nat)
    (sameSize : left.size = right.size) (b : Nat) (target : Channel n) (rootSlot : Nat) :
    ResolvedSourcePlan.query width graph left rows roots b target rootSlot =
      ResolvedSourcePlan.query width graph right rows roots b target rootSlot := by
  simp only [ResolvedSourcePlan.query,ResolvedSourcePlan.forwards]
  congr 2
  apply List.flatMap_congr
  intro node member
  simp only [ResolvedSourcePlan.node,ResolvedSourcePlan.childBase,cacheHeap_size,sameSize]

theorem callback_uniform (graph : DAG n) (left right : Array (Word width)) (rows : List Row) (roots : List Nat)
    (sameSize : left.size = right.size) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
    (rootSlot entry sourceCount found rejected : Nat) :
    ResolvedSourceCallback.code width graph left rows roots b target reference rootSlot entry sourceCount found rejected =
      ResolvedSourceCallback.code width graph right rows roots b target reference rootSlot entry sourceCount found rejected := by
  have plan := plan_uniform graph left right rows roots sameSize b target rootSlot
  simp only [ResolvedSourceCallback.code,ResolvedSourceCallback.positions,ResolvedSourceCallback.emitCode,plan]

def source (width n : Nat) (rows : List Row) (roots : List Nat)
    (healthy : Fin m → Bool) (root : Nat) : Array (Word width) :=
  cacheHeap width (packet width n rows roots healthy root) rows roots

theorem source_size_uniform (healthy : Fin m → Bool) (root : Nat) :
    (source width n rows roots healthy root).size = (source width n rows roots healthy 0).size := by
  simp [source]

theorem source_mask_update (healthy : Fin m → Bool) (before root : Nat) (ands : Nat) :
    (SupportSearch.maskHeap (source width n rows roots healthy before) (∅ : Finset (Fin ands))).set 4 (word width root)
      (by simp [source]; omega) =
      SupportSearch.maskHeap (source width n rows roots healthy root) (∅ : Finset (Fin ands)) := by
  unfold SupportSearch.maskHeap withValues
  rw [Array.set_append_left (by simp [source]; omega)]
  unfold source
  rw [update]

theorem retained_cell (healthy : Fin m → Bool) (root address : Nat) (value : Word width)
    (stored : (SupportCandidate.header width n rows roots healthy)[address]? = some value)
    (separate : address ≠ 4) :
    (source width n rows roots healthy root)[address]? = some value := by
  have bound := (Array.getElem?_eq_some_iff.mp stored).1
  unfold source cacheHeap Controller.Cost.ForestCursorMaterialize.allocatedHeap
  rw [Array.getElem?_append_left (by simpa only [packet,Array.size_set] using bound)]
  simp only [packet,Array.getElem?_set,ite_eq_right (Ne.symm separate)]
  exact stored

theorem channel_cell (healthy : Fin m → Bool) (root : Nat) :
    (source width n rows roots healthy root)[0]? = some (word width n) := by
  apply retained_cell healthy root 0 _ _ (by decide)
  simp [SupportCandidate.header,UniformDAGRun.packetHeaderHeap,globalHeader]

theorem node_cell (graph : DAG n) (healthy : Fin graph.nodeCount → Bool) (root : Nat)
    (matched : RowsMatch graph rows) :
    (source width n rows roots healthy root)[1]? = some (word width graph.nodeCount) := by
  exact retained_cell healthy root 1 _ (SupportCandidate.header_count graph rows roots healthy matched) (by decide)

theorem root_occurrence (healthy : Fin m → Bool) (root i : Nat) (valid : i<roots.length) :
    (source width n rows roots healthy root)[UniformDAGRuntimeOutputs.rootBase
      (packet width n rows roots healthy 0) rows+i]? = some (word width roots[i]) := by
  have cell := UniformDAGRuntimeOutputs.cache_root_cell (packet width n rows roots healthy root) rows roots i valid
  have same : UniformDAGRuntimeOutputs.rootBase (packet width n rows roots healthy root) rows =
      UniformDAGRuntimeOutputs.rootBase (packet width n rows roots healthy 0) rows := by
    simp [UniformDAGRuntimeOutputs.rootBase]
  have optional : (cacheHeap width (packet width n rows roots healthy root) rows roots)[
      UniformDAGRuntimeOutputs.rootBase (packet width n rows roots healthy root) rows+i]? =
      some (word width roots[i]) := by
    rw [Array.getElem?_eq_getElem (by simp [UniformDAGRuntimeOutputs.rootBase]; omega)]
    exact congrArg some cell
  simpa only [source,same] using optional

theorem source_bound (graph : DAG n) (healthy : Fin graph.nodeCount → Bool) (root : Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (source width n rows roots healthy root).size+graph.liveAndCount ≤ 40*(graph.countedSize+1) := by
  have size := graph.countedSize_eq
  have ands := graph.liveAndCount_le_nodeCount
  obtain ⟨children,guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  simp only [source,cacheHeap_size,packet_size,matched.length_eq,children,guards,rootLength]
  omega

end Controller.Extensions.ResolvedRootSource
