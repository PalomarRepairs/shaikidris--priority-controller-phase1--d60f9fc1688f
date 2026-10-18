module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourceCallback
public import Controller.Extensions.SupportSearchRun

@[expose] public section

/-! Positional selector masks enumerate the distinct stored AND identities.
The fetched traversal therefore has one binary position per AND, even when
an AND is shared by several parents or has the same child twice. -/
namespace Controller.Extensions.ResolvedSelector
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Extensions.BoundedAnd
open Controller.Cost Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored

def identity (graph : DAG n) (position : Fin graph.liveAndCount) : Fin graph.nodeCount :=
  (andIdentities graph)[position.val]'(by rw [andIdentities_length]; exact position.isLt)

theorem identity_injective (graph : DAG n) : Function.Injective (identity graph) := by
  intro left right same
  have nodup : (andIdentities graph).Nodup := (List.nodup_finRange _).filter _
  apply Fin.ext
  exact nodup.getElem_inj_iff.mp same

def selection (graph : DAG n) (chosen : Finset (Fin graph.liveAndCount)) : Finset (Fin graph.nodeCount) :=
  chosen.image (identity graph)

theorem selectorValues_selection (graph : DAG n) (chosen : Finset (Fin graph.liveAndCount)) :
    ResolvedSourcePlan.selectorValues graph (selection graph chosen) = assignmentOfSet chosen := by
  funext position
  change decide (identity graph position ∈ chosen.image (identity graph)) = decide (position ∈ chosen)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Finset.mem_image]
  constructor
  · rintro ⟨other, member, equal⟩
    exact (identity_injective graph equal) ▸ member
  · intro member; exact ⟨position, member, rfl⟩

theorem identities_map (graph : DAG n) : (List.finRange graph.liveAndCount).map (identity graph) = andIdentities graph := by
  apply List.ext_getElem
  · simp [andIdentities_length]
  · intro i left right
    simp only [List.getElem_map, List.getElem_finRange, identity]
    rfl

theorem search_map (f : α → β) (query : List β → Option γ) (capacity : Nat) (items chosen : List α) :
    SupportStream.search query capacity (items.map f) (chosen.map f) =
      SupportStream.search (fun values => query (values.map f)) capacity items chosen := by
  induction items generalizing capacity chosen with
  | nil => cases capacity <;> rfl
  | cons head tail ih =>
    cases capacity with
    | zero => rfl
    | succ capacity =>
      simp only [List.map_cons, SupportStream.search]
      rw [show SupportStream.search query capacity (List.map f tail) (f head :: List.map f chosen) =
        SupportStream.search (fun values => query (values.map f)) capacity tail (head::chosen) from
          by simpa only [List.map_cons] using ih capacity (head::chosen)]
      split
      · rfl
      · rw [ih]

def query (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount)
    (chosen : Finset (Fin graph.liveAndCount)) : Option (Finset (Channel n)) :=
  resolvedZeroQuery graph b target root (selection graph chosen)

theorem search_eq (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) :
    (SupportStream.search (fun chosen => query graph b target root chosen.toFinset)
      graph.liveAndCount (List.finRange graph.liveAndCount) []).result =
        SupportStream.scanExpansions graph b target root := by
  have mapped := search_map (identity graph)
    (fun chosen => resolvedZeroQuery graph b target root chosen.toFinset) graph.liveAndCount
    (List.finRange graph.liveAndCount) []
  have image : ∀ chosen : List (Fin graph.liveAndCount),
      (chosen.map (identity graph)).toFinset = chosen.toFinset.image (identity graph) := by
    intro chosen
    ext node
    simp
  simpa only [identities_map, List.map_nil, image, query, selection, SupportStream.scanExpansions] using
    (congrArg SupportStream.Run.result mapped).symm

theorem query_isSome (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount)
    (chosen : Finset (Fin graph.liveAndCount)) :
    (query graph b target root chosen).isSome = true ↔
      ∃ K, Admissible b target K ∧ (resolved graph (selection graph chosen)).eval (assignmentOfSet K) root = false := by
  have none := (resolved graph (selection graph chosen)).solveZero_none_iff
    (resolved_guarded graph _) b target root ∅ ∅
  simp only [query, resolvedZeroQuery]
  rw [← Option.ne_none_iff_isSome]
  simpa [ExtendsFixed] using not_congr none

theorem contract (program : Program width 8) (packet : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (b : Nat)
    (target : Channel n) (reference root : Fin graph.nodeCount) (rootSlot entry call found : Nat)
    (rootStored : (cacheHeap width packet rows roots)[rootSlot]? = some (word width root.val))
    (channelStored : (cacheHeap width packet rows roots)[0]? = some (word width n))
    (nodeStored : (cacheHeap width packet rows roots)[1]? = some (word width graph.nodeCount))
    (sourceBound : (cacheHeap width packet rows roots).size+graph.liveAndCount ≤ 40*(graph.countedSize+1))
    (callBound : call ≤ 128*(graph.countedSize+1)) (capacity : 4096*(graph.countedSize+1)<2^width)
    (present : SharedRootRead.BlockAt program call
      (ResolvedSourceCallback.code width graph packet rows roots b target reference rootSlot call
        ((cacheHeap width packet rows roots).size+graph.liveAndCount) found (SupportTraversal.backtrack entry))) :
    SupportSearch.Callback program (cacheHeap width packet rows roots) (query graph b target root)
      entry call found (7000*(graph.countedSize+1)) (300*(graph.countedSize+1)) := by
  intro chosen state heap pc running
  have storedHeap : state.heap = withValues (cacheHeap width packet rows roots)
      (ResolvedSourcePlan.selectorValues graph (selection graph chosen)) := by
    rw [selectorValues_selection]
    exact heap
  have prefixCell : ∀ (address : Nat) (value : Word width),
      (cacheHeap width packet rows roots)[address]? = some value → state.heap[address]? = some value := by
    intro address value cell
    rw [heap]
    unfold SupportSearch.maskHeap withValues
    rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp cell).1]
    exact cell
  have heapSize : state.heap.size = (cacheHeap width packet rows roots).size+graph.liveAndCount := by simp only [heap, SupportSearch.maskHeap_size]
  obtain ⟨answer, final, ticks, peak, trace, time, space, fh, fs, fo, fp, fr, meaning⟩ :=
    ResolvedSourceCallback.execution program state packet graph rows roots matched (selection graph chosen) b target
      reference root rootSlot call found (SupportTraversal.backtrack entry) storedHeap
      (prefixCell _ _ rootStored) (prefixCell _ _ channelStored) (prefixCell _ _ nodeStored)
      (by have bound := (Array.getElem?_eq_some_iff.mp channelStored).1; rw [heapSize]; omega)
      pc running callBound (by simpa only [heapSize] using sourceBound) capacity
      (by simpa only [heapSize] using present)
  have decision : answer = (query graph b target root chosen).isSome := by
    apply Bool.eq_iff_iff.mpr
    exact meaning.trans (query_isSome graph b target root chosen).symm
  exact ⟨final, ticks, peak, trace, time, space, fh, fs, fo, fr, by simpa only [decision] using fp⟩

theorem search (program : Program width 8) (packet : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (b k : Nat)
    (target : Channel n) (reference root : Fin graph.nodeCount) (rootSlot entry call found : Nat)
    (rootStored : (cacheHeap width packet rows roots)[rootSlot]? = some (word width root.val))
    (channelStored : (cacheHeap width packet rows roots)[0]? = some (word width n))
    (nodeStored : (cacheHeap width packet rows roots)[1]? = some (word width graph.nodeCount))
    (sourceBound : (cacheHeap width packet rows roots).size+graph.liveAndCount ≤ 40*(graph.countedSize+1))
    (callBound : call ≤ 128*(graph.countedSize+1)) (capacity : 4096*(graph.countedSize+1)<2^width)
    (andBound : graph.liveAndCount ≤ k) (coreRoom : entry+36 < 2^width)
    (callbackAt : SharedRootRead.BlockAt program call
      (ResolvedSourceCallback.code width graph packet rows roots b target reference rootSlot call
        ((cacheHeap width packet rows roots).size+graph.liveAndCount) found (SupportTraversal.backtrack entry)))
    (coreAt : SharedRootRead.BlockAt program entry (SupportTraversal.code width entry graph.liveAndCount
      (cacheHeap width packet rows roots).size call)) (rest output : List (Word width)) :
    ∃ final ticks peak, Execution program
      (SupportSearchRun.initial graph.liveAndCount graph.liveAndCount entry (cacheHeap width packet rows roots) rest output)
      final ticks peak ∧ ticks ≤ (7000*(graph.countedSize+1)+50)*2^k+6 ∧
      peak ≤ (cacheHeap width packet rows roots).size+3*graph.liveAndCount+
        300*(graph.countedSize+1)+rest.length+output.length+11 ∧
      final.output = output ∧ SupportSearchRun.Outcome (cacheHeap width packet rows roots) (query graph b target root)
        found rest final (SupportStream.scanExpansions graph b target root) := by
  have callback := contract program packet graph rows roots matched b target reference root rootSlot entry call found
    rootStored channelStored nodeStored sourceBound callBound capacity callbackAt
  have size := graph.countedSize_eq
  have ands := graph.liveAndCount_le_nodeCount
  obtain ⟨final, ticks, peak, trace, time, space, out, result⟩ :=
    SupportSearchRun.from_mask program _ (query graph b target root) entry call found
      (7000*(graph.countedSize+1)) (300*(graph.countedSize+1)) graph.liveAndCount callback coreAt coreRoom
      (by omega) (by omega) rest output
  have bound := SupportSearchRun.selector_bound graph.liveAndCount k (7000*(graph.countedSize+1)) andBound
  rw [search_eq] at result
  exact ⟨final, ticks, peak, trace, time.trans bound, space, out, result⟩

theorem returning_search (program : Program width 8) (packet : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (b k : Nat)
    (target : Channel n) (reference root : Fin graph.nodeCount) (rootSlot entry call found : Nat)
    (ending : Instruction width 8)
    (rootStored : (cacheHeap width packet rows roots)[rootSlot]? = some (word width root.val))
    (channelStored : (cacheHeap width packet rows roots)[0]? = some (word width n))
    (nodeStored : (cacheHeap width packet rows roots)[1]? = some (word width graph.nodeCount))
    (sourceBound : (cacheHeap width packet rows roots).size+graph.liveAndCount ≤ 40*(graph.countedSize+1))
    (callBound : call ≤ 128*(graph.countedSize+1)) (capacity : 4096*(graph.countedSize+1)<2^width)
    (andBound : graph.liveAndCount ≤ k) (coreRoom : entry+36 < 2^width)
    (callbackAt : SharedRootRead.BlockAt program call
      (ResolvedSourceCallback.code width graph packet rows roots b target reference rootSlot call
        ((cacheHeap width packet rows roots).size+graph.liveAndCount) found (SupportTraversal.backtrack entry)))
    (coreAt : SharedRootRead.BlockAt program entry (SupportTraversal.endingCode width entry graph.liveAndCount
      (cacheHeap width packet rows roots).size call ending)) (rest output : List (Word width)) :
    ∃ final ticks peak, Execution program
      (SupportSearchRun.initial graph.liveAndCount graph.liveAndCount entry (cacheHeap width packet rows roots) rest output)
      final ticks peak ∧ ticks ≤ (7000*(graph.countedSize+1)+50)*2^k+5 ∧
      peak ≤ (cacheHeap width packet rows roots).size+3*graph.liveAndCount+
        300*(graph.countedSize+1)+rest.length+output.length+11 ∧
      final.output = output ∧ SupportSearchRun.ReturnedOutcome (cacheHeap width packet rows roots) (query graph b target root)
        entry found rest final (SupportStream.scanExpansions graph b target root) := by
  have callback := contract program packet graph rows roots matched b target reference root rootSlot entry call found
    rootStored channelStored nodeStored sourceBound callBound capacity callbackAt
  have size := graph.countedSize_eq
  have ands := graph.liveAndCount_le_nodeCount
  obtain ⟨final, ticks, peak, trace, time, space, out, result⟩ :=
    SupportSearchRun.returning_from_mask program _ (query graph b target root) entry call found
      (7000*(graph.countedSize+1)) (300*(graph.countedSize+1)) graph.liveAndCount ending callback coreAt coreRoom
      (by omega) (by omega) rest output
  have powers : 2^graph.liveAndCount ≤ 2^k := Nat.pow_le_pow_right (by decide) andBound
  rw [SupportStream.leaves_saturated _ _ le_rfl] at time
  rw [search_eq] at result
  exact ⟨final, ticks, peak, trace,
    time.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ powers) 5), space, out, result⟩

end Controller.Extensions.ResolvedSelector
