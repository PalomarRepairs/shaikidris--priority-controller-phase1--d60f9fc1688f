module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorMaterialize
public import Controller.Cost.ForestCursorRootStore

@[expose] public section

/-!
# Shared descriptors for all declared roots

The source scan uses one allocation counter and chronological descriptor store
across declared root occurrences. The decoder below is a proof witness; it is
absent from the runtime builder. Physical materialization allocates this final
store once. Counter initialization and the traversal caller are separate from
this descriptor refinement.
-/
namespace Controller.Cost.ForestCursorAllRoots

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestCursorMaterialize Controller.Cost.ForestCursorRoot
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.GateProgram Controller.Cost.ForestMarkerMachine Controller.Cost.ForestGuardSchedule
open Controller.Cost.ForestCursorCapturedProgram Controller.Cost.ForestCursorDescriptorSource

/-- Extend only newly allocated pointers; root navigation starts at sentinel zero. -/
def rootDecoder (graph : DAG n) (state : Builder) (route : ℕ → LeafRoute)
    (position : Fin graph.roots.length) : ℕ → LeafRoute :=
  routeScan position.val (beginRoot state) route
    (cursorOps graph (graph.roots.get position) [])

def rootsDecoder (graph : DAG n) (state : Builder) (route : ℕ → LeafRoute) :
    List (Fin graph.roots.length) → ℕ → LeafRoute
  | [] => route
  | position :: rest => rootsDecoder graph (scanRoot graph state position)
      (rootDecoder graph state route position) rest

theorem rootDecoder_decodes (graph : DAG n) (state : Builder) (valid : Valid state)
    (route : ℕ → LeafRoute) (decoded : Decodes state route)
    (position : Fin graph.roots.length) :
    Decodes (scanRoot graph state position) (rootDecoder graph state route position) := by
  exact scan_decodes position.val (beginRoot state) (beginRoot_valid state valid)
    route ⟨decoded.sentinel, decoded.entries⟩ _

theorem scanRoots_dense (graph : DAG n) (state : Builder) (dense : Dense state)
    (positions : List (Fin graph.roots.length)) : Dense (scanRoots graph state positions) := by
  induction positions generalizing state with
  | nil => exact dense
  | cons position rest ih => exact ih _ (scanRoot_dense graph state dense position)

theorem rootsDecoder_decodes (graph : DAG n) (state : Builder) (valid : Valid state)
    (route : ℕ → LeafRoute) (decoded : Decodes state route)
    (positions : List (Fin graph.roots.length)) :
    Decodes (scanRoots graph state positions) (rootsDecoder graph state route positions) := by
  induction positions generalizing state route with
  | nil => exact decoded
  | cons position rest ih =>
      exact ih _ (scanRoot_valid graph state valid position) _
        (rootDecoder_decodes graph state valid route decoded position)

theorem rootsDecoder_preserves (graph : DAG n) (state : Builder)
    (route : ℕ → LeafRoute) (positions : List (Fin graph.roots.length))
    (pointer : ℕ) (bounded : pointer ≤ state.count) :
    rootsDecoder graph state route positions pointer = route pointer := by
  induction positions generalizing state route with
  | nil => rfl
  | cons position rest ih =>
      have nextBound : pointer ≤ (scanRoot graph state position).count := by
        have count := source_root_count graph position state
        change (scanRoot graph state position).count = _ at count
        omega
      rw [rootsDecoder, ih _ _ nextBound]
      exact routeScan_preserves position.val (beginRoot state) route _ pointer bounded

def allDecoder (graph : DAG n) : ℕ → LeafRoute :=
  rootsDecoder graph initial (fun _ => []) (List.finRange graph.roots.length)

theorem buildRoots_dense (graph : DAG n) : Dense (buildRoots graph) :=
  scanRoots_dense graph initial initial_dense _

theorem allDecoder_decodes (graph : DAG n) : Decodes (buildRoots graph) (allDecoder graph) := by
  apply rootsDecoder_decodes graph initial initial_valid
  exact ⟨rfl, by simp [initial]⟩

/-- One final shared store, with physical fields derived from all source scans.
The declared root identifier is retained separately by the traversal caller. -/
def allRepresented (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width) :
    RouteDescriptors width (descriptorHeap width heap (buildRoots graph)) :=
  represented width heap (buildRoots graph) (buildRoots_valid graph)
    (buildRoots_dense graph) (allDecoder graph) (allDecoder_decodes graph)
    countFits positionFits

@[simp] theorem allRepresented_route (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width) :
    (allRepresented width heap graph countFits positionFits).route = allDecoder graph := rfl

/-- Descriptor fields precede one global zero counter/selector/root-ID region. -/
def setupValues (graph : DAG n) : List ℕ :=
  fields (buildRoots graph).entries.reverse ++ List.replicate (n + 3) 0

def setupHeap (width : ℕ) (heap : Array (Word width)) (graph : DAG n) : Array (Word width) :=
  allocatedHeap width heap (setupValues graph)

def setupCode (width : ℕ) (graph : DAG n) : ForestCounter.Code width :=
  writeCode width (setupValues graph)

@[simp] theorem setupValues_length (graph : DAG n) :
    (setupValues graph).length = 2 * (buildRoots graph).count + (n + 3) := by
  simp only [setupValues, List.length_append, fields_length, List.length_reverse,
    (buildRoots_valid graph).count, List.length_replicate]

@[simp] theorem setupHeap_size (width : ℕ) (heap : Array (Word width)) (graph : DAG n) :
    (setupHeap width heap graph).size = heap.size + 2 * (buildRoots graph).count + (n + 3) := by
  simp only [setupHeap, allocatedHeap_size, setupValues_length, Nat.add_assoc]

/-- One fetched setup execution for the final shared descriptors and all counters.
This does not allocate a descriptor agreement again for each output. -/
theorem setup_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (base : ℕ) (address loaded temporary : Word width)
    (fits : base + (4 * (buildRoots graph).count + 2 * (n + 3)) < 2 ^ width)
    (room : heap.size + 2 * (buildRoots graph).count + (n + 3) ≤ 2 ^ width)
    (block : BlockAt program base (setupCode width graph)) :
    ∃ finalTemporary : Word width,
      Execution program (counterState heap base address loaded temporary)
        (counterState (setupHeap width heap graph)
          (base + (4 * (buildRoots graph).count + 2 * (n + 3))) address loaded finalTemporary)
        (4 * (buildRoots graph).count + 2 * (n + 3))
        (5 + heap.size + 2 * (buildRoots graph).count + (n + 3)) := by
  have twice : 2 * (setupValues graph).length =
      4 * (buildRoots graph).count + 2 * (n + 3) := by
    rw [setupValues_length]; omega
  have run := write_execution program heap base (setupValues graph) address loaded temporary
    (by rw [twice]; exact fits)
    (by rw [setupValues_length]; omega) block
  rw [twice] at run
  simpa only [setupHeap, setupValues_length, Nat.add_assoc] using run

/-- All previously stored graph cells survive the once-per-run setup. -/
theorem setup_prefix (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (address : ℕ) (valid : address < heap.size) :
    (setupHeap width heap graph)[address]? = heap[address]? :=
  allocatedHeap_prefix width heap (setupValues graph) address valid

/-- Finite allocation extends a heap without changing any pre-existing word. -/
theorem prefix_read (old current : Array (Word width))
    (size : old.size ≤ current.size)
    (agreement : ∀ address, address < old.size → current[address]? = old[address]?)
    (address : ℕ) (valid : address < old.size) :
    current[address]'(Nat.lt_of_lt_of_le valid size) = old[address]'valid := by
  calc
    _ = storedWord current address :=
      (storedWord_eq current address (Nat.lt_of_lt_of_le valid size)).symm
    _ = storedWord old address := by unfold storedWord; rw [agreement address valid]
    _ = _ := storedWord_eq old address valid

/-- Physical record interpretation survives finite agreement-preserving allocation.
This bridge does not require equal heap sizes, unlike a mutable-cell frame. -/
def extendGraphRecords (graph : DAG n) (old current : Array (Word width))
    (records : GraphRecords width old graph) (size : old.size ≤ current.size)
    (agreement : ∀ address, address < old.size → current[address]? = old[address]?) :
    GraphRecords width current graph where
  recordBase := records.recordBase
  childBase := records.childBase
  guardBase := records.guardBase
  tagValid := fun node => Nat.lt_of_lt_of_le (records.tagValid node) size
  tagWord := fun node => (prefix_read old current size agreement _ (records.tagValid node)).trans
    (records.tagWord node)
  headValid := fun node => Nat.lt_of_lt_of_le (records.headValid node) size
  headWord := fun node head equal =>
    (prefix_read old current size agreement _ (records.headValid node)).trans (records.headWord node head equal)
  childValid := fun node position => Nat.lt_of_lt_of_le (records.childValid node position) size
  childWord := fun node position =>
    (prefix_read old current size agreement _ (records.childValid node position)).trans (records.childWord node position)
  guardValid := fun node position => Nat.lt_of_lt_of_le (records.guardValid node position) size
  guardWord := fun node position =>
    (prefix_read old current size agreement _ (records.guardValid node position)).trans (records.guardWord node position)

def extendRouteDescriptors (old current : Array (Word width))
    (routes : RouteDescriptors width old) (size : old.size ≤ current.size)
    (agreement : ∀ address, address < old.size → current[address]? = old[address]?) :
    RouteDescriptors width current where
  base := routes.base
  count := routes.count
  route := routes.route
  sentinel := routes.sentinel
  parentValid := fun pointer bound => Nat.lt_of_lt_of_le (routes.parentValid pointer bound) size
  positionValid := fun pointer bound => Nat.lt_of_lt_of_le (routes.positionValid pointer bound) size
  parentEarlier := by
    intro pointer bound
    rw [prefix_read old current size agreement _ (routes.parentValid pointer bound)]
    exact routes.parentEarlier pointer bound
  cellRoute := by
    intro pointer bound
    rw [prefix_read old current size agreement _ (routes.positionValid pointer bound),
      prefix_read old current size agreement _ (routes.parentValid pointer bound)]
    exact routes.cellRoute pointer bound

def setupOffset (heap : Array (Word width)) (graph : DAG n) : ℕ :=
  heap.size + 2 * (buildRoots graph).count

def setupLayout (heap : Array (Word width)) (graph : DAG n) : SelectorLayout n where
  counterOffset := setupOffset heap graph
  found := setupOffset heap graph + n
  best := setupOffset heap graph + n + 1
  distinct := by omega
  foundOutside := Or.inr (by omega)
  bestOutside := Or.inr (by omega)

/-- The single initialization block stores zero at every counter and metadata cell. -/
theorem setup_zero (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (index : ℕ) (bound : index < n + 3) :
    (setupHeap width heap graph)[setupOffset heap graph + index]'
      (by rw [setupHeap_size]; unfold setupOffset; omega) = word width 0 := by
  have fieldLength : (fields (buildRoots graph).entries.reverse).length =
      2 * (buildRoots graph).count := by
    simp only [fields_length, List.length_reverse, (buildRoots_valid graph).count]
  have value : (setupValues graph)[2 * (buildRoots graph).count + index]'
      (by rw [setupValues_length]; omega) = 0 := by
    unfold setupValues
    rw [List.getElem_append_right (by rw [fieldLength]; omega)]
    simp only [fieldLength, Nat.add_sub_cancel_left, List.getElem_replicate]
  have actual := allocatedHeap_cell width heap (setupValues graph)
    (2 * (buildRoots graph).count + index) (by rw [setupValues_length]; omega)
  simpa only [setupHeap, setupOffset, Nat.add_assoc, value] using actual

theorem setup_counters (width : ℕ) (heap : Array (Word width)) (graph : DAG n) :
    CountersStored (setupHeap width heap graph) (setupOffset heap graph) (fun _ : Channel n => 0) := by
  refine ⟨?_, ?_⟩
  · intro channel
    rw [setupHeap_size]; unfold setupOffset
    have bound := channel.isLt
    omega
  · intro channel
    exact setup_zero width heap graph channel.val (by have bound := channel.isLt; omega)

theorem setup_selector (width : ℕ) (heap : Array (Word width)) (graph : DAG n) :
    SelectorStored (setupHeap width heap graph) (setupLayout heap graph) none := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [setupLayout, setupHeap_size, setupOffset]; omega
  · simp only [setupLayout, setupHeap_size, setupOffset]; omega
  · exact setup_zero width heap graph n (by omega)
  · intro pointer impossible; cases impossible

theorem scanRoots_count_ge (graph : DAG n) (state : Builder)
    (positions : List (Fin graph.roots.length)) : state.count ≤ (scanRoots graph state positions).count := by
  induction positions generalizing state with
  | nil => exact Nat.le_refl _
  | cons position rest ih =>
      have count := source_root_count graph position state
      change (scanRoot graph state position).count = _ at count
      have later := ih (scanRoot graph state position)
      change state.count ≤ (scanRoots graph (scanRoot graph state position) rest).count
      omega

/-- Captured leaf IDs of an earlier root remain valid in the final shared store.
The final decoder is calculated from actual later scans, not a supplied leaf map. -/
theorem tail_root_index (graph : DAG n) (position : Fin graph.roots.length)
    (state : Builder) (valid : Valid state) (decode : ℕ → LeafRoute) (sentinel : decode 0 = [])
    (rest : List (Fin graph.roots.length)) (routes : RouteDescriptors width heap)
    (count : routes.count = (scanRoots graph (scanRoot graph state position) rest).count)
    (represented : routes.route = rootsDecoder graph (scanRoot graph state position)
      (rootDecoder graph state decode position) rest)
    (fits : routes.count < 2 ^ width) :
    RootIndex graph (graph.roots.get position) routes
      (pairIndex graph (capturePairs position.val (beginRoot state)
        (cursorOps graph (graph.roots.get position) []))) := by
  intro owner route head present
  obtain ⟨pointer, member⟩ := capturePairs_callback position.val (beginRoot state) _ owner route head present
  have safe := source_route_safe graph position.val (graph.roots.get position) []
    (beginRoot state) (beginRoot_valid state valid) decode sentinel
  obtain ⟨decoded, bounded⟩ := capturePairs_decoded position.val (beginRoot state)
    (beginRoot_valid state valid) decode _ safe route pointer member
  have pointerEq := pairIndex_matches graph _ (source_capturePairs_unique graph position state)
    (source_capturePairs_empty graph position state) route pointer member
  have localBound : pointer ≤ (scanRoot graph state position).count := bounded
  have globalBound : pointer ≤ routes.count := by
    rw [count]
    exact Nat.le_trans localBound (scanRoots_count_ge graph _ rest)
  rw [pointerEq]
  refine ⟨?_, globalBound, Nat.lt_of_le_of_lt globalBound fits⟩
  rw [represented, rootsDecoder_preserves graph _ _ rest pointer localBound]
  exact decoded

end Controller.Cost.ForestCursorAllRoots
