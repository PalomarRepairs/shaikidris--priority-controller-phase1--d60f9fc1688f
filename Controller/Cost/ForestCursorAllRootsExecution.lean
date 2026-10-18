module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorAllRoots

@[expose] public section

/-!
# Declared-root provenance and complete cursor execution

Each caller block conditionally stores its declared root position before the
complete source traversal. The selector keeps the first feasible leaf, so later
roots preserve both its pointer and its originating root. Parent descriptors
and zero counters are allocated once by the all-root setup. The execution
contracts retain the finite physical representations and source-derived leaf
indices at each root boundary.
-/
namespace Controller.Cost.ForestCursorAllRootsExecution

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorExecution
open Controller.Cost.ForestCursorRoot Controller.Cost.ForestGuardSchedule
open Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorMaterialize
open Controller.Cost.ForestCursorCapturedProgram

/-- Root occurrence identity is independent of its possibly empty route. -/
def provenanceCell (heap : Array (Word width)) (graph : DAG n) : ℕ :=
  setupOffset heap graph + n + 2

theorem provenance_separate (heap : Array (Word width)) (graph : DAG n) :
    ForestCursorRootStore.RootCellLayout (setupLayout heap graph) (provenanceCell heap graph) := by
  refine ⟨Or.inr ?_, ?_, ?_⟩ <;>
    simp only [setupLayout, provenanceCell] <;> omega

/-- These root IDs remain distinguishable even when both route pointers are zero. -/
theorem root_identity_distinct (graph : DAG n) (first second : Fin graph.roots.length)
    (different : first ≠ second) : first.val ≠ second.val := by
  intro equal
  exact different (Fin.ext equal)

def setupRuntime (width : ℕ) (heap : Array (Word width)) (graph : DAG n) : RuntimeModel width n :=
  ⟨setupHeap width heap graph, fun _ => 0, none, []⟩

theorem setup_runtimeStored (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width (setupHeap width heap graph) graph)
    (routes : RouteDescriptors width (setupHeap width heap graph)) :
    RuntimeStored graph records routes (setupLayout heap graph) (setupRuntime width heap graph) := by
  exact ⟨setup_counters width heap graph, setup_selector width heap graph,
    ⟨rfl, fun _ _ => rfl⟩⟩

/-- Setup preserves the physically allocated descriptor prefix while adding zeros. -/
theorem setupHeap_split (width : ℕ) (heap : Array (Word width)) (graph : DAG n) :
    setupHeap width heap graph = allocatedHeap width
      (descriptorHeap width heap (buildRoots graph)) (List.replicate (n + 3) 0) := by
  apply Array.toList_inj.mp
  simp [setupHeap, descriptorHeap, allocatedHeap, setupValues, List.map_append, List.append_assoc]

def setupRecords (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph) : GraphRecords width (setupHeap width heap graph) graph :=
  extendGraphRecords graph heap (setupHeap width heap graph) records
    (by rw [setupHeap_size]; omega) (setup_prefix width heap graph)

def setupRoutes (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width) :
    RouteDescriptors width (setupHeap width heap graph) :=
  extendRouteDescriptors (descriptorHeap width heap (buildRoots graph)) (setupHeap width heap graph)
    (allRepresented width heap graph countFits positionFits)
    (by rw [descriptorHeap_size _ _ _ (buildRoots_valid graph), setupHeap_size]; omega)
    (by intro address bound; rw [setupHeap_split]; exact allocatedHeap_prefix width _ _ address bound)

theorem setup_persistent_before (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (address : ℕ)
    (present : PersistentCell graph (setupRecords width heap graph records)
      (setupRoutes width heap graph countFits positionFits) address) :
    address < setupOffset heap graph := by
  rcases present with source | child | guard | descriptor
  · obtain ⟨node, tag | head⟩ := source
    · subst address; have bound := records.tagValid node
      change records.recordBase + 2 * node.val < heap.size + 2 * (buildRoots graph).count
      omega
    · subst address; have bound := records.headValid node
      change records.recordBase + 2 * node.val + 1 < heap.size + 2 * (buildRoots graph).count
      omega
  · obtain ⟨node, position, equal⟩ := child
    subst address; have bound := records.childValid node position
    change records.childBase node + position.val < heap.size + 2 * (buildRoots graph).count
    omega
  · obtain ⟨node, position, equal⟩ := guard
    subst address; have bound := records.guardValid node position
    change records.guardBase node + position.val < heap.size + 2 * (buildRoots graph).count
    omega
  · obtain ⟨pointer, positive, bounded, parent | position⟩ := descriptor
    · subst address
      change heap.size + 2 * (pointer - 1) < heap.size + 2 * (buildRoots graph).count
      change pointer ≤ (buildRoots graph).count at bounded
      omega
    · subst address
      change heap.size + 2 * (pointer - 1) + 1 < heap.size + 2 * (buildRoots graph).count
      change pointer ≤ (buildRoots graph).count at bounded
      omega

theorem setup_readonly (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width) :
    ReadonlyLayout graph (setupRecords width heap graph records)
      (setupRoutes width heap graph countFits positionFits) (setupLayout heap graph) := by
  refine ⟨?_, ?_, ?_⟩
  · intro address present
    exact Or.inl (setup_persistent_before width heap graph records countFits positionFits address present)
  · intro address present
    have bound := setup_persistent_before width heap graph records countFits positionFits address present
    change setupOffset heap graph + n ≠ address
    omega
  · intro address present
    have bound := setup_persistent_before width heap graph records countFits positionFits address present
    change setupOffset heap graph + n + 1 ≠ address
    omega

theorem setup_provenance_persistent (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width) :
    ∀ address, PersistentCell graph (setupRecords width heap graph records)
      (setupRoutes width heap graph countFits positionFits) address →
      address ≠ provenanceCell heap graph := by
  intro address present
  have bound := setup_persistent_before width heap graph records countFits positionFits address present
  unfold provenanceCell
  omega

def rootPrefix (graph : DAG n) (position : Fin graph.roots.length) : List (Fin graph.roots.length) :=
  (List.finRange graph.roots.length).take position.val

def rootSuffix (graph : DAG n) (position : Fin graph.roots.length) : List (Fin graph.roots.length) :=
  (List.finRange graph.roots.length).drop (position.val + 1)

theorem root_split (graph : DAG n) (position : Fin graph.roots.length) :
    List.finRange graph.roots.length = rootPrefix graph position ++ position :: rootSuffix graph position := by
  have bound : position.val < (List.finRange graph.roots.length).length := by
    simpa only [List.length_finRange] using position.isLt
  have split := List.take_append_drop position.val (List.finRange graph.roots.length)
  rw [List.drop_eq_getElem_cons bound] at split
  have get : (List.finRange graph.roots.length)[position.val]'bound = position := by
    apply Fin.ext
    simp [List.getElem_finRange]
  rw [get] at split
  exact split.symm

theorem source_scan_append (graph : DAG n) (state : Builder)
    (first second : List (Fin graph.roots.length)) :
    scanRoots graph state (first ++ second) = scanRoots graph (scanRoots graph state first) second := by
  simp only [scanRoots, List.foldl_append]

theorem source_decoder_append (graph : DAG n) (state : Builder) (route : ℕ → LeafRoute)
    (first second : List (Fin graph.roots.length)) :
    rootsDecoder graph state route (first ++ second) =
      rootsDecoder graph (scanRoots graph state first) (rootsDecoder graph state route first) second := by
  induction first generalizing state route with
  | nil => rfl
  | cons position rest ih => exact ih _ _

def prefixBuilder (graph : DAG n) (position : Fin graph.roots.length) : Builder :=
  scanRoots graph initial (rootPrefix graph position)

def prefixDecoder (graph : DAG n) (position : Fin graph.roots.length) : ℕ → LeafRoute :=
  rootsDecoder graph initial (fun _ => []) (rootPrefix graph position)

/-- This proof index is derived from each actual allocation prefix. It is not
an input table to the runtime compiler, which emits its maintained pointer. -/
noncomputable def sourceIndices (graph : DAG n) (position : Fin graph.roots.length) : OccurrenceIndex graph :=
  pairIndex graph (capturePairs position.val (beginRoot (prefixBuilder graph position))
    (cursorOps graph (graph.roots.get position) []))

theorem source_indices (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (position : Fin graph.roots.length) :
    RootIndex graph (graph.roots.get position) (setupRoutes width heap graph countFits positionFits)
      (sourceIndices graph position) := by
  have valid : Valid (prefixBuilder graph position) :=
    scanRoots_valid graph initial initial_valid _
  have decoded : Decodes (prefixBuilder graph position) (prefixDecoder graph position) :=
    rootsDecoder_decodes graph initial initial_valid (fun _ => []) ⟨rfl, by simp [initial]⟩ _
  apply tail_root_index graph position (prefixBuilder graph position) valid
    (prefixDecoder graph position) decoded.sentinel (rootSuffix graph position)
    (setupRoutes width heap graph countFits positionFits)
  · change (buildRoots graph).count = _
    unfold buildRoots
    rw [root_split graph position, source_scan_append]
    rfl
  · change allDecoder graph = _
    unfold allDecoder
    rw [root_split graph position, source_decoder_append]
    rfl
  · exact countFits

def callerCode (graph : DAG n) (records : GraphRecords width initialHeap graph)
    (layout : SelectorLayout n) (cell : ℕ) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (base : ℕ) (position : Fin graph.roots.length) :
    ForestCounter.Code width :=
  ForestCursorRootStore.rootCode width base layout.found cell position.val ++
    ForestCursorTraversal.rootCode graph records layout index b target (base + 7) (graph.roots.get position)

def afterSetup (layout : SelectorLayout n) (cell identifier : ℕ)
    (state : RuntimeModel width n) : RuntimeModel width n :=
  { state with heap := ForestCursorRootStore.rootHeap width state.heap layout.found cell identifier }

def callerModel (graph : DAG n) (layout : SelectorLayout n) (cell : ℕ)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (position : Fin graph.roots.length) : RuntimeModel width n :=
  runModel layout index b target (afterSetup layout cell position.val state)
    (cursorOps graph (graph.roots.get position) [])

/-- The actual conditional provenance block and complete source traversal run
in one program, with restored counters and retained physical heap invariants. -/
theorem caller_execution (program : Program width 4) (graph : DAG n)
    (records : GraphRecords width initialHeap graph) (routes : RouteDescriptors width initialHeap)
    (layout : SelectorLayout n) (readonly : ReadonlyLayout graph records routes layout)
    (cell : ℕ) (separate : ForestCursorRootStore.RootCellLayout layout cell)
    (persistent : ∀ address, PersistentCell graph records routes address → address ≠ cell)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (position : Fin graph.roots.length) (state : RuntimeModel width n)
    (held : RuntimeStored graph records routes layout state)
    (capacity : ∀ channel, state.counters channel + (walkEvents graph (graph.roots.get position)).length + 1 < 2 ^ width)
    (heapFits : initialHeap.size ≤ 2 ^ width) (oneFits : 1 < 2 ^ width)
    (indexed : RootIndex graph (graph.roots.get position) routes index)
    (cellValid : cell < initialHeap.size)
    (base : ℕ) (address loaded temporary : Word width) (output : List (Word width))
    (fits : base + (callerCode graph records layout cell index b target base position).length < 2 ^ width)
    (block : BlockAt program base (callerCode graph records layout cell index b target base position)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program
        ((counterState state.heap base address loaded temporary).frame state.navigation output)
        ((counterState (callerModel graph layout cell index b target state position).heap
          (base + (callerCode graph records layout cell index b target base position).length)
          finalAddress finalLoaded finalTemporary).frame state.navigation output) ticks peak ∧
      ticks ≤ 6 + 20 * (cursorOps graph (graph.roots.get position) []).length ∧
      peak ≤ 6 + state.heap.size + state.navigation.length +
        (cursorOps graph (graph.roots.get position) []).length + output.length ∧
      RuntimeStored graph records routes layout (callerModel graph layout cell index b target state position) ∧
      (callerModel graph layout cell index b target state position).counters = state.counters := by
  have cover := block
  unfold callerCode at cover
  have setupBlock := BlockAt.prefix program base _ _ cover
  have traversalBlock := BlockAt.suffix program base _ _ cover
  have test : BlockAt program base (zeroTest width base layout.found (base + 7)) :=
    BlockAt.prefix program base _ _ setupBlock
  have store : BlockAt program (base + 4) (ForestCursorRootStore.storeCode width cell position.val) := by
    simpa only [zeroTest, List.length_cons, List.length_nil] using
      BlockAt.suffix program base _ _ setupBlock
  have setupFits : base + 7 < 2 ^ width := by
    simp only [callerCode, List.length_append, ForestCursorRootStore.rootCode_length] at fits
    omega
  have foundFits : layout.found < 2 ^ width := by
    have size := held.persistent.size
    have bound := held.selector.foundValid
    omega
  have liveCell : cell < state.heap.size := by rw [held.persistent.size]; exact cellValid
  have cellFits : cell < 2 ^ width := Nat.lt_of_lt_of_le cellValid heapFits
  obtain ⟨sa, sl, st, first⟩ := ForestCursorRootStore.root_execution program state.heap
    base layout.found cell position.val address loaded temporary setupFits foundFits
    held.selector.foundValid cellFits liveCell test store
  have nextHeld := ForestCursorRootStore.setup_runtimeStored graph records routes layout state held
    cell position.val separate persistent
  have rootBlock : BlockAt program (base + 7)
      (ForestCursorTraversal.rootCode graph records layout index b target (base + 7) (graph.roots.get position)) := by
    simpa only [ForestCursorRootStore.rootCode_length] using traversalBlock
  obtain ⟨fa, fl, ft, ticks, peak, second, tickBound, spaceBound, finalHeld, restored, result⟩ :=
    ForestCursorRoot.root_execution program graph (graph.roots.get position) records routes layout
      readonly index b target (afterSetup layout cell position.val state) nextHeld capacity
      heapFits oneFits indexed (base + 7) sa sl st output
      (by simpa only [callerCode, List.length_append, ForestCursorRootStore.rootCode_length,
        Nat.add_assoc] using fits) rootBlock
  have trace := (first.frame state.navigation output).append second
  refine ⟨fa, fl, ft,
    (if (storedWord state.heap layout.found).val = 0 then 6 else 4) + ticks,
    max (5 + state.heap.size + (state.navigation.length + output.length)) peak,
    ?_, ?_, ?_, finalHeld, restored⟩
  · simpa only [callerModel, afterSetup, callerCode, List.length_append,
      ForestCursorRootStore.rootCode_length, Nat.add_assoc] using trace
  · split <;> omega
  · have sameSize : (afterSetup layout cell position.val state).heap.size = state.heap.size := by
      simp only [afterSetup, ForestCursorRootStore.rootHeap_size]
    simp only [afterSetup] at spaceBound
    rw [ForestCursorRootStore.rootHeap_size] at spaceBound
    apply max_le
    · omega
    · exact spaceBound

def rootsCode (graph : DAG n) (records : GraphRecords width initialHeap graph)
    (layout : SelectorLayout n) (cell : ℕ)
    (indices : Fin graph.roots.length → OccurrenceIndex graph) (b : ℕ) (target : Channel n) :
    ℕ → List (Fin graph.roots.length) → ForestCounter.Code width
  | _, [] => []
  | base, position :: rest =>
      let first := callerCode graph records layout cell (indices position) b target base position
      first ++ rootsCode graph records layout cell indices b target (base + first.length) rest

def rootsModel (graph : DAG n) (layout : SelectorLayout n) (cell : ℕ)
    (indices : Fin graph.roots.length → OccurrenceIndex graph) (b : ℕ) (target : Channel n) :
    RuntimeModel width n → List (Fin graph.roots.length) → RuntimeModel width n
  | state, [] => state
  | state, position :: rest => rootsModel graph layout cell indices b target
      (callerModel graph layout cell (indices position) b target state position) rest

def rootOperations (graph : DAG n) (positions : List (Fin graph.roots.length)) : ℕ :=
  (positions.map fun position => (cursorOps graph (graph.roots.get position) []).length).sum

theorem caller_navigation (graph : DAG n) (layout : SelectorLayout n) (cell : ℕ)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (position : Fin graph.roots.length) :
    (callerModel graph layout cell index b target state position).navigation = state.navigation :=
  root_model_navigation graph (graph.roots.get position) layout index b target
    (afterSetup layout cell position.val state)

/-- Complete emitted multi-root execution. Counters and persistent cells are
reused at every boundary; no allocation or initialization appears in the loop. -/
theorem roots_execution (program : Program width 4) (graph : DAG n)
    (records : GraphRecords width initialHeap graph) (routes : RouteDescriptors width initialHeap)
    (layout : SelectorLayout n) (readonly : ReadonlyLayout graph records routes layout)
    (cell : ℕ) (separate : ForestCursorRootStore.RootCellLayout layout cell)
    (persistent : ∀ address, PersistentCell graph records routes address → address ≠ cell)
    (indices : Fin graph.roots.length → OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (positions : List (Fin graph.roots.length)) (state : RuntimeModel width n)
    (held : RuntimeStored graph records routes layout state)
    (capacity : ∀ position ∈ positions, ∀ channel,
      state.counters channel + (walkEvents graph (graph.roots.get position)).length + 1 < 2 ^ width)
    (heapFits : initialHeap.size ≤ 2 ^ width) (oneFits : 1 < 2 ^ width)
    (indexed : ∀ position ∈ positions, RootIndex graph (graph.roots.get position) routes (indices position))
    (cellValid : cell < initialHeap.size)
    (base : ℕ) (address loaded temporary : Word width) (output : List (Word width))
    (fits : base + (rootsCode graph records layout cell indices b target base positions).length < 2 ^ width)
    (block : BlockAt program base (rootsCode graph records layout cell indices b target base positions)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program
        ((counterState state.heap base address loaded temporary).frame state.navigation output)
        ((counterState (rootsModel graph layout cell indices b target state positions).heap
          (base + (rootsCode graph records layout cell indices b target base positions).length)
          finalAddress finalLoaded finalTemporary).frame state.navigation output) ticks peak ∧
      ticks ≤ 6 * positions.length + 20 * rootOperations graph positions ∧
      peak ≤ 6 + state.heap.size + state.navigation.length + rootOperations graph positions + output.length ∧
      RuntimeStored graph records routes layout (rootsModel graph layout cell indices b target state positions) ∧
      (rootsModel graph layout cell indices b target state positions).counters = state.counters := by
  induction positions generalizing state base address loaded temporary with
  | nil =>
      refine ⟨address, loaded, temporary, 0,
        ((counterState state.heap base address loaded temporary).frame state.navigation output).liveWords,
        ?_, ?_, ?_, held, rfl⟩
      · simpa only [rootsCode, rootsModel, List.length_nil, Nat.add_zero] using
          Execution.refl (p := program) ((counterState state.heap base address loaded temporary).frame state.navigation output)
      · simp [rootOperations]
      · simp only [rootOperations, List.map_nil, List.sum_nil, State.frame_liveWords, counterState_liveWords]
        omega
  | cons position rest ih =>
      have cover := block
      rw [rootsCode] at cover
      have firstBlock := BlockAt.prefix program base _ _ cover
      have restBlock := BlockAt.suffix program base _ _ cover
      have firstFits : base + (callerCode graph records layout cell (indices position) b target base position).length < 2 ^ width := by
        simp only [rootsCode, List.length_append] at fits
        omega
      obtain ⟨fa, fl, ft, firstTicks, firstPeak, first, firstBound, firstSpace, nextHeld, restored⟩ :=
        caller_execution program graph records routes layout readonly cell separate persistent
          (indices position) b target position state held (capacity position List.mem_cons_self)
          heapFits oneFits (indexed position List.mem_cons_self) cellValid base address loaded temporary
          output firstFits firstBlock
      let next := callerModel graph layout cell (indices position) b target state position
      have sameSize : next.heap.size = state.heap.size := nextHeld.persistent.size.trans held.persistent.size.symm
      have sameNavigation : next.navigation = state.navigation :=
        caller_navigation graph layout cell (indices position) b target state position
      obtain ⟨la, ll, lt, restTicks, restPeak, second, restBound, restSpace, finalHeld, finalCounters⟩ :=
        ih next nextHeld
          (fun pos member channel => by rw [restored]; exact capacity pos (List.mem_cons_of_mem position member) channel)
          (fun pos member => indexed pos (List.mem_cons_of_mem position member))
          (base + (callerCode graph records layout cell (indices position) b target base position).length)
          fa fl ft
          (by simpa only [rootsCode, List.length_append, Nat.add_assoc] using fits) restBlock
      have second' := second
      rw [sameNavigation] at second'
      have trace := first.append second'
      refine ⟨la, ll, lt, firstTicks + restTicks, max firstPeak restPeak, ?_, ?_, ?_, finalHeld,
        finalCounters.trans restored⟩
      · simpa only [rootsCode, rootsModel, List.length_append, Nat.add_assoc] using trace
      · simp only [rootOperations, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
      · rw [sameSize, sameNavigation] at restSpace
        simp only [rootOperations] at restSpace
        simp only [rootOperations, List.map_cons, List.sum_cons]
        apply max_le <;> omega

/-- All traversal indices and initial counter/selector invariants come from
actual setup and source captures. Only the source graph records and program
coverage are supplied; their construction costs are not hidden in this theorem. -/
theorem concrete_roots_execution (width : ℕ) (program : Program width 4)
    (heap : Array (Word width)) (graph : DAG n) (records : GraphRecords width heap graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (b : ℕ) (target : Channel n)
    (capacity : ∀ position : Fin graph.roots.length, ∀ channel : Channel n,
      (walkEvents graph (graph.roots.get position)).length + 1 < 2 ^ width)
    (heapFits : (setupHeap width heap graph).size ≤ 2 ^ width) (oneFits : 1 < 2 ^ width)
    (base : ℕ) (address loaded temporary : Word width) (output : List (Word width))
    (fits : base + (rootsCode graph (setupRecords width heap graph records) (setupLayout heap graph)
      (provenanceCell heap graph) (sourceIndices graph) b target base
      (List.finRange graph.roots.length)).length < 2 ^ width)
    (block : BlockAt program base
      (rootsCode graph (setupRecords width heap graph records) (setupLayout heap graph)
        (provenanceCell heap graph) (sourceIndices graph) b target base (List.finRange graph.roots.length))) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program ((counterState (setupHeap width heap graph) base address loaded temporary).frame [] output)
        ((counterState (rootsModel graph (setupLayout heap graph) (provenanceCell heap graph)
          (sourceIndices graph) b target (setupRuntime width heap graph) (List.finRange graph.roots.length)).heap
          (base + (rootsCode graph (setupRecords width heap graph records) (setupLayout heap graph)
            (provenanceCell heap graph) (sourceIndices graph) b target base
            (List.finRange graph.roots.length)).length) finalAddress finalLoaded finalTemporary).frame [] output)
        ticks peak ∧ ticks ≤ 6 * graph.roots.length + 20 * rootOperations graph (List.finRange graph.roots.length) ∧
      peak ≤ 6 + (setupHeap width heap graph).size + rootOperations graph (List.finRange graph.roots.length) + output.length ∧
      RuntimeStored graph (setupRecords width heap graph records) (setupRoutes width heap graph countFits positionFits)
        (setupLayout heap graph) (rootsModel graph (setupLayout heap graph) (provenanceCell heap graph)
          (sourceIndices graph) b target (setupRuntime width heap graph) (List.finRange graph.roots.length)) ∧
      (rootsModel graph (setupLayout heap graph) (provenanceCell heap graph) (sourceIndices graph)
        b target (setupRuntime width heap graph) (List.finRange graph.roots.length)).counters = (fun _ : Channel n => 0) := by
  have run := roots_execution program graph (setupRecords width heap graph records)
    (setupRoutes width heap graph countFits positionFits) (setupLayout heap graph)
    (setup_readonly width heap graph records countFits positionFits) (provenanceCell heap graph)
    (provenance_separate heap graph) (setup_provenance_persistent width heap graph records countFits positionFits)
    (sourceIndices graph) b target (List.finRange graph.roots.length) (setupRuntime width heap graph)
    (setup_runtimeStored width heap graph _ _)
    (fun position _ channel => by simpa only [setupRuntime, Nat.zero_add] using capacity position channel)
    heapFits oneFits (fun position _ => source_indices width heap graph countFits positionFits position)
    (by rw [setupHeap_size]; unfold provenanceCell setupOffset; omega)
    base address loaded temporary output fits block
  simpa only [setupRuntime, List.length_finRange, List.length_nil, Nat.add_zero] using run

end Controller.Cost.ForestCursorAllRootsExecution
