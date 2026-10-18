module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorAllRootsExecution
public import Controller.Cost.ForestCursorCharging

@[expose] public section

/-!
# Once-initialized unweighted forest cursor program

The program allocates the final shared parent records and zero counter region,
then executes every declared-root caller in the same instruction array. Root
identifiers fit because each declared caller contributes seven instructions.
The contracts count fetched setup and traversal instructions. Construction of
the supplied source records and instruction array, weighted score replacement,
and final witness reconstruction have separate costs.
-/
namespace Controller.Cost.ForestCursorWholeProgram

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorExecution
open Controller.Cost.ForestCursorRoot Controller.Cost.ForestGuardSchedule
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorMaterialize
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorAllRootsExecution

@[simp] theorem setupCode_length (width : ℕ) (graph : DAG n) :
    (setupCode width graph).length = 4 * (buildRoots graph).count + 2 * (n + 3) := by
  simp only [setupCode, writeCode_length, setupValues_length]
  omega

noncomputable def wholeCode (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph) (b : ℕ) (target : Channel n) (base : ℕ) :
    ForestCounter.Code width :=
  setupCode width graph ++ rootsCode graph (setupRecords width heap graph records)
    (setupLayout heap graph) (provenanceCell heap graph) (sourceIndices graph) b target
    (base + (setupCode width graph).length) (List.finRange graph.roots.length)

noncomputable def wholeModel (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (b : ℕ) (target : Channel n) : RuntimeModel width n :=
  rootsModel graph (setupLayout heap graph) (provenanceCell heap graph) (sourceIndices graph)
    b target (setupRuntime width heap graph) (List.finRange graph.roots.length)

/-- Seven actual emitted instructions per declared-root provenance block. -/
theorem rootsCode_seven_bound (graph : DAG n) (records : GraphRecords width initialHeap graph)
    (layout : SelectorLayout n) (cell : ℕ) (indices : Fin graph.roots.length → OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (positions : List (Fin graph.roots.length)) (base : ℕ) :
    7 * positions.length ≤ (rootsCode graph records layout cell indices b target base positions).length := by
  induction positions generalizing base with
  | nil => simp [rootsCode]
  | cons position rest ih =>
      have tail := ih (base + (callerCode graph records layout cell (indices position) b target base position).length)
      simp only [rootsCode, List.length_append, callerCode, ForestCursorRootStore.rootCode_length,
        List.length_cons] at *
      omega

/-- The emitted program capacity guarantees exact encoding of every root ID. -/
theorem rootIdentifiers_fit (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph) (b : ℕ) (target : Channel n) (base : ℕ)
    (fits : base + (wholeCode width heap graph records b target base).length < 2 ^ width)
    (position : Fin graph.roots.length) : position.val < 2 ^ width := by
  have count := rootsCode_seven_bound graph (setupRecords width heap graph records)
    (setupLayout heap graph) (provenanceCell heap graph) (sourceIndices graph) b target
    (List.finRange graph.roots.length) (base + (setupCode width graph).length)
  simp only [List.length_finRange] at count
  simp only [wholeCode, List.length_append] at fits
  have bounded := position.isLt
  omega

theorem rootIdentifiers_injective (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (records : GraphRecords width heap graph) (b : ℕ) (target : Channel n) (base : ℕ)
    (fits : base + (wholeCode width heap graph records b target base).length < 2 ^ width)
    (first second : Fin graph.roots.length)
    (equal : word width first.val = word width second.val) : first = second := by
  apply Fin.ext
  have natural := congrArg (fun value : Word width => value.val) equal
  simpa only [word, Nat.mod_eq_of_lt (rootIdentifiers_fit width heap graph records b target base fits first),
    Nat.mod_eq_of_lt (rootIdentifiers_fit width heap graph records b target base fits second)] using natural

/-- One shared program executes physical setup and all source-derived root
callers. All setup allocations occur before the first root traversal. -/
theorem whole_execution (width : ℕ) (program : Program width 4)
    (heap : Array (Word width)) (graph : DAG n) (records : GraphRecords width heap graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (b : ℕ) (target : Channel n)
    (capacity : ∀ position : Fin graph.roots.length, ∀ channel : Channel n,
      (walkEvents graph (graph.roots.get position)).length + 1 < 2 ^ width)
    (heapFits : (setupHeap width heap graph).size ≤ 2 ^ width) (oneFits : 1 < 2 ^ width)
    (base : ℕ) (address loaded temporary : Word width) (output : List (Word width))
    (fits : base + (wholeCode width heap graph records b target base).length < 2 ^ width)
    (block : BlockAt program base (wholeCode width heap graph records b target base)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks peak : ℕ,
      Execution program ((counterState heap base address loaded temporary).frame [] output)
        ((counterState (wholeModel width heap graph b target).heap
          (base + (wholeCode width heap graph records b target base).length)
          finalAddress finalLoaded finalTemporary).frame [] output) ticks peak ∧
      ticks ≤ 4 * (buildRoots graph).count + 2 * (n + 3) +
        6 * graph.roots.length + 20 * rootOperations graph (List.finRange graph.roots.length) ∧
      peak ≤ 6 + (setupHeap width heap graph).size + rootOperations graph (List.finRange graph.roots.length) + output.length ∧
      RuntimeStored graph (setupRecords width heap graph records) (setupRoutes width heap graph countFits positionFits)
        (setupLayout heap graph) (wholeModel width heap graph b target) ∧
      (wholeModel width heap graph b target).counters = (fun _ : Channel n => 0) := by
  have cover := block
  unfold wholeCode at cover
  have setupBlock := BlockAt.prefix program base _ _ cover
  have rootBlock := BlockAt.suffix program base _ _ cover
  obtain ⟨nextTemporary, setupTrace⟩ := setup_execution program heap graph base address loaded temporary
    (by simp only [wholeCode, List.length_append, setupCode_length] at fits; omega)
    (by rw [setupHeap_size] at heapFits; exact heapFits) setupBlock
  obtain ⟨fa, fl, ft, rootTicks, rootPeak, rootTrace, timeBound, spaceBound, held, counters⟩ :=
    concrete_roots_execution width program heap graph records countFits positionFits b target capacity heapFits
      oneFits (base + (setupCode width graph).length) address loaded nextTemporary output
      (by simpa only [wholeCode, List.length_append, Nat.add_assoc] using fits) rootBlock
  have first := setupTrace.frame [] output
  rw [← setupCode_length width graph] at first
  have trace := first.append rootTrace
  refine ⟨fa, fl, ft, (setupCode width graph).length + rootTicks,
    max (5 + heap.size + 2 * (buildRoots graph).count + (n + 3) + output.length) rootPeak,
    ?_, ?_, ?_, held, counters⟩
  · simpa only [wholeCode, wholeModel, List.length_append, List.length_nil, Nat.zero_add,
      Nat.add_assoc] using trace
  · rw [setupCode_length]
    omega
  · have sameSize := setupHeap_size width heap graph
    apply max_le
    · omega
    · exact spaceBound

private theorem allocations_le_length (operations : List (CursorOp n)) :
    allocations operations ≤ operations.length := by
  induction operations with
  | nil => simp [allocations]
  | cons operation rest ih =>
      cases operation <;> simp only [allocations, List.map_cons, List.sum_cons, isDown, List.length_cons] at * <;> omega

private theorem map_sum_bound (items : List α) (first second : α → ℕ)
    (bound : ∀ item ∈ items, first item ≤ second item) :
    (items.map first).sum ≤ (items.map second).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := bound item List.mem_cons_self
      have tail := ih (fun current present => bound current (List.mem_cons_of_mem item present))
      simp only [List.map_cons, List.sum_cons]
      omega

theorem descriptor_count_le_operations (graph : DAG n) :
    (buildRoots graph).count ≤ rootOperations graph (List.finRange graph.roots.length) := by
  rw [← (buildRoots_valid graph).count, buildRoots_count]
  exact map_sum_bound _ _ _ (fun position _ => allocations_le_length _)

theorem rootOperations_total (graph : DAG n) :
    rootOperations graph (List.finRange graph.roots.length) = ForestCursorCharging.allRootBudget graph := by
  unfold rootOperations ForestCursorCharging.allRootBudget
  simp only [ForestCursorCharging.cursor_length]
  have same := congrArg (List.map (ForestCursorCharging.operationBudget graph)) (List.map_get_finRange graph.roots)
  simpa only [List.map_map, Function.comp_def] using congrArg List.sum same

/-- A bound on the actual whole execution transfers to counted source incidences. -/
theorem whole_ticks_forest (graph : DAG n) (forest : graph.FormulaForest) (ticks : ℕ)
    (executed : ticks ≤ 4 * (buildRoots graph).count + 2 * (n + 3) +
      6 * graph.roots.length + 20 * rootOperations graph (List.finRange graph.roots.length)) :
    ticks ≤ 2 * (n + 3) + 102 * graph.roots.length + 96 * graph.childIncidences + 48 * graph.guardIncidences := by
  have descriptors := descriptor_count_le_operations graph
  have source := ForestCursorCharging.all_root_budget_bound graph forest
  rw [← rootOperations_total] at source
  omega

/-- Before any selected leaf, the current root's exact ID is retained through
all traversal stores. Sentinel pointer zero does not erase this provenance. -/
theorem caller_provenance_fresh (graph : DAG n) (records : GraphRecords width initialHeap graph)
    (routes : RouteDescriptors width initialHeap) (layout : SelectorLayout n) (cell : ℕ)
    (separate : ForestCursorRootStore.RootCellLayout layout cell)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (held : RuntimeStored graph records routes layout state)
    (fresh : state.selected = none) (position : Fin graph.roots.length)
    (cellValid : cell < state.heap.size) (identifierFits : position.val < 2 ^ width) :
    (storedWord (callerModel graph layout cell index b target state position).heap cell).val = position.val := by
  have foundZero : (storedWord state.heap layout.found).val = 0 := by
    rw [storedWord_eq state.heap layout.found held.selector.foundValid]
    have zero : state.heap[layout.found]'held.selector.foundValid = word width 0 := by
      simpa [fresh] using held.selector.foundWord
    rw [zero]
    simp [word]
  have preserved := ForestCursorRootStore.runModel_rootCell layout index b target
    (afterSetup layout cell position.val state) cell separate (cursorOps graph (graph.roots.get position) [])
  have kept : storedWord (callerModel graph layout cell index b target state position).heap cell =
      storedWord (afterSetup layout cell position.val state).heap cell := by
    unfold storedWord callerModel
    rw [preserved]
  rw [kept]
  exact ForestCursorRootStore.rootHeap_decodes width state.heap layout.found cell position.val
    foundZero cellValid identifierFits

/-- Once selected, later roots retain both the pointer and its root-ID word. -/
theorem caller_provenance_selected (graph : DAG n) (records : GraphRecords width initialHeap graph)
    (routes : RouteDescriptors width initialHeap) (layout : SelectorLayout n) (cell : ℕ)
    (separate : ForestCursorRootStore.RootCellLayout layout cell)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n)
    (state : RuntimeModel width n) (held : RuntimeStored graph records routes layout state)
    (pointer : ℕ) (selected : state.selected = some pointer) (position : Fin graph.roots.length)
    (oneFits : 1 < 2 ^ width) :
    (callerModel graph layout cell index b target state position).selected = some pointer ∧
      storedWord (callerModel graph layout cell index b target state position).heap cell = storedWord state.heap cell := by
  have nonzero : (storedWord state.heap layout.found).val ≠ 0 := by
    rw [storedWord_eq state.heap layout.found held.selector.foundValid]
    have one : state.heap[layout.found]'held.selector.foundValid = word width 1 := by
      simpa [selected] using held.selector.foundWord
    rw [one]
    simp only [word, Nat.mod_eq_of_lt oneFits]
    omega
  have setupEq : (afterSetup layout cell position.val state).heap = state.heap :=
    ForestCursorRootStore.rootHeap_selected width state.heap layout.found cell position.val nonzero
  constructor
  · exact ForestCursorRootStore.runModel_selected layout index b target
      (afterSetup layout cell position.val state) pointer selected _
  · have preserved := ForestCursorRootStore.runModel_rootCell layout index b target
      (afterSetup layout cell position.val state) cell separate (cursorOps graph (graph.roots.get position) [])
    unfold storedWord callerModel
    rw [preserved, setupEq]

end Controller.Cost.ForestCursorWholeProgram
