module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroNonemptyImage
public import Controller.Cost.ForestZeroSourcePlan
public import Controller.Physical.DetectionBridge

@[expose] public section

/-! The resident source constructor's semantic image is the original guarded
root-zero problem with its actual forced target. -/
namespace Controller.Cost.ForestZeroControllerImage
open Controller Controller.CNF Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroCompile Controller.Cost.GateProgram
open Controller.Cost.ForestZeroRows

/-- The optional nonemptiness row contributes no extra semantic restriction
once the actual query forces its physical target channel true. -/
theorem forced_constructor_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (position : Fin graph.roots.length) (target : Fin n)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size) :
    Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
      (empty_coherent _) (forcedQuery (width := width) graph rows rawRoots rowsMatch position target)
      n (Nat.le_add_right _ _)) ↔
      ∃ K : Finset (Channel n), graph.eval (assignmentOfSet K) (graph.roots.get position) = false ∧
        target ∈ K := by
  rw [ForestZeroNonemptyImage.constructor_satisfiable_iff]
  constructor
  · rintro ⟨values, model, _⟩
    let channels : Assignment n := fun channel => values (sourceIndex graph (.inl channel))
    let activities : Fin graph.nodeCount → Bool := fun node => values (sourceIndex graph (.inr node))
    have same : sourceAssignment graph (assignmentOfSet (setOfAssignment channels)) activities = values := by
      rw [assignmentOfSet_setOfAssignment]
      exact sourceAssignment_split graph values
    refine ⟨setOfAssignment channels, (forced_query_zero_iff (width := width) graph guarded rows rawRoots rowsMatch position target _).mp ?_⟩
    exact ⟨activities, same.symm ▸ model⟩
  · rintro ⟨K, zero⟩
    obtain ⟨activities, model⟩ := (forced_query_zero_iff (width := width) graph guarded rows rawRoots rowsMatch position target K).mpr zero
    refine ⟨sourceAssignment graph (assignmentOfSet K) activities, model, target, ?_⟩
    have index : (⟨target.val, lt_of_lt_of_le target.isLt (Nat.le_add_right n graph.nodeCount)⟩ :
        Fin (n + graph.nodeCount)) = sourceIndex graph (.inl target) := by
      apply Fin.ext
      rfl
    rw [index, sourceAssignment_index]
    exact (assignmentOfSet_eq_true K target).mpr zero.2


/-- For a healthy-one observation on one bus, the actual finite query formula
is equivalent to literal physical bridge detection. -/
theorem forced_constructor_physical_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (position : Fin graph.roots.length) (bridge : Physical.Bridge n)
    (healthy : graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = true)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size) :
    Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
      (empty_coherent _) (forcedQuery (width := width) graph rows rawRoots rowsMatch position bridge.target)
      n (Nat.le_add_right _ _)) ↔
      Physical.BridgeDetectable (b := 1) bridge true
        (fun _ : Fin 1 => fun assignment => graph.eval assignment (graph.roots.get position)) := by
  rw [forced_constructor_iff graph guarded rows rawRoots rowsMatch position bridge.target heap layout,
    Physical.bridge_detectable_iff_exists_output bridge (by decide)]
  constructor
  · rintro ⟨K, zero, contains⟩
    refine ⟨rfl, K, (admissible_one bridge.target K).mpr contains, ⟨0, by decide⟩, ?_⟩
    rw [zero, healthy]
    decide
  · rintro ⟨_, K, admissible, output, different⟩
    have contains := (admissible_one bridge.target K).mp admissible
    cases value : graph.eval (assignmentOfSet K) (graph.roots.get position) with
    | false => exact ⟨K, value, contains⟩
    | true => exact False.elim (different (value.trans healthy.symm))


/-- The declared output list has a satisfiable forced query exactly when one
original output admits a target-containing zero witness. -/
theorem declared_queries_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (target : Fin n) (heap : Array (Word width))
    (layout : Layout (n + graph.nodeCount) heap.size) :
    (∃ position : Fin graph.roots.length,
      Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
        (empty_coherent _) (forcedQuery (width := width) graph rows rawRoots rowsMatch position target)
        n (Nat.le_add_right _ _))) ↔
    ∃ position : Fin graph.roots.length, ∃ K : Finset (Channel n),
      graph.eval (assignmentOfSet K) (graph.roots.get position) = false ∧ target ∈ K := by
  constructor
  · rintro ⟨position, satisfiable⟩
    exact ⟨position, (forced_constructor_iff graph guarded rows rawRoots rowsMatch
      position target heap layout).mp satisfiable⟩
  · rintro ⟨position, witness⟩
    exact ⟨position, (forced_constructor_iff graph guarded rows rawRoots rowsMatch
      position target heap layout).mpr witness⟩


/-- For healthy-one outputs, the whole declared query family characterizes
literal one-bus physical detection, including duplicate root positions. -/
theorem declared_queries_physical_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (bridge : Physical.Bridge n)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = true)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size) :
    (∃ position : Fin graph.roots.length,
      Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
        (empty_coherent _) (forcedQuery (width := width) graph rows rawRoots rowsMatch position bridge.target)
        n (Nat.le_add_right _ _))) ↔
    Physical.BridgeDetectable (b := 1) bridge true
      (fun position : Fin graph.roots.length => fun assignment =>
        graph.eval assignment (graph.roots.get position)) := by
  rw [declared_queries_iff graph guarded rows rawRoots rowsMatch bridge.target heap layout,
    Physical.bridge_detectable_iff_exists_output bridge (by decide)]
  constructor
  · rintro ⟨position, K, zero, contains⟩
    refine ⟨rfl, K, (admissible_one bridge.target K).mpr contains, position, ?_⟩
    rw [zero, healthy position]
    decide
  · rintro ⟨_, K, admissible, position, different⟩
    refine ⟨position, K, ?_, (admissible_one bridge.target K).mp admissible⟩
    cases value : graph.eval (assignmentOfSet K) (graph.roots.get position) with
    | false => rfl
    | true => exact False.elim (different (value.trans (healthy position).symm))


/-- The execution's actual terminal queue model lifts to a model of the source
rows, and the same lifted channel values are the emitted output prefix. -/
theorem query_witness_source_model (heap : Array (Word width))
    (layout : Layout ambient heap.size)
    (references : List (List (ForestZeroEmit.Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) (observed : List (Word width))
    (witness : QueryChannelWitness heap layout references channels within observed) :
    ∃ values : Fin ambient → Bool,
      Satisfies values (ofClauses (ForestZeroAssembly.originalRows references)) ∧
      ∃ previous : List (Word width),
        observed = (List.finRange channels).map (fun channel =>
          ForestZeroChannelEmit.bitWord width
            (values ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩)) ++
          word width 1 :: previous := by
  obtain ⟨queue, previous, model, _, emitted⟩ := witness
  let localValues := ForestZeroChannelEmit.localValues queue
  have rawModel : Satisfies localValues
      (ofClauses (ForestZeroNonemptyImage.nonemptyRows (empty ambient)
        (ForestZeroAssembly.originalRows references) channels)) := by
    rw [← ForestZeroNonemptyImage.constructor_clauses_raw heap layout (empty ambient)
      (empty_coherent _) references channels within]
    rw [satisfies_ofClauses]
    intro row member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have finiteModel := (satisfies_ofClauses _ _).mp model original present
    obtain ⟨literal, belongs, holds⟩ := finiteModel
    refine ⟨(literal.1.val, literal.2), List.mem_map.mpr ⟨literal, belongs, rfl⟩, ?_⟩
    simpa [LiteralHolds, localValues, ForestZeroChannelEmit.localValues, literal.1.isLt] using holds
  have compiledModel : Satisfies localValues
      (ofClauses (compileRows (empty ambient) (ForestZeroAssembly.originalRows references)).2.1) := by
    rw [satisfies_ofClauses] at rawModel ⊢
    intro row member
    apply rawModel row
    unfold ForestZeroNonemptyImage.nonemptyRows
    dsimp only
    split_ifs
    · exact List.mem_append_left _ member
    · exact member
  let values := ForestZeroModelLift.lift
    (constructorDictionary heap layout (empty ambient) references) true localValues
  refine ⟨values, ?_, previous, emitted⟩
  dsimp only [values]
  rw [ForestZeroNonemptyImage.constructor_dictionary_eq]
  exact (ForestZeroModelLift.rows_lift_model (empty ambient) (empty_coherent _)
    (ForestZeroAssembly.originalRows references) true localValues).mp compiledModel


/-- The exact returned bit prefix is a target-containing zero witness for the
selected original root; it is the lift of this execution's queue model. -/
theorem forced_query_output_witness (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (position : Fin graph.roots.length) (target : Fin n)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size)
    (observed : List (Word width))
    (witness : QueryChannelWitness heap layout
      (forcedQuery (width := width) graph rows rawRoots rowsMatch position target)
      n (Nat.le_add_right _ _) observed) :
    ∃ K : Finset (Channel n),
      graph.eval (assignmentOfSet K) (graph.roots.get position) = false ∧ target ∈ K ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  obtain ⟨values, model, previous, emitted⟩ := query_witness_source_model heap layout _ n
    (Nat.le_add_right _ _) observed witness
  let channels : Assignment n := fun channel => values (sourceIndex graph (.inl channel))
  let activities : Fin graph.nodeCount → Bool := fun node => values (sourceIndex graph (.inr node))
  let K := setOfAssignment channels
  have same : sourceAssignment graph (assignmentOfSet K) activities = values := by
    dsimp only [K]
    rw [assignmentOfSet_setOfAssignment]
    exact sourceAssignment_split graph values
  obtain ⟨zero, contains⟩ := (forced_query_zero_iff (width := width) graph guarded rows rawRoots
    rowsMatch position target K).mp ⟨activities, same.symm ▸ model⟩
  refine ⟨K, zero, contains, previous, ?_⟩
  dsimp only [K]
  rw [assignmentOfSet_setOfAssignment]
  exact emitted


/-- The returned channel prefix constructs a literal physical detecting input
for a healthy-one observation of its original root. -/
theorem forced_query_output_physical (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (position : Fin graph.roots.length) (bridge : Physical.Bridge n)
    (healthy : graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = true)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size)
    (observed : List (Word width))
    (witness : QueryChannelWitness heap layout
      (forcedQuery (width := width) graph rows rawRoots rowsMatch position bridge.target)
      n (Nat.le_add_right _ _) observed) :
    ∃ K : Finset (Channel n), Admissible 1 bridge.target K ∧
      Physical.BridgeInputDetects bridge true
        (fun _ : Fin 1 => fun assignment => graph.eval assignment (graph.roots.get position))
        (Physical.realizeBridge bridge (by decide : 0 < 1) K) true ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  obtain ⟨K, zero, contains, previous, emitted⟩ :=
    forced_query_output_witness graph guarded rows rawRoots rowsMatch position bridge.target
      heap layout observed witness
  have admissible := (admissible_one bridge.target K).mpr contains
  refine ⟨K, admissible, ?_, previous, emitted⟩
  apply (Physical.realizeBridge_detects_iff bridge (by decide : 0 < 1) K admissible _).mpr
  refine ⟨(0 : Fin 1), ?_⟩
  change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) ≠
    graph.eval (assignmentOfSet K) (graph.roots.get position)
  rw [healthy, zero]
  decide


/-- A selected stream position is precisely its original declared forced query. -/
theorem forced_query_stream_at (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (target : Fin n)
    (position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch target).length) :
    (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position] =
      forcedQuery (width := width) graph rows rawRoots rowsMatch
        ⟨position.val, by simpa only [forced_queries_length] using position.isLt⟩ target := by
  change (forcedQueries (width := width) graph rows rawRoots rowsMatch target)[position.val] = _
  simp only [forcedQueries, List.getElem_map, queries, List.getElem_ofFn, forcedQuery]

/-- The original position selected by the runtime's successful query supplies
a literal physical input whose channel bits are exactly the returned prefix. -/
theorem forced_stream_output_physical (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (bridge : Physical.Bridge n)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = true)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size)
    (observed : List (Word width))
    (position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch bridge.target).length)
    (witness : QueryChannelWitness heap layout
      (forcedQueries (width := width) graph rows rawRoots rowsMatch bridge.target)[position]
      n (Nat.le_add_right _ _) observed) :
    ∃ original : Fin graph.roots.length, ∃ K : Finset (Channel n),
      Admissible 1 bridge.target K ∧
      Physical.BridgeInputDetects bridge true
        (fun root : Fin graph.roots.length => fun assignment => graph.eval assignment (graph.roots.get root))
        (Physical.realizeBridge bridge (by decide : 0 < 1) K) true ∧
      graph.eval (assignmentOfSet K) (graph.roots.get original) = false ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  let original : Fin graph.roots.length :=
    ⟨position.val, by simpa only [forced_queries_length] using position.isLt⟩
  rw [forced_query_stream_at] at witness
  obtain ⟨K, zero, contains, previous, emitted⟩ := forced_query_output_witness graph guarded rows rawRoots
    rowsMatch original bridge.target heap layout observed witness
  have admissible := (admissible_one bridge.target K).mpr contains
  refine ⟨original, K, admissible, ?_, zero, previous, emitted⟩
  apply (Physical.realizeBridge_detects_iff bridge (by decide : 0 < 1) K admissible _).mpr
  refine ⟨original, ?_⟩
  change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get original) ≠
    graph.eval (assignmentOfSet K) (graph.roots.get original)
  rw [healthy original, zero]
  decide

/-- Cold fetched execution decides literal detection and returns its actual physical witness, with the original time and peak bounds. -/
theorem cold_physical_execution (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph rawRoots) (bridge : Physical.Bridge n)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = true) (forest : graph.FormulaForest)
    (priorProgram : Program width 8) (callerRest output : List (Word width))
    (address loaded temporary : Word width) (saved : Fin 8 → Word width)
    (programRoom :
      (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots bridge.target)
        (controlledLayout (width := width) graph rows rawRoots bridge.target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch bridge.target)).size < 2 ^ width)
    (wordRoom : (controlledHeap (width := width) graph rows rawRoots bridge.target).size + 2 * (n + graph.nodeCount) + 14 +
      5 * (5 * graph.roots.length + 3 * graph.childIncidences) +
      15 * (8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences) < 2 ^ width) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (residentProgram (coldPrefix priorProgram) (controlledHeap (width := width) graph rows rawRoots bridge.target)
        (controlledLayout (width := width) graph rows rawRoots bridge.target) n (Nat.le_add_right _ _)
        (forcedQueries (width := width) graph rows rawRoots rowsMatch bridge.target)) (coldInitial graph rows rawRoots bridge.target priorProgram.size callerRest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 63 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        14 * (n + graph.nodeCount) + 4288 * graph.roots.length + 2772 * graph.childIncidences +
        387 * graph.guardIncidences + 13 * n + 2 ∧
      peak ≤ (coldInitial graph rows rawRoots bridge.target priorProgram.size callerRest output address loaded temporary saved).liveWords + 2 * (n + graph.nodeCount) + 146 * graph.roots.length + 105 * graph.childIncidences +
        15 * graph.guardIncidences + 2 * n + 21 ∧
      (answer = true ↔ Physical.BridgeDetectable (b := 1) bridge true
        (fun position : Fin graph.roots.length => fun assignment => graph.eval assignment (graph.roots.get position))) ∧
      (answer = true → ∃ original : Fin graph.roots.length, ∃ K : Finset (Channel n),
        Admissible 1 bridge.target K ∧
        Physical.BridgeInputDetects bridge true
          (fun position : Fin graph.roots.length => fun assignment => graph.eval assignment (graph.roots.get position))
          (Physical.realizeBridge bridge (by decide : 0 < 1) K) true ∧
        graph.eval (assignmentOfSet K) (graph.roots.get original) = false ∧
        ∃ previous : List (Word width),
          final.output = (List.finRange n).map (fun channel =>
            ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
            word width 1 :: previous) := by
  obtain ⟨answer, final, ticks, peak, trace, halted, tag, timeBound, spaceBound, meaning, model⟩ :=
    cold_forced_resident_execution graph guarded rows rawRoots rowsMatch rootsMatch bridge.target forest
      priorProgram callerRest output address loaded temporary saved programRoom wordRoom
  refine ⟨answer, final, ticks, peak, trace, halted, tag, timeBound, spaceBound, ?_, ?_⟩
  · rw [meaning]
    have physical := declared_queries_physical_iff graph guarded rows rawRoots rowsMatch bridge healthy
      (controlledHeap (width := width) graph rows rawRoots bridge.target)
      (controlledLayout (width := width) graph rows rawRoots bridge.target)
    constructor
    · rintro ⟨position, satisfies⟩
      apply physical.mp
      refine ⟨⟨position.val, by simpa only [forced_queries_length] using position.isLt⟩, ?_⟩
      rw [forced_query_stream_at] at satisfies
      exact satisfies
    · intro detects
      obtain ⟨original, satisfies⟩ := physical.mpr detects
      let position : Fin (forcedQueries (width := width) graph rows rawRoots rowsMatch bridge.target).length :=
        ⟨original.val, by simpa only [forced_queries_length] using original.isLt⟩
      refine ⟨position, ?_⟩
      rw [forced_query_stream_at]
      exact satisfies
  · intro accepted
    obtain ⟨position, _, witness⟩ := model accepted
    exact forced_stream_output_physical graph guarded rows rawRoots rowsMatch bridge healthy
      (controlledHeap (width := width) graph rows rawRoots bridge.target)
      (controlledLayout (width := width) graph rows rawRoots bridge.target) final.output position witness

end Controller.Cost.ForestZeroControllerImage
