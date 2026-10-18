module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroControllerImage
public import Controller.Cost.ForestZeroSameLift

@[expose] public section

/-! Exact source models and enabled channels from the emitted queue witness. -/
namespace Controller.Cost.ForestZeroOutputImage
open Controller Controller.CNF Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroSourcePlan Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroCompile Controller.Cost.GateProgram
open Controller.Cost.ForestZeroRows

theorem query_witness_nonempty_source_model (heap : Array (Word width))
    (layout : Layout ambient heap.size)
    (references : List (List (ForestZeroEmit.Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) (observed : List (Word width))
    (witness : QueryChannelWitness heap layout references channels within observed) :
    ∃ values : Fin ambient → Bool,
      Satisfies values (ofClauses (ForestZeroAssembly.originalRows references)) ∧
      (∃ channel : Fin channels,
        values ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ = true) ∧
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
    simpa [LiteralHolds, localValues, ForestZeroChannelEmit.localValues,
      literal.1.isLt] using holds
  have lifted := ForestZeroSameLift.nonemptyRows_lift_model (empty ambient)
    (empty_coherent _) (ForestZeroAssembly.originalRows references) channels within
    localValues rawModel
  let values := ForestZeroModelLift.lift
    (constructorDictionary heap layout (empty ambient) references) true localValues
  have equality : values = ForestZeroModelLift.lift
      (compileRows (empty ambient) (ForestZeroAssembly.originalRows references)).1
      true localValues := by
    dsimp only [values]
    rw [ForestZeroNonemptyImage.constructor_dictionary_eq]
  refine ⟨values, equality.symm ▸ lifted.1, equality.symm ▸ lifted.2,
    previous, emitted⟩

/-- The emitted prefix is a nonempty zero witness for an unforced query. -/
theorem query_output_witness (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (position : Fin graph.roots.length)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size)
    (observed : List (Word width))
    (witness : QueryChannelWitness heap layout
      (query graph rows rawRoots rowsMatch position) n (Nat.le_add_right _ _) observed) :
    ∃ K : Finset (Channel n), K.Nonempty ∧
      graph.eval (assignmentOfSet K) (graph.roots.get position) = false ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  obtain ⟨values, model, ⟨channel, active⟩, previous, emitted⟩ :=
    query_witness_nonempty_source_model heap layout _ n (Nat.le_add_right _ _) observed witness
  let channels : Assignment n := fun channel => values (sourceIndex graph (.inl channel))
  let activities : Fin graph.nodeCount → Bool := fun node => values (sourceIndex graph (.inr node))
  let K := setOfAssignment channels
  have same : sourceAssignment graph (assignmentOfSet K) activities = values := by
    dsimp only [K]
    rw [assignmentOfSet_setOfAssignment]
    exact sourceAssignment_split graph values
  have zero := (query_zero_iff graph guarded rows rawRoots rowsMatch position K).mp
    ⟨activities, same.symm ▸ model⟩
  have present : channel ∈ K := by
    apply (mem_setOfAssignment channels channel).mpr
    exact active
  refine ⟨K, ⟨channel, present⟩, zero, previous, ?_⟩
  dsimp only [K]
  rw [assignmentOfSet_setOfAssignment]
  exact emitted

/-- Both bus branches return the exact original admissible root-zero witness. -/
theorem zero_query_output_witness (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (position : Fin graph.roots.length) (target : Fin n)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size)
    (observed : List (Word width))
    (witness : QueryChannelWitness heap layout
      (zeroQuery width graph rows rawRoots rowsMatch b position target)
      n (Nat.le_add_right _ _) observed) :
    ∃ K : Finset (Channel n), Admissible b target K ∧
      graph.eval (assignmentOfSet K) (graph.roots.get position) = false ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  by_cases one : b = 1
  · subst b
    rw [zeroQuery_one] at witness
    obtain ⟨K, zero, contains, previous, emitted⟩ :=
      ForestZeroControllerImage.forced_query_output_witness graph guarded rows rawRoots
        rowsMatch position target heap layout observed witness
    exact ⟨K, (admissible_one target K).mpr contains, zero, previous, emitted⟩
  · rw [zeroQuery_other graph rows rawRoots rowsMatch one] at witness
    obtain ⟨K, nonempty, zero, previous, emitted⟩ :=
      query_output_witness graph guarded rows rawRoots rowsMatch position heap layout observed witness
    exact ⟨K, ⟨nonempty, fun equality => False.elim (one equality)⟩,
      zero, previous, emitted⟩

/-- The returned bits realize a physical detecting input for a healthy-one root. -/
theorem zero_query_output_physical (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (positive : 0 < b) (position : Fin graph.roots.length)
    (bridge : Physical.Bridge n)
    (healthy : graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = true)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size)
    (observed : List (Word width))
    (witness : QueryChannelWitness heap layout
      (zeroQuery width graph rows rawRoots rowsMatch b position bridge.target)
      n (Nat.le_add_right _ _) observed) :
    ∃ K : Finset (Channel n), Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true
        (fun _ : Fin 1 => fun assignment => graph.eval assignment (graph.roots.get position))
        (Physical.realizeBridge bridge positive K) true ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  obtain ⟨K, admissible, zero, previous, emitted⟩ := zero_query_output_witness graph guarded
    rows rawRoots rowsMatch b position bridge.target heap layout observed witness
  refine ⟨K, admissible, ?_, previous, emitted⟩
  apply (Physical.realizeBridge_detects_iff bridge positive K admissible _).mpr
  refine ⟨(0 : Fin 1), ?_⟩
  change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) ≠
    graph.eval (assignmentOfSet K) (graph.roots.get position)
  rw [healthy, zero]
  decide

/-- An unforced constructor is satisfiable exactly for a nonempty original zero set. -/
theorem query_constructor_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (position : Fin graph.roots.length) (heap : Array (Word width))
    (layout : Layout (n + graph.nodeCount) heap.size) :
    Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
      (empty_coherent _) (query graph rows rawRoots rowsMatch position)
      n (Nat.le_add_right _ _)) ↔
      ∃ K : Finset (Channel n), K.Nonempty ∧
        graph.eval (assignmentOfSet K) (graph.roots.get position) = false := by
  rw [ForestZeroNonemptyImage.constructor_satisfiable_iff]
  constructor
  · rintro ⟨values, model, channel, active⟩
    let channels : Assignment n := fun channel => values (sourceIndex graph (.inl channel))
    let activities : Fin graph.nodeCount → Bool := fun node => values (sourceIndex graph (.inr node))
    have same : sourceAssignment graph (assignmentOfSet (setOfAssignment channels)) activities = values := by
      rw [assignmentOfSet_setOfAssignment]
      exact sourceAssignment_split graph values
    refine ⟨setOfAssignment channels, ⟨channel, ?_⟩,
      (query_zero_iff graph guarded rows rawRoots rowsMatch position _).mp
        ⟨activities, same.symm ▸ model⟩⟩
    exact (mem_setOfAssignment channels channel).mpr active
  · rintro ⟨K, ⟨channel, present⟩, zero⟩
    obtain ⟨activities, model⟩ :=
      (query_zero_iff graph guarded rows rawRoots rowsMatch position K).mpr zero
    refine ⟨sourceAssignment graph (assignmentOfSet K) activities, model, channel, ?_⟩
    have index : (⟨channel.val, lt_of_lt_of_le channel.isLt (Nat.le_add_right n graph.nodeCount)⟩ :
        Fin (n + graph.nodeCount)) = sourceIndex graph (.inl channel) := by
      apply Fin.ext
      rfl
    rw [index, sourceAssignment_index]
    exact (assignmentOfSet_eq_true K channel).mpr present

/-- Exact constructor characterization for both actual bus-query branches. -/
theorem zero_query_constructor_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (position : Fin graph.roots.length) (target : Fin n)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size) :
    Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
      (empty_coherent _) (zeroQuery width graph rows rawRoots rowsMatch b position target)
      n (Nat.le_add_right _ _)) ↔
      ∃ K : Finset (Channel n), Admissible b target K ∧
        graph.eval (assignmentOfSet K) (graph.roots.get position) = false := by
  by_cases one : b = 1
  · subst b
    rw [zeroQuery_one, ForestZeroControllerImage.forced_constructor_iff graph guarded]
    simp only [admissible_one]
    constructor <;> rintro ⟨K, left, right⟩ <;> exact ⟨K, right, left⟩
  · rw [zeroQuery_other graph rows rawRoots rowsMatch one,
      query_constructor_iff graph guarded]
    simp only [Admissible, one, false_implies, and_true]

/-- Stream positions retain the original declared occurrence, including duplicates. -/
theorem zero_query_stream_at (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (rowsMatch : RowsMatch graph rows) (b : Nat) (target : Fin n)
    (position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length) :
    (zeroQueries width graph rows rawRoots rowsMatch b target)[position] =
      zeroQuery width graph rows rawRoots rowsMatch b
        ⟨position.val, by simpa only [zeroQueries_length] using position.isLt⟩ target := by
  change (zeroQueries width graph rows rawRoots rowsMatch b target)[position.val] = _
  simp only [zeroQueries, List.getElem_ofFn]

/-- The resident answer's actual finite stream condition has an original-root meaning. -/
theorem zero_stream_constructor_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (target : Fin n) (heap : Array (Word width))
    (layout : Layout (n + graph.nodeCount) heap.size) :
    (∃ position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length,
      Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
        (empty_coherent _) (zeroQueries width graph rows rawRoots rowsMatch b target)[position]
        n (Nat.le_add_right _ _))) ↔
      ∃ K : Finset (Channel n), Admissible b target K ∧
        ∃ original : Fin graph.roots.length,
          graph.eval (assignmentOfSet K) (graph.roots.get original) = false := by
  constructor
  · rintro ⟨position, model⟩
    rw [zero_query_stream_at] at model
    obtain ⟨K, admissible, zero⟩ :=
      (zero_query_constructor_iff graph guarded rows rawRoots rowsMatch b _ target heap layout).mp model
    exact ⟨K, admissible, _, zero⟩
  · rintro ⟨K, admissible, original, zero⟩
    let position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length :=
      ⟨original.val, by simpa only [zeroQueries_length] using original.isLt⟩
    refine ⟨position, ?_⟩
    rw [zero_query_stream_at]
    exact (zero_query_constructor_iff graph guarded rows rawRoots rowsMatch b original
      target heap layout).mpr ⟨K, admissible, zero⟩

theorem zero_stream_output_witness (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (target : Fin n) (heap : Array (Word width))
    (layout : Layout (n + graph.nodeCount) heap.size) (observed : List (Word width))
    (position : Fin (zeroQueries width graph rows rawRoots rowsMatch b target).length)
    (witness : QueryChannelWitness heap layout
      (zeroQueries width graph rows rawRoots rowsMatch b target)[position]
      n (Nat.le_add_right _ _) observed) :
    ∃ original : Fin graph.roots.length, ∃ K : Finset (Channel n),
      Admissible b target K ∧ graph.eval (assignmentOfSet K) (graph.roots.get original) = false ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  rw [zero_query_stream_at] at witness
  obtain ⟨K, admissible, zero, previous, emitted⟩ :=
    zero_query_output_witness graph guarded rows rawRoots rowsMatch b _ target
      heap layout observed witness
  exact ⟨_, K, admissible, zero, previous, emitted⟩

/-- For healthy-one observations, the actual query stream decides physical detection. -/
theorem zero_stream_physical_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (positive : 0 < b) (bridge : Physical.Bridge n)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = true)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size) :
    (∃ position : Fin (zeroQueries width graph rows rawRoots rowsMatch b bridge.target).length,
      Satisfiable (constructorFormula heap layout (empty (n + graph.nodeCount))
        (empty_coherent _) (zeroQueries width graph rows rawRoots rowsMatch b bridge.target)[position]
        n (Nat.le_add_right _ _))) ↔
      Physical.BridgeDetectable (b := b) bridge true
        (fun position : Fin graph.roots.length => fun assignment =>
          graph.eval assignment (graph.roots.get position)) := by
  rw [zero_stream_constructor_iff graph guarded,
    Physical.bridge_detectable_iff_exists_output bridge positive]
  constructor
  · rintro ⟨K, admissible, position, zero⟩
    refine ⟨rfl, K, admissible, position, ?_⟩
    rw [zero, healthy position]
    decide
  · rintro ⟨_, K, admissible, position, different⟩
    refine ⟨K, admissible, position, ?_⟩
    cases value : graph.eval (assignmentOfSet K) (graph.roots.get position) with
    | false => rfl
    | true => exact False.elim (different (value.trans (healthy position).symm))

/-- The selected stream's exact returned bits realize detection among all declared outputs. -/
theorem zero_stream_output_physical (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (rawRoots : List Nat) (rowsMatch : RowsMatch graph rows)
    (b : Nat) (positive : 0 < b) (bridge : Physical.Bridge n)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = true)
    (heap : Array (Word width)) (layout : Layout (n + graph.nodeCount) heap.size)
    (observed : List (Word width))
    (position : Fin (zeroQueries width graph rows rawRoots rowsMatch b bridge.target).length)
    (witness : QueryChannelWitness heap layout
      (zeroQueries width graph rows rawRoots rowsMatch b bridge.target)[position]
      n (Nat.le_add_right _ _) observed) :
    ∃ original : Fin graph.roots.length, ∃ K : Finset (Channel n),
      Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true
        (fun root : Fin graph.roots.length => fun assignment =>
          graph.eval assignment (graph.roots.get root))
        (Physical.realizeBridge bridge positive K) true ∧
      graph.eval (assignmentOfSet K) (graph.roots.get original) = false ∧
      ∃ previous : List (Word width),
        observed = (List.finRange n).map (fun channel =>
          ForestZeroChannelEmit.bitWord width (assignmentOfSet K channel)) ++
          word width 1 :: previous := by
  obtain ⟨original, K, admissible, zero, previous, emitted⟩ := zero_stream_output_witness
    graph guarded rows rawRoots rowsMatch b bridge.target heap layout observed position witness
  refine ⟨original, K, admissible, ?_, zero, previous, emitted⟩
  apply (Physical.realizeBridge_detects_iff bridge positive K admissible _).mpr
  refine ⟨original, ?_⟩
  change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get original) ≠
    graph.eval (assignmentOfSet K) (graph.roots.get original)
  rw [healthy original, zero]
  decide

end Controller.Cost.ForestZeroOutputImage
