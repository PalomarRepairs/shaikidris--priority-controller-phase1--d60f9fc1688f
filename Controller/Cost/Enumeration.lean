module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverStream

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Complete resident enumeration of detecting eligible sets and their canonical
native realizations. Delay includes initial search and final exhaustion; output
serialization is charged separately, and working storage excludes the external
output stream at every intermediate state. -/
namespace Controller.Cost.Enumeration
open Controller.Decoder Controller.Native Controller.Cost.GateProgram
open Controller.Cost.EnumerationStreamEmit Controller.Cost.EnumerationWorkingTrace

/-- Word width sufficient for the source, resident program and oracle scratch. -/
abbrev Width (parameters : Parameters) (graph : DAG parameters.channels) := EnumerationDriverCapacity.Width parameters graph
/-- One immutable instruction array for every prefix of the supplied instance. -/
abbrev program (parameters : Parameters) (graph : DAG parameters.channels) (rows : List ForestIndexedOperands.Row) (roots : List Nat) :=
  EnumerationDriverCapacity.program parameters graph rows roots

/-- Loaded canonical packet, empty stack and output, and the startup entry. -/
def initial (parameters : Parameters) (graph : DAG parameters.channels) (rows : List ForestIndexedOperands.Row) (roots : List Nat) :
    State (Width parameters graph) 8 where
  reg := fun _ => word (Width parameters graph) 0
  heap := EnumerationPrefixOracle.packet parameters (Width parameters graph) rows roots
  stack := []
  output := []
  pc := word (Width parameters graph) 0
  halted := false

/-- Ghost order specification; the machine stores one prefix, not this list. -/
def results (parameters : Parameters) (graph : DAG parameters.channels) :=
  Decoder.Enumeration.trace graph parameters.buses parameters.bridge.target parameters.drive (2 ^ parameters.channels + 1) .initial

theorem results_exact (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded) :
    (results parameters graph).Nodup ∧ (results parameters graph).Pairwise Decoder.Enumeration.Before ∧
    ∀ K, K ∈ results parameters graph ↔ Decoder.Enumeration.Detecting graph parameters.buses parameters.bridge.target parameters.drive K := by
  refine ⟨Decoder.Enumeration.trace_nodup graph guarded parameters.buses parameters.bridge.target parameters.drive _ _,
    Decoder.Enumeration.trace_lexicographic graph guarded parameters.buses parameters.bridge.target parameters.drive _ _, ?_⟩
  exact Decoder.Enumeration.trace_complete graph guarded parameters.buses parameters.bridge.target parameters.drive _ _
    ((Decoder.Enumeration.remainingSets_card_le graph parameters.buses parameters.bridge.target parameters.drive _).trans (by omega))

theorem canonical_result_detects (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (K : Finset (Fin parameters.channels)) (member : K ∈ results parameters graph) :
    Controller.Physical.BridgeInputDetects parameters.bridge true (Decoder.Enumeration.observations graph)
      (Controller.Physical.realizeBridge parameters.bridge parameters.positiveBuses K) true :=
  Decoder.Enumeration.canonical_realization_detects graph parameters.bridge parameters.buses parameters.positiveBuses parameters.drive K
    ((results_exact parameters graph guarded).2.2 K |>.mp member)

set_option maxRecDepth 10000 in
private theorem polynomial_delay (n q G : Nat) (positive : 1 ≤ n) (graphSize : n ≤ G) :
    (2 * n + 1) * (24 * n + 16 + (n + q + 1) * (8000 * (G + 1)) + 100) ≤ 100000 * n * (n + q) * G := by
  have product : n ≤ (n + q) * G :=
    (by omega : n ≤ n + q).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n + q) (show 1 ≤ G by omega))
  have core : (n + q + 1) * (G + 1) ≤ 4 * ((n + q) * G) := by
    calc
      _ ≤ (2 * (n + q)) * (2 * G) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have query : 24 * n + 116 + 8000 * ((n + q + 1) * (G + 1)) ≤ 32140 * ((n + q) * G) := by
    have scaled := Nat.mul_le_mul_left 8000 core
    have overhead : 24 * n + 116 ≤ 140 * ((n + q) * G) := by
      clear * - positive product
      omega
    calc
      _ ≤ 140 * ((n + q) * G) + 8000 * (4 * ((n + q) * G)) := Nat.add_le_add overhead scaled
      _ = _ := by ring
  calc
    _ = (2 * n + 1) * (24 * n + 116 + 8000 * ((n + q + 1) * (G + 1))) := by ring
    _ ≤ (3 * n) * (32140 * ((n + q) * G)) := Nat.mul_le_mul (by omega) query
    _ = 96420 * (n * ((n + q) * G)) := by ring
    _ ≤ 100000 * (n * ((n + q) * G)) := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring

theorem delay_bound (parameters : Parameters) (graph : DAG parameters.channels) :
    EnumerationDriverNext.delay parameters graph ≤ 100000 * parameters.channels *
      (parameters.channels + graph.roots.length) * graph.countedSize := by
  have positive : 1 ≤ parameters.channels := by have := parameters.bridge.target.isLt; omega
  have size := graph.countedSize_eq
  exact polynomial_delay parameters.channels graph.roots.length graph.countedSize positive (by omega)

theorem program_words_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (rootMatches : ForestIndexedOperands.RootsMatch graph roots) :
    programWords (program parameters graph rows roots) ≤
      4 * (8 * parameters.channels + 129 + 6 * EnumerationCanonicalEmit.Coordinates parameters + 610 * (graph.countedSize + 1) + 1609) := by
  have bound := EnumerationDriverCode.code_length_bound parameters graph (Width parameters graph) 0 rows roots rootMatches
  simp only [programWords, program, EnumerationDriverCapacity.program, EnumerationDriverLayout.program, List.size_toArray]
  simpa only [Nat.add_assoc] using Nat.mul_le_mul_left 4 bound

theorem representable (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : ForestIndexedOperands.RootsMatch graph roots) :
    Representable (program parameters graph rows roots) (initial parameters graph rows roots) := by
  have context := EnumerationDriverCapacity.context parameters graph guarded rows roots matched heads rootMatches
  have retainedFits := EnumerationDriverCapacity.retained_fits parameters graph
  have large : 8 ≤ EnumerationDriverCapacity.retained parameters graph := by
    dsimp [EnumerationDriverCapacity.retained]
    omega
  refine ⟨large.trans (Nat.le_of_lt retainedFits), ?_, ?_⟩
  · simpa only [program, EnumerationDriverCapacity.program, EnumerationDriverLayout.program, List.size_toArray, Nat.zero_add]
      using Nat.le_of_lt context.room
  · change (EnumerationPrefixOracle.packet parameters (Width parameters graph) rows roots).size ≤ 2 ^ Width parameters graph
    exact (Nat.le_add_right _ _).trans (Nat.le_of_lt context.heapFits)

set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : ForestIndexedOperands.RootsMatch graph roots) :
    ∃ final ticks peak, WorkingExecution (program parameters graph rows roots) (initial parameters graph rows roots) final ticks peak ∧
      ticks ≤ (2 ^ parameters.channels + 1) * EnumerationDriverNext.delay parameters graph +
        (results parameters graph).length * EnumerationDriverStream.emitBudget parameters ∧
      peak ≤ 258 * (graph.countedSize + 1) ∧ final.halted = true ∧
      final.output = (EnumerationDriverStream.words parameters (Width parameters graph) (results parameters graph)).reverse ∧
      ∃ livePeak, Execution (program parameters graph rows roots) (initial parameters graph rows roots) final ticks livePeak := by
  have context := EnumerationDriverCapacity.context parameters graph guarded rows roots matched heads rootMatches
  obtain ⟨final, ticks, peak, trace, time, space, output, runtime⟩ :=
    EnumerationDriverStream.execution parameters graph (EnumerationDriverCapacity.retained parameters graph) 0 rows roots
      (program parameters graph rows roots) context (2 ^ parameters.channels + 1) .initial (initial parameters graph rows roots)
      ⟨rfl, rfl, rfl, rfl⟩
  have finish := Decoder.Enumeration.enumeration_terminates graph guarded parameters.buses parameters.bridge.target parameters.drive
  rw [finish] at runtime
  exact ⟨final, ticks, peak, trace, time, space, runtime.1, by simpa only [results, initial, List.append_nil] using output, trace.to_execution⟩

set_option maxHeartbeats 2000000 in
theorem iterator_delay (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (logical : Decoder.Enumeration.State parameters.channels) (state : State (Width parameters graph) 8)
    (runtime : EnumerationDriverNext.Runtime parameters graph (EnumerationPrefixOracle.packet parameters (Width parameters graph) rows roots)
      0 (EnumerationDriverCode.labels parameters graph (Width parameters graph) 0).seek logical state) :
    ∃ final ticks peak, WorkingExecution (program parameters graph rows roots) state final ticks peak ∧
      ticks ≤ 100000 * parameters.channels * (parameters.channels + graph.roots.length) * graph.countedSize ∧
      peak ≤ 258 * (graph.countedSize + 1) ∧ final.output = state.output ∧
      EnumerationDriverStart.Endpoint parameters (EnumerationPrefixOracle.packet parameters (Width parameters graph) rows roots)
        (EnumerationDriverCode.labels parameters graph (Width parameters graph) 0).emit
        (Decoder.Enumeration.next graph parameters.buses parameters.bridge.target parameters.drive logical).output final := by
  obtain ⟨final, ticks, peak, trace, time, space, output, endpoint⟩ :=
    EnumerationDriverNext.execution parameters graph (EnumerationDriverCapacity.retained parameters graph) 0 rows roots
      (program parameters graph rows roots) (EnumerationDriverCapacity.context parameters graph guarded rows roots matched heads rootMatches) logical state runtime
  exact ⟨final, ticks, peak, trace, time.trans (delay_bound parameters graph), space, output, endpoint⟩

end Controller.Cost.Enumeration
