module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.MonotoneOutputSearch

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A terminating monotone detector using one evaluation per extremal set.
Shared singleton/full tables are constructed before the output traversal;
the final witness is an actual emitted channel vector. -/
namespace Controller.Extensions.MonotoneDetector
open Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun Controller.Cost.UniformDAGSource Controller.Cost.RawTransferLoops
open Controller.Extensions.LiteralSourceConstruction (Width initial source_size_bound)
open Controller.Extensions.LiteralDetector (sourceHeap Output)
open Controller.Extensions.MonotoneTableConstruction (matrix matrix_length)

variable {n width : Nat}

def constructionSize (graph : DAG n) : Nat := 162 * n + 143 + 2 * (n + 1) * graph.nodeCount
def found (graph : DAG n) (b : Nat) : Nat := constructionSize graph + graph.roots.length * MonotoneOutputSearch.stride b n + 2

def code (graph : DAG n) (width b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat) :
    List (Instruction width 8) :=
  (MonotoneTableConstruction.code graph width rows roots 0).toList ++
    (MonotoneOutputSearch.code b target graph.nodeCount (sourceHeap width n rows roots).size
      (found graph b) (found graph b + 1) graph.roots.length (constructionSize graph)
      (SharedDetectorPrepared.rootBase graph) ++ [.halt, .halt])

def program (graph : DAG n) (width b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat) :
    Program width 8 := (code graph width b target rows roots).toArray

@[simp] theorem code_length (graph : DAG n) (b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat) :
    (code graph width b target rows roots).length = found graph b + 2 := by
  simp only [code, List.length_append, Array.length_toList, MonotoneTableConstruction.code_size,
    MonotoneOutputSearch.code_length, List.length_cons, List.length_nil, found, constructionSize]
  omega

theorem matrix_stored (graph : DAG n) (heap : Array (Word width)) :
    MonotoneRoot.MatrixAt (heap ++ (matrix graph width).toArray) heap.size graph := by
  intro i h
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_toArray]

set_option maxHeartbeats 1200000 in
/-- Capacity, placement, termination and total resident storage for the
concrete source-packet program, with arbitrary stack and output frames. -/
theorem from_source (graph : DAG n) (b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (caller output : List (Word (Width graph))) :
    ∃ final ticks peak,
      Execution (program graph (Width graph) b target rows roots)
        (initial n (Width graph) rows roots caller output) final ticks peak ∧
      ticks ≤ 192 * ((n + 1) * (graph.countedSize + 1)) ∧
      programWords (program graph (Width graph) b target rows roots) + peak ≤
        2048 * ((n + 1) * (graph.countedSize + 1)) + caller.length + output.length ∧
      final.halted = true ∧ final.stack = caller ∧
      Output output final.output (MonotoneDecision.search graph b target) ∧
      final.heap = sourceHeap (Width graph) n rows roots ++ (matrix graph (Width graph)).toArray := by
  let start := initial n (Width graph) rows roots caller output
  let resident := program graph (Width graph) b target rows roots
  let base := start.heap.size
  let total := (n + 1) * (graph.countedSize + 1)
  have positive : 0 < total := Nat.mul_pos (by omega) (by omega)
  have size := graph.countedSize_eq
  have baseline : graph.countedSize + 1 ≤ total := le_mul_of_one_le_left (Nat.zero_le _) (by omega)
  have channels : n ≤ total := by omega
  have nodes : graph.nodeCount ≤ total := by omega
  have capacity := SharedMachineCapacity.capacity 0 total 0
  simp only [Nat.zero_add, Nat.add_zero] at capacity
  change 131072 * (total + 1) < 2 ^ Width graph at capacity
  have source : base ≤ 7 * total := by
    have bound := source_size_bound graph rows roots matched rootMatches (width := Width graph)
    change base ≤ 7 * (graph.countedSize + 1) at bound
    omega
  have matrixBound : (matrix graph (Width graph)).length ≤ total := by
    rw [matrix_length]
    exact Nat.mul_le_mul_left (n + 1) (by omega)
  have codeBound : constructionSize graph ≤ 307 * total := by
    have product : 2 * (n + 1) * graph.nodeCount = 2 * (matrix graph (Width graph)).length := by
      rw [matrix_length]; ring
    unfold constructionSize
    rw [product]; omega
  have traversal : graph.roots.length * MonotoneOutputSearch.stride b n ≤ 57 * total := by
    have bound := MonotoneOutputSearch.stride_bound b n
    have mult := Nat.mul_le_mul (show graph.roots.length ≤ graph.countedSize + 1 by omega)
      (show MonotoneOutputSearch.stride b n ≤ 57 * (n + 1) by omega)
    convert mult using 1 <;> dsimp [total] <;> ring
  have traversaltime : graph.roots.length * (22 * n + 22) + 2 ≤ 22 * total + 2 := by
    have mult := Nat.mul_le_mul_right (22 * n + 22) (show graph.roots.length ≤ graph.countedSize + 1 by omega)
    have eq : (graph.countedSize + 1) * (22 * n + 22) = 22 * total := by dsimp [total]; ring
    rw [eq] at mult; omega
  have physical : SharedRootRead.BlockAt resident 0 (code graph (Width graph) b target rows roots) := by
    intro i h
    simp only [resident, program, Nat.zero_add, List.getElem?_toArray]
  have constructorAt := SharedDetectorAssembly.block_left resident 0 _ _ physical
  have restAt := SharedDetectorAssembly.block_right resident 0 _ _ physical
  simp only [Array.length_toList, MonotoneTableConstruction.code_size, Nat.zero_add] at restAt
  have searchAt := SharedDetectorAssembly.block_left resident (constructionSize graph) _ _ restAt
  have haltAt := SharedDetectorAssembly.block_right resident (constructionSize graph) _ _ restAt
  simp only [MonotoneOutputSearch.code_length] at haltAt
  have constructor : CodeAt resident 0 (MonotoneTableConstruction.code graph (Width graph) rows roots 0) := by
    intro i
    simpa only [Array.getElem?_toList] using constructorAt i.val (by simpa using i.isLt)
  obtain ⟨built, bt, bp, buildTrace, buildTime, buildSpace, buildHeap, buildStack, buildOutput, buildPC, buildRun⟩ :=
    MonotoneTableConstruction.execution resident start graph rows roots matched heads rootMatches 0
      (by omega) (by simpa only [Nat.zero_add, constructionSize] using (show constructionSize graph < 2 ^ Width graph by omega)) (by omega) rfl rfl rfl constructor
  have builtSize : built.heap.size = base + (matrix graph (Width graph)).length := by
    simp only [buildHeap, Array.size_append, List.size_toArray]; rfl
  have builtLive : built.liveWords = start.liveWords + (matrix graph (Width graph)).length := by
    simp only [State.liveWords, builtSize, buildStack, buildOutput, base]; omega
  have stored : MonotoneRoot.MatrixAt built.heap base graph := by rw [buildHeap]; exact matrix_stored graph _
  have rootCells : LiteralOutputSearch.Stored built.heap (SharedDetectorPrepared.rootBase graph) graph.roots := by
    rw [buildHeap]
    exact LiteralDetector.roots_stored graph rows roots matched rootMatches _
  obtain ⟨queried, qt, qp, queryTrace, queryTime, querySpace, queryHeap, queryStack, queryRun, result⟩ :=
    MonotoneOutputSearch.execution resident graph b target base (found graph b) (found graph b + 1) graph.roots
      (constructionSize graph) (SharedDetectorPrepared.rootBase graph) built
      (by simpa only [Nat.zero_add, constructionSize] using buildPC) buildRun
      (by rw [← matrix_length (width := Width graph) graph]; omega) (by rw [builtSize]; omega) stored rootCells searchAt
  have qpBound : qp ≤ start.liveWords + 2 * total := by rw [builtLive] at querySpace; omega
  have bpBound : bp ≤ start.liveWords + 8 * total := buildSpace
  have haltRoom : found graph b + 2 < 2 ^ Width graph := by unfold found; omega
  have outcome : ∃ final, Execution resident queried final 1 queried.liveWords ∧ final.halted = true ∧
      final.heap = queried.heap ∧ final.stack = queried.stack ∧
      Output output final.output (MonotoneDecision.search graph b target) := by
    change LiteralOutputSearch.Result (found graph b + 1) (found graph b) built queried
      (MonotoneDecision.search graph b target) at result
    cases answer : MonotoneDecision.search graph b target with
    | none =>
      have res : queried.pc = word (Width graph) (found graph b + 1) ∧ queried.output = built.output := by
        simpa only [answer, LiteralOutputSearch.Result] using result
      obtain ⟨final, tr, run, heap, stack, out⟩ := EnumerationSteps.halt_execution resident queried
        (found graph b + 1) res.1 queryRun (by omega)
        (by simpa only [found, Nat.add_assoc, List.getElem?_cons_succ, List.getElem?_cons_zero] using haltAt 1 (by simp))
      exact ⟨final, tr, run, heap, stack, by simpa only [Output, start, initial] using out.trans (res.2.trans buildOutput)⟩
    | some K =>
      have res : queried.pc = word (Width graph) (found graph b) ∧
          queried.output = LiteralWitnessReturn.words (Width graph) K ++ built.output := by
        simpa only [answer, LiteralOutputSearch.Result] using result
      obtain ⟨final, tr, run, heap, stack, out⟩ := EnumerationSteps.halt_execution resident queried
        (found graph b) res.1 queryRun (by omega)
        (by simpa only [found, Nat.add_zero, Nat.add_assoc, List.getElem?_cons_zero] using haltAt 0 (by simp))
      exact ⟨final, tr, run, heap, stack, by simp only [Output, out, res.2, buildOutput, start, initial]⟩
  obtain ⟨final, haltTrace, halted, finalHeap, finalStack, finalOutput⟩ := outcome
  have joined := (buildTrace.append queryTrace).append haltTrace
  have endBound := queryTrace.final_storage_le
  have live : start.liveWords ≤ 9 + 7 * total + caller.length + output.length := by
    dsimp only [base, State.liveWords, start, initial] at source ⊢; omega
  have programBound : programWords resident ≤ 4 * (364 * total + 4) := by
    simp only [resident, programWords, program, List.size_toArray, code_length, found]
    omega
  refine ⟨final, bt + qt + 1, max (max bp qp) queried.liveWords, joined, ?_, ?_, halted,
    finalStack.trans (queryStack.trans buildStack), finalOutput, finalHeap.trans (queryHeap.trans buildHeap)⟩
  · have time : bt ≤ 128 * total := buildTime
    omega
  · have peaks : max (max bp qp) queried.liveWords ≤ start.liveWords + 8 * total := by omega
    change programWords resident + max (max bp qp) queried.liveWords ≤ 2048 * total + caller.length + output.length
    omega

/-- Correct detection for every DAG without negative guards, including shared
live-AND/OR nodes and repeated output occurrences. -/
theorem from_source_correct (graph : DAG n) (noGuards : GateBasis.NoNegativeGuards graph)
    (b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (caller output : List (Word (Width graph))) :
    ∃ final ticks peak,
      Execution (program graph (Width graph) b target rows roots)
        (initial n (Width graph) rows roots caller output) final ticks peak ∧
      ticks ≤ 192 * ((n + 1) * (graph.countedSize + 1)) ∧
      programWords (program graph (Width graph) b target rows roots) + peak ≤
        2048 * ((n + 1) * (graph.countedSize + 1)) + caller.length + output.length ∧
      final.halted = true ∧ final.stack = caller ∧
      ((final.output = output ∧ ¬∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
          graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) ∨
        ∃ K, Admissible b target K ∧
          (∃ root ∈ graph.roots, graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) ∧
          final.output = LiteralWitnessReturn.words (Width graph) K ++ output) := by
  obtain ⟨final, ticks, peak, trace, time, space, halted, stack, out, _⟩ :=
    from_source graph b target rows roots matched heads rootMatches caller output
  refine ⟨final, ticks, peak, trace, time, space, halted, stack, ?_⟩
  cases answer : MonotoneDecision.search graph b target with
  | none => exact Or.inl ⟨by simpa only [answer, Output] using out,
      (MonotoneDecision.search_none_iff graph noGuards b target).mp answer⟩
  | some K =>
    obtain ⟨eligible, changes⟩ := MonotoneDecision.search_some graph b target K answer
    exact Or.inr ⟨K, eligible, changes, by simpa only [answer, Output] using out⟩

end Controller.Extensions.MonotoneDetector
