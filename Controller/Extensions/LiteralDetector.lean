module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralOutputSearch
public import Controller.Cost.SharedDetectorPrepared

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A terminating no-OR detector from the original typed source packet.
The one execution constructs the literal matrix, reads all declared outputs,
and emits the first detecting channel vector. Code storage is included in
the O(nG) space bound. -/
namespace Controller.Extensions.LiteralDetector
open Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun Controller.Cost.UniformDAGSource Controller.Cost.GateProgram
open Controller.Cost.RawTransferLoops
open Controller.Extensions.LiteralSourceConstruction

variable {n width : Nat}

def sourceHeap (width n : Nat) (rows : List Row) (roots : List Nat) : Array (Word width) :=
  channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false)

def found (graph : DAG n) (b : Nat) (target : Channel n) (base : Nat) : Nat :=
  constructionSize graph + graph.roots.length * LiteralOutputSearch.stride b target graph.nodeCount base + 2

def code (graph : DAG n) (width b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat) :
    List (Instruction width 8) :=
  let base := (sourceHeap width n rows roots).size
  (constructionCode graph width rows roots 0 base).toList ++
    (LiteralOutputSearch.code b target graph.nodeCount base (found graph b target base) (found graph b target base + 1)
      graph.roots.length (constructionSize graph) (SharedDetectorPrepared.rootBase graph) ++ [.halt, .halt])

def program (graph : DAG n) (width b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat) :
    Program width 8 := (code graph width b target rows roots).toArray

@[simp] theorem code_length (graph : DAG n) (b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat) :
    (code graph width b target rows roots).length = found graph b target (sourceHeap width n rows roots).size + 2 := by
  simp only [code, List.length_append, Array.length_toList, constructionCode_size,
    LiteralOutputSearch.code_length, List.length_cons, List.length_nil, found]
  omega

def Output (before after : List (Word width)) : Option (Finset (Channel n)) → Prop
  | none => after = before
  | some K => after = LiteralWitnessReturn.words width K ++ before

/-- Source cells survive the matrix and flag allocations. -/
theorem roots_stored (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (suffix : Array (Word width)) :
    LiteralOutputSearch.Stored (sourceHeap width n rows roots ++ suffix)
      (SharedDetectorPrepared.rootBase graph) graph.roots := by
  intro i h
  have cell := SharedDetectorPrepared.packet_roots (width := width) graph rows roots matched rootMatches
    (fun _ => false) i (by simpa only [SharedDetectorPrepared.rootWords, List.length_map] using h)
  have bound := (Array.getElem?_eq_some_iff.mp cell).1
  rw [sourceHeap, Array.getElem?_append_left bound]
  simpa only [SharedDetectorPrepared.rootWords, List.getElem_map] using cell

theorem matrix_stored (graph : DAG n) (heap suffix : Array (Word width)) :
    LiteralRoot.MatrixAt (heap ++ (matrix graph width).toArray ++ suffix) heap.size graph := by
  intro i h
  rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_toArray]

set_option maxHeartbeats 1600000 in
/-- All placement and word-capacity premises are discharged for this program.
The stack and old output form arbitrary caller frames. -/
theorem from_source (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (caller output : List (Word (Width graph))) :
    ∃ final ticks peak,
      Execution (program graph (Width graph) b target rows roots)
        (initial n (Width graph) rows roots caller output) final ticks peak ∧
      ticks ≤ 640 * ((n + 1) * (graph.countedSize + 1)) ∧
      programWords (program graph (Width graph) b target rows roots) + peak ≤
        4096 * ((n + 1) * (graph.countedSize + 1)) + caller.length + output.length ∧
      final.halted = true ∧ final.stack = caller ∧
      Output output final.output (LiteralWitness.search graph b target) ∧
      final.heap = sourceHeap (Width graph) n rows roots ++ (matrix graph (Width graph)).toArray ++
        (List.ofFn (fun root : Fin graph.nodeCount => boolWord (Width graph) (LiteralMachine.summary graph root).invalid)).toArray := by
  let start := initial n (Width graph) rows roots caller output
  let resident := program graph (Width graph) b target rows roots
  let base := start.heap.size
  let total := (n + 1) * (graph.countedSize + 1)
  have positive : 0 < total := Nat.mul_pos (by omega) (by omega)
  have size := graph.countedSize_eq
  have baseline : graph.countedSize + 1 ≤ total := by
    exact le_mul_of_one_le_left (Nat.zero_le _) (by omega)
  have channels : n ≤ total := by omega
  have nodes : graph.nodeCount ≤ total := by omega
  have capacity := SharedMachineCapacity.capacity 0 total 0
  simp only [Nat.zero_add, Nat.add_zero] at capacity
  change 131072 * (total + 1) < 2 ^ Width graph at capacity
  have source : base ≤ 7 * total := by
    have bound := source_size_bound graph rows roots matched rootMatches (width := Width graph)
    change base ≤ 7 * (graph.countedSize + 1) at bound
    omega
  have matrixBound : (matrix graph (Width graph)).length ≤ 4 * total := by
    rw [matrix_length]
    have mult := Nat.mul_le_mul (show 2 * n + 1 ≤ 4 * (n + 1) by omega)
      (show graph.nodeCount ≤ graph.countedSize + 1 by omega)
    simpa only [Nat.mul_assoc] using mult
  have codeBound : constructionSize graph ≤ 512 * total := constructionSize_bound graph
  have traversal : graph.roots.length * LiteralOutputSearch.stride b target graph.nodeCount base ≤ 172 * total := by
    have bound := LiteralOutputSearch.stride_bound b target graph.nodeCount base
    have mult := Nat.mul_le_mul (show graph.roots.length ≤ graph.countedSize + 1 by omega)
      (show LiteralOutputSearch.stride b target graph.nodeCount base ≤ 172 * (n + 1) by omega)
    convert mult using 1 <;> dsimp [total] <;> ring
  have traversaltime : graph.roots.length * (73 * n + 70) + 2 ≤ 143 * total + 2 := by
    have mult := Nat.mul_le_mul (show graph.roots.length ≤ graph.countedSize + 1 by omega)
      (show 73 * n + 70 ≤ 143 * (n + 1) by omega)
    have eq : (graph.countedSize + 1) * (143 * (n + 1)) = 143 * total := by dsimp [total]; ring
    rw [eq] at mult; omega
  have physical : SharedRootRead.BlockAt resident 0 (code graph (Width graph) b target rows roots) := by
    intro i h
    simp only [resident, program, Nat.zero_add, List.getElem?_toArray]
  have constructorAt := SharedDetectorAssembly.block_left resident 0 _ _ physical
  have restAt := SharedDetectorAssembly.block_right resident 0 _ _ physical
  simp only [Array.length_toList, constructionCode_size, Nat.zero_add] at restAt
  have searchAt := SharedDetectorAssembly.block_left resident (constructionSize graph) _ _ restAt
  have haltAt := SharedDetectorAssembly.block_right resident (constructionSize graph) _ _ restAt
  simp only [LiteralOutputSearch.code_length] at haltAt
  have constructor : CodeAt resident 0 (constructionCode graph (Width graph) rows roots 0 base) := by
    intro i
    simpa only [Array.getElem?_toList, sourceHeap, base, start, initial] using constructorAt i.val (by simpa using i.isLt)
  obtain ⟨built, bt, bp, buildTrace, buildTime, buildSpace, buildHeap, buildStack, buildOutput, buildPC, buildRun⟩ :=
    construction_execution resident start graph noOr rows roots matched heads rootMatches 0 base
      (by omega) constructor (by omega) rfl rfl rfl rfl (by omega)
  have builtSize : built.heap.size = base + (matrix graph (Width graph)).length + graph.nodeCount := by
    simp only [buildHeap, Array.size_append, List.size_toArray, List.length_ofFn]; rfl
  have builtLive : built.liveWords = start.liveWords + (matrix graph (Width graph)).length + graph.nodeCount := by
    simp only [State.liveWords, builtSize, buildStack, buildOutput, base]; omega
  have stored : LiteralRoot.MatrixAt built.heap base graph := by rw [buildHeap]; exact matrix_stored graph _ _
  have rootCells : LiteralOutputSearch.Stored built.heap (SharedDetectorPrepared.rootBase graph) graph.roots := by
    rw [buildHeap, Array.append_assoc]
    exact roots_stored graph rows roots matched rootMatches _
  obtain ⟨queried, qt, qp, queryTrace, queryTime, querySpace, queryHeap, queryStack, queryRun, result⟩ :=
    LiteralOutputSearch.execution resident graph noOr b target base (found graph b target base)
      (found graph b target base + 1) graph.roots (constructionSize graph) (SharedDetectorPrepared.rootBase graph)
      built (by simpa only [Nat.zero_add] using buildPC) buildRun
      (by rw [← matrix_length (width := Width graph) graph]; omega) (by rw [builtSize]; omega) stored rootCells searchAt
  have qpBound : qp ≤ start.liveWords + 6 * total := by rw [builtLive] at querySpace; omega
  have bpBound : bp ≤ start.liveWords + 16 * total := by simpa only [Nat.mul_assoc] using buildSpace
  have haltRoom : found graph b target base + 2 < 2 ^ Width graph := by unfold found; omega
  have outcome : ∃ final, Execution resident queried final 1 queried.liveWords ∧ final.halted = true ∧
      final.heap = queried.heap ∧ final.stack = queried.stack ∧
      Output output final.output (LiteralWitness.search graph b target) := by
    change LiteralOutputSearch.Result (found graph b target base + 1) (found graph b target base)
      built queried (LiteralWitness.search graph b target) at result
    cases answer : LiteralWitness.search graph b target with
    | none =>
      have res : queried.pc = word (Width graph) (found graph b target base + 1) ∧ queried.output = built.output := by
        simpa only [answer, LiteralOutputSearch.Result] using result
      obtain ⟨final, tr, run, heap, stack, out⟩ := EnumerationSteps.halt_execution resident queried
        (found graph b target base + 1) res.1 queryRun (by omega)
        (by simpa only [found, Nat.add_assoc, List.getElem?_cons_succ, List.getElem?_cons_zero,
          sourceHeap, base, start, initial] using haltAt 1 (by simp))
      exact ⟨final, tr, run, heap, stack, by simpa only [Output, start, initial] using out.trans (res.2.trans buildOutput)⟩
    | some K =>
      have res : queried.pc = word (Width graph) (found graph b target base) ∧
          queried.output = LiteralWitnessReturn.words (Width graph) K ++ built.output := by
        simpa only [answer, LiteralOutputSearch.Result] using result
      obtain ⟨final, tr, run, heap, stack, out⟩ := EnumerationSteps.halt_execution resident queried
        (found graph b target base) res.1 queryRun (by omega)
        (by simpa only [found, Nat.add_zero, Nat.add_assoc, List.getElem?_cons_zero,
          sourceHeap, base, start, initial] using haltAt 0 (by simp))
      exact ⟨final, tr, run, heap, stack, by simp only [Output, out, res.2, buildOutput, start, initial]⟩
  obtain ⟨final, haltTrace, halted, finalHeap, finalStack, finalOutput⟩ := outcome
  have joined := (buildTrace.append queryTrace).append haltTrace
  have endBound := queryTrace.final_storage_le
  have live : start.liveWords ≤ 9 + 7 * total + caller.length + output.length := by
    dsimp only [base, State.liveWords, start, initial] at source ⊢
    omega
  have programBound : programWords resident ≤ 4 * (684 * total + 4) := by
    simp only [resident, programWords, program, List.size_toArray, code_length, found]
    change 4 * (constructionSize graph + graph.roots.length * LiteralOutputSearch.stride b target graph.nodeCount base + 2 + 2) ≤ _
    omega
  refine ⟨final, bt + qt + 1, max (max bp qp) queried.liveWords, joined, ?_, ?_, halted,
    finalStack.trans (queryStack.trans buildStack), finalOutput, finalHeap.trans (queryHeap.trans buildHeap)⟩
  · have time : bt ≤ 480 * total := by simpa only [Nat.mul_assoc] using buildTime
    omega
  · have peaks : max (max bp qp) queried.liveWords ≤ start.liveWords + 16 * total := by omega
    change programWords resident + max (max bp qp) queried.liveWords ≤ 4096 * total + caller.length + output.length
    omega

/-- The halted program either preserves the old output and certifies absence,
or prepends an admissible vector that changes a declared observation. -/
theorem from_source_correct (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (b : Nat) (target : Channel n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (caller output : List (Word (Width graph))) :
    ∃ final ticks peak,
      Execution (program graph (Width graph) b target rows roots)
        (initial n (Width graph) rows roots caller output) final ticks peak ∧
      ticks ≤ 640 * ((n + 1) * (graph.countedSize + 1)) ∧
      programWords (program graph (Width graph) b target rows roots) + peak ≤
        4096 * ((n + 1) * (graph.countedSize + 1)) + caller.length + output.length ∧
      final.halted = true ∧ final.stack = caller ∧
      ((final.output = output ∧ ¬∃ root ∈ graph.roots, ∃ K, Admissible b target K ∧
          graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) ∨
        ∃ K, Admissible b target K ∧
          (∃ root ∈ graph.roots, graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) ∧
          final.output = LiteralWitnessReturn.words (Width graph) K ++ output) := by
  obtain ⟨final, ticks, peak, trace, time, space, halted, stack, out, _⟩ :=
    from_source graph noOr b target rows roots matched heads rootMatches caller output
  refine ⟨final, ticks, peak, trace, time, space, halted, stack, ?_⟩
  cases answer : LiteralWitness.search graph b target with
  | none =>
    exact Or.inl ⟨by simpa only [answer, Output] using out,
      (LiteralWitness.search_none_iff graph noOr b target).mp answer⟩
  | some K =>
    obtain ⟨eligible, changes⟩ := LiteralWitness.search_some graph noOr b target K answer
    exact Or.inr ⟨K, eligible, changes, by simpa only [answer, Output] using out⟩

end Controller.Extensions.LiteralDetector
