module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BasisNativeFinish

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Monotone detection and native model emission in one fetched execution,
starting with the original shared graph packet. -/
namespace Controller.Extensions.MonotoneNativeDetector
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGRun Controller.Cost.UniformDAGSource
open Controller.Cost.RawTransferLoops
open Controller.Extensions.LiteralSourceConstruction (initial source_size_bound)
open Controller.Extensions.LiteralDetector (sourceHeap)
open Controller.Extensions.MonotoneTableConstruction (matrix matrix_length)
open Controller.Extensions.MonotoneDetector (constructionSize)

def Width (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  SharedMachineCapacity.wordWidth 0 ((parameters.channels + 1) * (graph.countedSize + 1)) (selectedSize parameters).total

def found (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  MonotoneDetector.found graph parameters.buses

def nativeBase (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) : Nat :=
  (sourceHeap width n rows roots).size + (matrix graph width).length

def absent (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) : Nat :=
  found parameters graph + (BasisNativeFinish.code parameters width (nativeBase graph width rows roots)
    (found parameters graph)).length

def code (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) : List (Instruction width 8) :=
  (MonotoneTableConstruction.code graph width rows roots 0).toList ++
    ((MonotoneOutputSearch.code parameters.buses parameters.bridge.target graph.nodeCount
      (sourceHeap width parameters.channels rows roots).size (found parameters graph)
      (absent parameters graph width rows roots) graph.roots.length (constructionSize graph)
      (SharedDetectorPrepared.rootBase graph)).map WitnessStack.redirect ++
    (BasisNativeFinish.code parameters width (nativeBase graph width rows roots) (found parameters graph) ++ [.halt]))

def program (parameters : Parameters) (graph : DAG parameters.channels) (rows : List Row) (roots : List Nat) :
    Program (Width parameters graph) 8 := (code parameters graph (Width parameters graph) rows roots).toArray

@[simp] theorem code_length (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) :
    (code parameters graph width rows roots).length = absent parameters graph width rows roots + 1 := by
  simp only [code, List.length_append, List.length_map, Array.length_toList, MonotoneTableConstruction.code_size,
    MonotoneOutputSearch.code_length, List.length_cons, List.length_nil, absent, found,
    MonotoneDetector.found, constructionSize]
  omega

def Outcome (parameters : Parameters) (graph : DAG parameters.channels) (old : List (Word width))
    (final : State width 8) : Prop :=
  match MonotoneDecision.search graph parameters.buses parameters.bridge.target with
  | none => final.output = old
  | some K => final.output = (NativeRootLoad.words width
      (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ old ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true

set_option maxHeartbeats 2000000 in
theorem from_source (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (graph : DAG parameters.channels) (noGuards : GateBasis.NoNegativeGuards graph)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots)
    (observations : Fin graph.roots.length → Fin parameters.decoder.roots.length)
    (observationEq : ∀ position K, parameters.observations (observations position) (assignmentOfSet K) =
      graph.eval (assignmentOfSet K) graph.roots[position.val])
    (caller output : List (Word (Width parameters graph))) :
    ∃ final ticks peak, Execution (program parameters graph rows roots)
      (initial parameters.channels (Width parameters graph) rows roots caller output) final ticks peak ∧
      ticks ≤ 192 * ((parameters.channels + 1) * (graph.countedSize + 1)) + 34 * (selectedSize parameters).total + 1 ∧
      programWords (program parameters graph rows roots) + peak ≤
        2048 * ((parameters.channels + 1) * (graph.countedSize + 1)) + 160 * (selectedSize parameters).total + caller.length + output.length ∧
      final.halted = true ∧ final.stack = caller ∧ Outcome parameters graph output final ∧
      (MonotoneDecision.search graph parameters.buses parameters.bridge.target = none ↔
        ¬∃ root ∈ graph.roots, ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
          graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {parameters.bridge.target}) root) := by
  let start := LiteralSourceConstruction.initial parameters.channels (Width parameters graph) rows roots caller output
  let resident := program parameters graph rows roots
  let base := start.heap.size
  let total := (parameters.channels + 1) * (graph.countedSize + 1)
  have positive : 0 < total := Nat.mul_pos (by omega) (by omega)
  have size := graph.countedSize_eq
  have baseline : graph.countedSize + 1 ≤ total := le_mul_of_one_le_left (Nat.zero_le _) (by omega)
  have channels : parameters.channels ≤ total := by omega
  have capacity := SharedMachineCapacity.capacity 0 total (selectedSize parameters).total
  simp only [Nat.zero_add] at capacity
  change 131072 * (total + (selectedSize parameters).total + 1) < 2 ^ Width parameters graph at capacity
  have source : base ≤ 7 * total := by
    have bound := source_size_bound graph rows roots matched rootMatches (width := Width parameters graph)
    change base ≤ 7 * (graph.countedSize + 1) at bound
    omega
  have matrixBound : (matrix graph (Width parameters graph)).length ≤ total := by
    rw [matrix_length]; exact Nat.mul_le_mul_left (parameters.channels + 1) (by omega)
  have codeBound : constructionSize graph ≤ 307 * total := by
    have product : 2 * (parameters.channels + 1) * graph.nodeCount = 2 * (matrix graph (Width parameters graph)).length := by
      rw [matrix_length]; ring
    unfold constructionSize
    change 162 * parameters.channels + 143 + 2 * (parameters.channels + 1) * graph.nodeCount ≤ _
    rw [product]; omega
  have traversal : graph.roots.length * MonotoneOutputSearch.stride parameters.buses parameters.channels ≤ 57 * total := by
    have bound := MonotoneOutputSearch.stride_bound parameters.buses parameters.channels
    have mult := Nat.mul_le_mul (show graph.roots.length ≤ graph.countedSize + 1 by omega)
      (show MonotoneOutputSearch.stride parameters.buses parameters.channels ≤ 57 * (parameters.channels + 1) by omega)
    convert mult using 1 <;> dsimp [total] <;> ring
  have traversaltime : graph.roots.length * (22 * parameters.channels + 22) + 2 ≤ 22 * total + 2 := by
    have mult := Nat.mul_le_mul_right (22 * parameters.channels + 22) (show graph.roots.length ≤ graph.countedSize + 1 by omega)
    have eq : (graph.countedSize + 1) * (22 * parameters.channels + 22) = 22 * total := by dsimp [total]; ring
    rw [eq] at mult; omega
  have nativeLength := BasisNativeFinish.code_bound parameters (Width parameters graph)
    (nativeBase graph (Width parameters graph) rows roots) (found parameters graph)
  have foundBound : found parameters graph ≤ 364 * total + 2 := by
    change constructionSize graph + graph.roots.length * MonotoneOutputSearch.stride parameters.buses parameters.channels + 2 ≤ _; omega
  have nativeSize : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]; omega
  have physical : SharedRootRead.BlockAt resident 0 (code parameters graph (Width parameters graph) rows roots) := by
    intro i h; simp only [resident, program, Nat.zero_add, List.getElem?_toArray]
  have constructorAt := SharedDetectorAssembly.block_left resident 0 _ _ physical
  have restAt := SharedDetectorAssembly.block_right resident 0 _ _ physical
  simp only [Array.length_toList, MonotoneTableConstruction.code_size, Nat.zero_add] at restAt
  have searchAt := SharedDetectorAssembly.block_left resident (constructionSize graph) _ _ restAt
  have tailAt := SharedDetectorAssembly.block_right resident (constructionSize graph) _ _ restAt
  simp only [List.length_map, MonotoneOutputSearch.code_length] at tailAt
  have nativeAt := SharedDetectorAssembly.block_left resident (found parameters graph) _ _ tailAt
  have haltAt := SharedDetectorAssembly.block_right resident (found parameters graph) _ _ tailAt
  have constructor : CodeAt resident 0 (MonotoneTableConstruction.code graph (Width parameters graph) rows roots 0) := by
    intro i; simpa only [Array.getElem?_toList] using constructorAt i.val (by simpa using i.isLt)
  obtain ⟨built, bt, bp, buildTrace, buildTime, buildSpace, buildHeap, buildStack, buildOutput, buildPC, buildRun⟩ :=
    MonotoneTableConstruction.execution resident start graph rows roots matched heads rootMatches 0
      (by omega) (by simpa only [Nat.zero_add, constructionSize] using
        (show constructionSize graph < 2 ^ Width parameters graph by omega)) (by omega) rfl rfl rfl constructor
  have builtSize : built.heap.size = base + (matrix graph (Width parameters graph)).length := by
    simp only [buildHeap, Array.size_append, List.size_toArray]; rfl
  have builtLive : built.liveWords = start.liveWords + (matrix graph (Width parameters graph)).length := by
    simp only [State.liveWords, builtSize, buildStack, buildOutput, base]; omega
  have stored : MonotoneRoot.MatrixAt built.heap base graph := by
    rw [buildHeap]; exact MonotoneDetector.matrix_stored graph _
  have rootCells : LiteralOutputSearch.Stored built.heap (SharedDetectorPrepared.rootBase graph) graph.roots := by
    rw [buildHeap]; exact LiteralDetector.roots_stored graph rows roots matched rootMatches _
  obtain ⟨queried, qt, qp, queryTrace, queryTime, querySpace, queryHeap, queryOutput, queryRun, result⟩ :=
    BasisStackSearch.monotone_execution resident graph parameters.buses parameters.bridge.target base (found parameters graph)
      (absent parameters graph (Width parameters graph) rows roots) (constructionSize graph)
      (SharedDetectorPrepared.rootBase graph) built
      (by simpa only [Nat.zero_add, constructionSize] using buildPC) buildRun
      (by rw [← matrix_length (width := Width parameters graph) graph]; omega) (by rw [builtSize]; omega) stored rootCells searchAt
  have qpBound : qp ≤ start.liveWords + 2 * total := by rw [builtLive] at querySpace; omega
  have bpBound : bp ≤ start.liveWords + 8 * total := buildSpace
  have querySize : queried.heap.size = nativeBase graph (Width parameters graph) rows roots := by
    rw [queryHeap, builtSize]; rfl
  have queryOut : queried.output = output := queryOutput.trans buildOutput
  have outcome : ∃ final ft fp, Execution resident queried final ft fp ∧
      ft ≤ 34 * (selectedSize parameters).total + 1 ∧ fp ≤ queried.liveWords + 2 * (selectedSize parameters).total ∧
      final.halted = true ∧ final.stack = caller ∧ Outcome parameters graph output final := by
    cases answer : MonotoneDecision.search graph parameters.buses parameters.bridge.target with
    | none =>
      have res : queried.pc = word _ (absent parameters graph (Width parameters graph) rows roots) ∧ queried.stack = built.stack := by
        simpa only [answer, BasisStackSearch.Result] using result
      obtain ⟨final, tr, run, heap, stack, out⟩ := EnumerationSteps.halt_execution resident queried
        (absent parameters graph (Width parameters graph) rows roots) res.1 queryRun
        (by unfold absent; omega)
        (by simpa only [absent, Nat.add_zero, List.getElem?_cons_zero] using haltAt 0 (by simp))
      exact ⟨final, 1, queried.liveWords, tr, by omega, by omega, run,
        stack.trans (res.2.trans buildStack), by simpa only [Outcome, answer] using out.trans queryOut⟩
    | some K =>
      have res : queried.pc = word _ (found parameters graph) ∧
          queried.stack = LiteralWitnessReturn.words _ K ++ built.stack := by
        simpa only [answer, BasisStackSearch.Result] using result
      obtain ⟨eligible, root, member, changes⟩ := MonotoneDecision.search_some graph parameters.buses parameters.bridge.target K answer
      obtain ⟨index, eq⟩ := List.mem_iff_get.mp member
      change graph.roots[index.val] = root at eq
      have differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
          parameters.observations output (assignmentOfSet K) := by
        refine ⟨observations index, ?_⟩
        rw [observationEq, observationEq]
        simpa only [eq] using changes.symm
      obtain ⟨final, ft, fp, trace, time, space, stack, halted, out, checked⟩ :=
        BasisNativeFinish.execution parameters raw K eligible drive differs resident queried (found parameters graph) caller
          res.1 queryRun (by rw [res.2, buildStack]; rfl)
          (by rw [querySize]; omega) (by omega) (by rw [queryHeap, builtSize]; omega)
          (by simpa only [querySize] using nativeAt)
      exact ⟨final, ft, fp, trace, time, space, halted, stack, by
        simp only [Outcome, answer]
        exact ⟨by rw [out, queryOut], checked⟩⟩
  obtain ⟨final, ft, fp, finishTrace, finishTime, finishSpace, halted, stack, outcome⟩ := outcome
  have endBound := queryTrace.final_storage_le
  have live : start.liveWords ≤ 9 + 7 * total + caller.length + output.length := by
    dsimp only [base, State.liveWords, start, LiteralSourceConstruction.initial] at source ⊢; omega
  have programBound : programWords resident ≤ 4 * (364 * total + 34 * (selectedSize parameters).total + 4) := by
    simp only [resident, programWords, program, List.size_toArray, code_length, absent]; omega
  refine ⟨final, bt + qt + ft, max (max bp qp) fp, (buildTrace.append queryTrace).append finishTrace,
    ?_, ?_, halted, stack, outcome, MonotoneDecision.search_none_iff graph noGuards _ _⟩
  · have time : bt ≤ 128 * total := buildTime
    omega
  · change programWords resident + max (max bp qp) fp ≤
      2048 * total + 160 * (selectedSize parameters).total + caller.length + output.length
    omega

end Controller.Extensions.MonotoneNativeDetector
