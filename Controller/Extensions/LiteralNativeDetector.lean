module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.BasisNativeFinish

public import Mathlib.Tactic.Ring

@[expose] public section

/-! No-OR detection and native model emission in one fetched execution,
starting with the original shared graph packet. -/
namespace Controller.Extensions.LiteralNativeDetector
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGRun Controller.Cost.UniformDAGSource
open Controller.Cost.RawTransferLoops
open Controller.Extensions.LiteralSourceConstruction (initial source_size_bound)
open Controller.Extensions.LiteralDetector (sourceHeap)
open Controller.Extensions.LiteralSourceConstruction (matrix matrix_length constructionSize constructionCode constructionCode_size construction_execution constructionSize_bound)

def Width (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  SharedMachineCapacity.wordWidth 0 ((parameters.channels + 1) * (graph.countedSize + 1)) (selectedSize parameters).total

def found (parameters : Parameters) (graph : DAG parameters.channels) (base : Nat) : Nat :=
  LiteralDetector.found graph parameters.buses parameters.bridge.target base

def nativeBase (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) : Nat :=
  (sourceHeap width n rows roots).size + (matrix graph width).length + graph.nodeCount

def absent (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) : Nat :=
  found parameters graph (sourceHeap width parameters.channels rows roots).size + (BasisNativeFinish.code parameters width (nativeBase graph width rows roots)
    (found parameters graph (sourceHeap width parameters.channels rows roots).size)).length

def code (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) : List (Instruction width 8) :=
  (constructionCode graph width rows roots 0 (sourceHeap width parameters.channels rows roots).size).toList ++
    ((LiteralOutputSearch.code parameters.buses parameters.bridge.target graph.nodeCount
      (sourceHeap width parameters.channels rows roots).size (found parameters graph (sourceHeap width parameters.channels rows roots).size)
      (absent parameters graph width rows roots) graph.roots.length (constructionSize graph)
      (SharedDetectorPrepared.rootBase graph)).map WitnessStack.redirect ++
    (BasisNativeFinish.code parameters width (nativeBase graph width rows roots) (found parameters graph (sourceHeap width parameters.channels rows roots).size) ++ [.halt]))

def program (parameters : Parameters) (graph : DAG parameters.channels) (rows : List Row) (roots : List Nat) :
    Program (Width parameters graph) 8 := (code parameters graph (Width parameters graph) rows roots).toArray

@[simp] theorem code_length (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) :
    (code parameters graph width rows roots).length = absent parameters graph width rows roots + 1 := by
  simp only [code, List.length_append, List.length_map, Array.length_toList, constructionCode_size,
    LiteralOutputSearch.code_length, List.length_cons, List.length_nil, absent, found,
    LiteralDetector.found, constructionSize]
  omega

def Outcome (parameters : Parameters) (graph : DAG parameters.channels) (old : List (Word width))
    (final : State width 8) : Prop :=
  match LiteralWitness.search graph parameters.buses parameters.bridge.target with
  | none => final.output = old
  | some K => final.output = (NativeRootLoad.words width
      (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ old ∧
      Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true

set_option maxHeartbeats 2000000 in
theorem from_source (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (graph : DAG parameters.channels) (noOr : GateBasis.NoDisjunction graph)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots)
    (observations : Fin graph.roots.length → Fin parameters.decoder.roots.length)
    (observationEq : ∀ position K, parameters.observations (observations position) (assignmentOfSet K) =
      graph.eval (assignmentOfSet K) graph.roots[position.val])
    (caller output : List (Word (Width parameters graph))) :
    ∃ final ticks peak, Execution (program parameters graph rows roots)
      (initial parameters.channels (Width parameters graph) rows roots caller output) final ticks peak ∧
      ticks ≤ 640 * ((parameters.channels + 1) * (graph.countedSize + 1)) + 34 * (selectedSize parameters).total + 1 ∧
      programWords (program parameters graph rows roots) + peak ≤
        4096 * ((parameters.channels + 1) * (graph.countedSize + 1)) + 160 * (selectedSize parameters).total + caller.length + output.length ∧
      final.halted = true ∧ final.stack = caller ∧ Outcome parameters graph output final ∧
      (LiteralWitness.search graph parameters.buses parameters.bridge.target = none ↔
        ¬∃ root ∈ graph.roots, ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
          graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {parameters.bridge.target}) root) := by
  let start := LiteralSourceConstruction.initial parameters.channels (Width parameters graph) rows roots caller output
  let resident := program parameters graph rows roots
  let base := start.heap.size
  have baseEq : (sourceHeap (Width parameters graph) parameters.channels rows roots).size = base := rfl
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
  have matrixBound : (matrix graph (Width parameters graph)).length ≤ 4 * total := by
    rw [matrix_length]
    have mult := Nat.mul_le_mul (show 2 * parameters.channels + 1 ≤ 4 * (parameters.channels + 1) by omega)
      (show graph.nodeCount ≤ graph.countedSize + 1 by omega)
    simpa only [Nat.mul_assoc] using mult
  have codeBound : constructionSize graph ≤ 512 * total := constructionSize_bound graph
  have traversal : graph.roots.length * LiteralOutputSearch.stride parameters.buses parameters.bridge.target graph.nodeCount base ≤ 172 * total := by
    have bound := LiteralOutputSearch.stride_bound parameters.buses parameters.bridge.target graph.nodeCount base
    have mult := Nat.mul_le_mul (show graph.roots.length ≤ graph.countedSize + 1 by omega)
      (show LiteralOutputSearch.stride parameters.buses parameters.bridge.target graph.nodeCount base ≤ 172 * (parameters.channels + 1) by omega)
    convert mult using 1 <;> dsimp [total] <;> ring
  have traversaltime : graph.roots.length * (73 * parameters.channels + 70) + 2 ≤ 143 * total + 2 := by
    have mult := Nat.mul_le_mul (show graph.roots.length ≤ graph.countedSize + 1 by omega)
      (show 73 * parameters.channels + 70 ≤ 143 * (parameters.channels + 1) by omega)
    have eq : (graph.countedSize + 1) * (143 * (parameters.channels + 1)) = 143 * total := by dsimp [total]; ring
    rw [eq] at mult; omega
  have nativeLength := BasisNativeFinish.code_bound parameters (Width parameters graph)
    (nativeBase graph (Width parameters graph) rows roots) (found parameters graph base)
  have foundBound : found parameters graph base ≤ 684 * total + 2 := by
    change constructionSize graph + graph.roots.length * LiteralOutputSearch.stride parameters.buses parameters.bridge.target graph.nodeCount base + 2 ≤ _; omega
  have nativeSize : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]; omega
  have physical : SharedRootRead.BlockAt resident 0 (code parameters graph (Width parameters graph) rows roots) := by
    intro i h; simp only [resident, program, Nat.zero_add, List.getElem?_toArray]
  have constructorAt := SharedDetectorAssembly.block_left resident 0 _ _ physical
  have restAt := SharedDetectorAssembly.block_right resident 0 _ _ physical
  simp only [baseEq] at constructorAt restAt
  simp only [Array.length_toList, constructionCode_size, Nat.zero_add] at restAt
  have searchAt := SharedDetectorAssembly.block_left resident (constructionSize graph) _ _ restAt
  have tailAt := SharedDetectorAssembly.block_right resident (constructionSize graph) _ _ restAt
  simp only [List.length_map, LiteralOutputSearch.code_length] at tailAt
  have nativeAt := SharedDetectorAssembly.block_left resident (found parameters graph base) _ _ tailAt
  have haltAt := SharedDetectorAssembly.block_right resident (found parameters graph base) _ _ tailAt
  have constructor : CodeAt resident 0 (constructionCode graph (Width parameters graph) rows roots 0 base) := by
    intro i; simpa only [Array.getElem?_toList] using constructorAt i.val (by simpa using i.isLt)
  obtain ⟨built, bt, bp, buildTrace, buildTime, buildSpace, buildHeap, buildStack, buildOutput, buildPC, buildRun⟩ :=
    construction_execution resident start graph noOr rows roots matched heads rootMatches 0 base
      (by omega) constructor (by omega) rfl rfl rfl rfl (by omega)
  have builtSize : built.heap.size = base + (matrix graph (Width parameters graph)).length + graph.nodeCount := by
    simp only [buildHeap, Array.size_append, List.size_toArray, List.length_ofFn]; rfl
  have builtLive : built.liveWords = start.liveWords + (matrix graph (Width parameters graph)).length + graph.nodeCount := by
    simp only [State.liveWords, builtSize, buildStack, buildOutput, base]; omega
  have stored : LiteralRoot.MatrixAt built.heap base graph := by
    rw [buildHeap]; exact LiteralDetector.matrix_stored graph _ _
  have rootCells : LiteralOutputSearch.Stored built.heap (SharedDetectorPrepared.rootBase graph) graph.roots := by
    rw [buildHeap, Array.append_assoc]; exact LiteralDetector.roots_stored graph rows roots matched rootMatches _
  obtain ⟨queried, qt, qp, queryTrace, queryTime, querySpace, queryHeap, queryOutput, queryRun, result⟩ :=
    BasisStackSearch.literal_execution resident graph noOr parameters.buses parameters.bridge.target base (found parameters graph base)
      (absent parameters graph (Width parameters graph) rows roots) (constructionSize graph)
      (SharedDetectorPrepared.rootBase graph) built
      (by simpa only [Nat.zero_add, constructionSize] using buildPC) buildRun
      (by rw [← matrix_length (width := Width parameters graph) graph]; omega) (by rw [builtSize]; omega) stored rootCells searchAt
  have qpBound : qp ≤ start.liveWords + 6 * total := by rw [builtLive] at querySpace; omega
  have bpBound : bp ≤ start.liveWords + 16 * total := by simpa only [Nat.mul_assoc] using buildSpace
  have querySize : queried.heap.size = nativeBase graph (Width parameters graph) rows roots := by
    rw [queryHeap, builtSize]; rfl
  have queryOut : queried.output = output := queryOutput.trans buildOutput
  have outcome : ∃ final ft fp, Execution resident queried final ft fp ∧
      ft ≤ 34 * (selectedSize parameters).total + 1 ∧ fp ≤ queried.liveWords + 2 * (selectedSize parameters).total ∧
      final.halted = true ∧ final.stack = caller ∧ Outcome parameters graph output final := by
    cases answer : LiteralWitness.search graph parameters.buses parameters.bridge.target with
    | none =>
      have res : queried.pc = word _ (absent parameters graph (Width parameters graph) rows roots) ∧ queried.stack = built.stack := by
        simpa only [answer, BasisStackSearch.Result] using result
      obtain ⟨final, tr, run, heap, stack, out⟩ := EnumerationSteps.halt_execution resident queried
        (absent parameters graph (Width parameters graph) rows roots) res.1 queryRun
        (by unfold absent; rw [baseEq]; omega)
        (by simpa only [absent, baseEq, Nat.add_zero, List.getElem?_cons_zero] using haltAt 0 (by simp))
      exact ⟨final, 1, queried.liveWords, tr, by omega, by omega, run,
        stack.trans (res.2.trans buildStack), by simpa only [Outcome, answer] using out.trans queryOut⟩
    | some K =>
      have res : queried.pc = word _ (found parameters graph base) ∧
          queried.stack = LiteralWitnessReturn.words _ K ++ built.stack := by
        simpa only [answer, BasisStackSearch.Result] using result
      obtain ⟨eligible, root, member, changes⟩ := LiteralWitness.search_some graph noOr parameters.buses parameters.bridge.target K answer
      obtain ⟨index, eq⟩ := List.mem_iff_get.mp member
      change graph.roots[index.val] = root at eq
      have differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
          parameters.observations output (assignmentOfSet K) := by
        refine ⟨observations index, ?_⟩
        rw [observationEq, observationEq]
        simpa only [eq] using changes.symm
      obtain ⟨final, ft, fp, trace, time, space, stack, halted, out, checked⟩ :=
        BasisNativeFinish.execution parameters raw K eligible drive differs resident queried (found parameters graph base) caller
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
  have programBound : programWords resident ≤ 4 * (684 * total + 34 * (selectedSize parameters).total + 4) := by
    simp only [resident, programWords, program, List.size_toArray, code_length, absent, baseEq]; omega
  refine ⟨final, bt + qt + ft, max (max bp qp) fp, (buildTrace.append queryTrace).append finishTrace,
    ?_, ?_, halted, stack, outcome, LiteralWitness.search_none_iff graph noOr _ _⟩
  · have time : bt ≤ 480 * total := by simpa only [Nat.mul_assoc] using buildTime
    omega
  · change programWords resident + max (max bp qp) fp ≤
      4096 * total + 160 * (selectedSize parameters).total + caller.length + output.length
    omega

end Controller.Extensions.LiteralNativeDetector
