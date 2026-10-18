module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationQuery
public import Controller.Cost.SharedQueryResidentPlan

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Resident layout of the decision-only zero query. It reuses the shared source/constructor
prefix and solver prefix; only the worklist answer blocks differ, and both jump to the counted
cleanup, dictionary reset and decision pop. The query returns at the end of its own code. -/
namespace Controller.Cost.EnumerationResident
open Controller.Cost.ForestZeroTouch Controller.Cost.GateProgram Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestZeroEmit Controller.CNF Controller.Cost.EnumerationQuery

def worklistCode (width entry n base cleanup : Nat) : Program width 8 :=
  Controller.Horn.WorklistSeed.code (n := n) width base entry (entry + 47) (entry + 121) ++
  Controller.Horn.WorklistAccept.headSetupCode (n := n) width base (entry + 51) ++
  Controller.Horn.WorklistFIFO.fetchCode (n := n) width base (entry + 51) (entry + 108) (entry + 70) ++
  Controller.Horn.WorklistFIFO.advanceCode (n := n) width base (entry + 51) ++
  Controller.Horn.WorklistBucketLoop.code width (entry + 70) (entry + 65) (entry + 82) ++
  Controller.Horn.WorklistBucketReady.code (n := n) width base (entry + 82) (entry + 65) (entry + 121) (entry + 70) ++
  quietSavedCode width 1 cleanup ++ quietSavedCode width 0 cleanup

@[simp] theorem worklistCode_size : (worklistCode width entry n base cleanup).size = 134 := by
  simp [worklistCode, Controller.Horn.WorklistSeed.code, Controller.Horn.WorklistAccept.headSetupCode,
    Controller.Horn.WorklistFIFO.fetchCode, Controller.Horn.WorklistFIFO.advanceCode,
    Controller.Horn.WorklistBucketLoop.code, Controller.Horn.WorklistBucketReady.code,
    quietSavedCode, ForestZeroAnswer.saveTagCode, ForestZeroAnswer.code]

structure WorklistPhysical (program : Program width 8) (entry n base cleanup : Nat) : Prop where
  seed : Controller.Horn.WorklistSeed.At (n := n) program base entry (entry + 47) (entry + 121)
  head : ∀ phase : Fin 4, program[entry + 47 + phase.val]? =
    (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base (entry + 51))[phase.val]?
  fetch : Controller.Horn.WorklistFIFO.FetchAt (n := n) program base (entry + 51) (entry + 108) (entry + 70)
  advance : Controller.Horn.WorklistFIFO.AdvanceAt (n := n) program base (entry + 65) (entry + 51)
  bucket : Controller.Horn.WorklistBucketLoop.At program (entry + 70) (entry + 65) (entry + 82)
  ready : Controller.Horn.WorklistBucketReady.At (n := n) program base (entry + 82) (entry + 65) (entry + 121) (entry + 70)
  success : QuietSavedAt program (entry + 108) 1 cleanup
  conflict : QuietSavedAt program (entry + 121) 0 cleanup

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem worklist_physical_at (program : Program width 8) (entry n base cleanup : Nat)
    (present : SharedRootRead.BlockAt program entry (worklistCode width entry n base cleanup).toList) :
    WorklistPhysical program entry n base cleanup := by
  have fetched : ∀ offset, offset < 134 → program[entry + offset]? =
      (worklistCode width entry n base cleanup)[offset]? := by
    intro offset bound
    simpa only [Array.getElem?_toList] using present offset (by simp; exact bound)
  constructor
  all_goals intro phase
  all_goals fin_cases phase
  all_goals try simp only [Nat.add_assoc, Nat.reduceAdd]
  all_goals rw [fetched _ (by omega)]
  all_goals simp [worklistCode, Array.getElem?_append, Controller.Horn.WorklistSeed.code,
    Controller.Horn.WorklistAccept.headSetupCode, Controller.Horn.WorklistFIFO.fetchCode,
    Controller.Horn.WorklistFIFO.advanceCode, Controller.Horn.WorklistBucketLoop.code,
    Controller.Horn.WorklistBucketReady.code, quietSavedCode, ForestZeroAnswer.saveTagCode,
    ForestZeroAnswer.code, Nat.add_assoc]

/-- Solver prefix, quiet worklist and the shared cleanup/reset/decision block. -/
def solverCode (width entry n base directoryHeader endHeader inputHeader firstHeader recordHeader : Nat) :
    List (Instruction width 8) :=
  (SharedSolverPrefix.code width entry n base directoryHeader endHeader inputHeader firstHeader
    recordHeader (entry + 261)).toList ++
  (worklistCode width (entry + 261) n base (entry + 395)).toList ++
  SharedQueryCleanupCode.code width (entry + 395)

@[simp] theorem solverCode_length :
    (solverCode width entry n base directoryHeader endHeader inputHeader firstHeader recordHeader).length = 430 := by
  simp [solverCode]

/-- The complete resident decision-only query, starting at the shared query entry. -/
def code (width entry keep n base : Nat) (references : List (List (Reference ambient))) :
    List (Instruction width 8) :=
  SharedQuerySourceCode.code width entry keep references ++
  solverCode width (SharedQuerySourceCode.solverEntry width entry keep references)
    n base (keep + 3) (keep + 4) (keep + 1) (keep + 2) keep

theorem code_end (width entry keep n base : Nat) (references : List (List (Reference ambient))) :
    entry + (code width entry keep n base references).length =
      SharedQuerySourceCode.solverEntry width entry keep references + 430 := by
  have before : entry ≤ SharedQuerySourceCode.solverEntry width entry keep references := by
    unfold SharedQuerySourceCode.solverEntry; omega
  simp only [code, List.length_append, SharedQuerySourceCode.code_length, solverCode_length]
  omega

private theorem left_at (program : Program width 8) (entry : Nat) (first rest : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (first ++ rest)) : SharedRootRead.BlockAt program entry first := by
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rwa [List.getElem?_append_left below] at found

private theorem right_at (program : Program width 8) (entry : Nat) (first rest : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program (entry + first.length) rest := by
  intro offset below
  have found := present (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at found
  simpa only [Nat.add_assoc] using found

structure Physical (program : Program width 8) (entry keep n base : Nat)
    (references : List (List (Reference ambient))) : Prop where
  source : SharedQuerySourceCode.Physical program entry keep references
  prepared : SharedSolverPrefix.Physical program (SharedQuerySourceCode.solverEntry width entry keep references)
    n base keep (SharedQuerySourceCode.solverEntry width entry keep references + 261)
  prefixBlock : SharedRootRead.BlockAt program (SharedQuerySourceCode.solverEntry width entry keep references)
    (SharedSolverPrefix.code width (SharedQuerySourceCode.solverEntry width entry keep references) n base
      (keep + 3) (keep + 4) (keep + 1) (keep + 2) keep
      (SharedQuerySourceCode.solverEntry width entry keep references + 261)).toList
  worklist : WorklistPhysical program (SharedQuerySourceCode.solverEntry width entry keep references + 261)
    n base (SharedQuerySourceCode.solverEntry width entry keep references + 395)
  cleanup : SharedQueryCleanupCode.Physical program (SharedQuerySourceCode.solverEntry width entry keep references + 395)

set_option maxRecDepth 4096 in
theorem physical_at (program : Program width 8) (entry keep n base : Nat)
    (references : List (List (Reference ambient)))
    (present : SharedRootRead.BlockAt program entry (code width entry keep n base references)) :
    Physical program entry keep n base references := by
  unfold code at present
  have sourceAt := left_at program entry _ _ present
  have solverAt := right_at program entry _ _ present
  have before : entry ≤ SharedQuerySourceCode.solverEntry width entry keep references := by
    unfold SharedQuerySourceCode.solverEntry; omega
  rw [SharedQuerySourceCode.code_length, Nat.add_sub_cancel' before] at solverAt
  unfold solverCode at solverAt
  have prefixAt := left_at program _ _ _ (left_at program _ _ _ solverAt)
  have worklistAt := right_at program _ _ _ (left_at program _ _ _ solverAt)
  have cleanupAt := right_at program _ _ _ solverAt
  simp only [Array.length_toList, SharedSolverPrefix.code_size] at worklistAt
  simp only [List.length_append, Array.length_toList, SharedSolverPrefix.code_size, worklistCode_size,
    Nat.add_assoc, Nat.reduceAdd] at cleanupAt
  exact ⟨SharedQuerySourceCode.physical_at program entry keep references sourceAt,
    SharedSolverPrefix.physical_at program _ n base _ _ _ _ keep _ prefixAt, prefixAt,
    worklist_physical_at program _ n base _ worklistAt,
    SharedQueryCleanupCode.physical_at program _ cleanupAt⟩

structure Conditions {width ambient : Nat} (channels : Nat) (program : Program width 8) (initial : State width 8)
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : channels ≤ ambient) : Prop where
  sourceReferences : ∀ reference ∈ references.flatten,
    Controller.Cost.ForestZeroEmit.StoredReference initial.heap channels sourceEnd reference
  sourceBeforeTable : sourceEnd ≤ sharedLayout.tableBase
  sourceBeforeInverse : sourceEnd ≤ sharedLayout.inverseBase
  sourceBound : sourceEnd ≤ initial.heap.size
  sourcePositive : 0 < sourceEnd
  sourceChannel : initial.heap[0]? = some (word width channels)
  sourceNodes : initial.heap[1]? = some (word width nodes)
  ambientEq : ambient = channels + nodes
  adjacent : sharedLayout.inverseBase = sharedLayout.tableBase + ambient
  tablePositive : 0 < sharedLayout.tableBase
  sourceHeaderRoom : 1 < sourceEnd
  sourceDual : Controller.Horn.DualHorn
    (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references)))
  sourceEndpoint : initial.heap.size = sharedLayout.inverseBase + ambient
  constructorRoom : initial.heap.size + 5 + 2 * (references.length + 1) +
    2 * references.flatten.length + 2 * ambient < 2 ^ width
  room : (constructorState initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references)
      (word width initial.heap.size :: rest) initial.output initial.reg).heap.size +
    5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4 +
    3 * (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
      (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList.length +
    ((constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
      (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList.map List.length).sum +
    2 * (Controller.Horn.IndexScan.occurrences (constructorFormula initial.heap sharedLayout
      (ForestZeroCompile.empty ambient) (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList
      ((constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size +
        5 * (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size + 4)).length
    < 2 ^ width
  residentCapacity : SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 430 < 2 ^ width

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- The resident decision-only query: from the shared query entry it decides satisfiability of the
source-constructed zero system and returns, ready for the next query, with the output unchanged. -/
theorem execution {width ambient : Nat} (channels : Nat)
    (program : Program width 8) (initial : State width 8) (sourceHeap : Array (Word width))
    (sharedLayout : Layout ambient initial.heap.size)
    (references : List (List (Reference ambient))) (sourceEnd nodes sourceEntry : Nat)
    (rest : List (Word width)) (within : channels ≤ ambient)
    (conditions : Conditions channels program initial sharedLayout references sourceEnd nodes sourceEntry rest within)
    (present : SharedRootRead.BlockAt program sourceEntry
      (code width sourceEntry initial.heap.size
        (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size
        (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size
        references))
    (initialReady : QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase
      sourceEntry rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧
      final.halted = false ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 150 * references.length + 387 * references.flatten.length + 441 ∧
      peak ≤ initial.liveWords + 5 * references.length + 15 * references.flatten.length + channels + 20 ∧
      final.output = initial.output ∧
      (answer = true ↔ Controller.CNF.Satisfiable
        (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references channels within)) ∧
      QueryReady (ambient := ambient) sourceHeap sharedLayout.tableBase sharedLayout.inverseBase
        (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 430) rest final := by
  have physical := physical_at program sourceEntry initial.heap.size
    (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references).coordinates.size
    (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size
    references present
  have represented : Represented initial.heap sharedLayout (ForestZeroCompile.empty ambient) :=
    empty_dictionary_from_zero_table initial.heap sharedLayout initialReady.zeroTable
  have initialEq := initialReady.entry_state
  have sourceBefore : sourceEntry + 15 ≤ SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references := by
    unfold SharedQuerySourceCode.solverEntry; omega
  have constructorEnd : sourceEntry + 15 +
      (constructorCode width (sourceEntry + 15) initial.heap.size initial.heap.size
        (initial.heap.size + 4) (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references)
        references).length = SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references := by
    simp only [constructorCode, List.length_append, ForestZeroAdmissibleCaller.code_length,
      SharedQuerySourceCode.solverEntry]
    omega
  have constructorRoom := conditions.constructorRoom
  have residentCapacity := conditions.residentCapacity
  have ambientFits : ambient + 1 < 2 ^ width := by omega
  have dictionaryCoherent := (ForestZeroCompile.rows_dictionary (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient)
    (ForestZeroAssembly.originalRows (reservedReferences references))).1
  have localBound := ForestZeroDictionary.count_le_ambient
    (constructorDictionary initial.heap sharedLayout (ForestZeroCompile.empty ambient) references)
    dictionaryCoherent
  have actualRoom := conditions.room
  simp only [constructorState, RegisterWiden.widenState, atState] at actualRoom
  have stateHeap : (constructorState initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references)
      (word width initial.heap.size :: rest) initial.output initial.reg).heap.size =
      (constructorHeap initial.heap sharedLayout (ForestZeroCompile.empty ambient) references channels).size := rfl
  obtain ⟨answer, final, ticks, peak, trace, timeBound, spaceBound, heapSize, finalStack, finalOutput,
      finalPC, finalRunning, finalFrame, zeroTable, decision, zeroRegister, tableRegister, inverseRegister,
      meaning, finalLive, sourceFrame, reusable⟩ :=
    quiet_constructor_execution initial.heap sharedLayout (ForestZeroCompile.empty ambient) represented references
      sourceEnd nodes conditions.sourceReferences conditions.sourceBeforeTable conditions.sourceBeforeInverse
      conditions.sourceBound conditions.sourcePositive conditions.sourceChannel conditions.sourceNodes
      conditions.ambientEq conditions.adjacent conditions.tablePositive conditions.sourceHeaderRoom
      conditions.sourceDual program sourceEntry (sourceEntry + 15)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) rfl rfl
      conditions.sourceEndpoint (initial.reg 3).val (by omega)
      physical.source.reuse physical.source.saved physical.source.cursor rest initial.output initial.reg
      conditions.constructorRoom ambientFits (by omega) physical.source.constructor
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 261)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 308)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 382)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.count)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.allocate)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.headers)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.endpoint)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.saved)
      (SharedSolverPrefix.normalizer_at program _ _
        (constructorFormula initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references channels within).clauses.toList
        (constructorFormulaBackend initial.heap sharedLayout (ForestZeroCompile.empty ambient)
          (ForestZeroCompile.empty_coherent ambient) references channels within) physical.prefixBlock)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.indexSave)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.index)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.indexRestore)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.capture)
      (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.prepared.seed)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.worklist.seed)
      conditions.room (by omega)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 312)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.worklist.head) (by omega)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 369)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 331)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 326)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 343)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 326)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.worklist.fetch)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.worklist.advance)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.worklist.bucket)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.worklist.ready)
      (by omega) (by omega) (by omega) (by omega)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 395)
      (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 402)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.worklist.success)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.worklist.conflict)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.cleanup.setup)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.cleanup.release)
      (by omega) (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.cleanup.prepare)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.cleanup.reset)
      (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, constructorState, RegisterWiden.widenState, atState] using physical.cleanup.decision)
  rw [initialEq] at trace finalLive
  have budgets := constructor_full_query_budget initial.heap sharedLayout (ForestZeroCompile.empty ambient)
    (ForestZeroCompile.empty_coherent ambient) references channels within rfl
    (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references) sourceEntry
    (initial.reg 3).val rest initial.output initial.reg false
  rw [initialEq] at budgets
  simp only [constructorFormula_rows] at timeBound spaceBound
  simp only [Bool.false_eq_true, ite_false] at budgets
  refine ⟨answer, final, ticks, peak, trace, finalRunning, decision,
    (by have bound := budgets.1; omega), (by have := budgets.2; omega), ?_, ?_, ?_⟩
  · simpa [constructorState, RegisterWiden.widenState, atState] using finalOutput
  · simpa only [Controller.CNF.Satisfiable] using meaning
  · have ready : QueryReady (ambient := ambient) initial.heap sharedLayout.tableBase sharedLayout.inverseBase
        (SharedQuerySourceCode.solverEntry width sourceEntry initial.heap.size references + 430) rest final := by
      refine ⟨heapSize, sourceFrame, ?_, finalStack, ?_, finalRunning, zeroRegister, ?_, ?_⟩
      · simpa only [constructorDictionaryLayout] using zeroTable
      · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
      · simpa only [constructorDictionaryLayout] using tableRegister
      · simpa only [constructorDictionaryLayout] using inverseRegister
    exact ready.rebase initialReady.heapSize initialReady.sourceFrame

end Controller.Cost.EnumerationResident
