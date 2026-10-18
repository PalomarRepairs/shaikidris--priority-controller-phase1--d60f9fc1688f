module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceSupportSummaries
public import Controller.NativeProof.XorUnits
public import Controller.Native.SourceTransport
public import Controller.Physical.DetectCorrect

@[expose] public section

/-! The native compiler uses the independent UNSAT-to-discrepancy lift,
shared decoder preparation, and ordinary resolution on actual source rows. -/
namespace Controller.NativeProof.Compiler
open Controller.CNF Controller.Resolution
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceHealthyOne
variable {parameters : Parameters} {v : Nat}

/-- The physical target assertion fixes the healthy first flag when driven.
Resolving the two faulty cofactors and this unit removes the whole context. -/
def dischargeTransfer (state : State v) (healthy faulty input output : Literal (Fin v))
    (one : GuardedTransfer state [negate healthy, negate faulty] input output)
    (zero : GuardedTransfer state [negate healthy, faulty] input output)
    (unit : AvailableSubclause state [healthy]) :
    Controller.NativeProof.SourceStagePolarity.GuardedProjection state [] input output 2 := by
  cases one with
  | identity same => exact ⟨state, [], rfl, .identity same, by simp⟩
  | derived first =>
    cases zero with
    | identity same => exact ⟨state, [], rfl, .identity same, by simp⟩
    | derived second =>
      let target := [negate input, output]
      let a : AvailableSubclause state ([negate faulty] ++ [negate healthy] ++ target) :=
        retarget first (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop)
      let b : AvailableSubclause state ([faulty] ++ target ++ [negate healthy]) :=
        retarget second (by intro l h; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; aesop)
      let joined := longMerge state faulty ([negate healthy] ++ target) (target ++ [negate healthy]) a b
      let row : AvailableSubclause joined.state ([negate healthy] ++ target) :=
        retarget (longMerge_result _ _ _ _ _ _) (by
          intro l h
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
          aesop)
      let held := afterTrace unit joined.state joined.steps (longMerge_run _ _ _ _ _ _)
      let final := longMerge joined.state healthy target [] row held
      refine ⟨final.state, joined.steps ++ final.steps, ?_, .derived ?_, ?_⟩
      · rw [runSteps_append, longMerge_run]
        exact longMerge_run _ _ _ _ _ _
      · exact retarget (longMerge_result _ _ _ _ _ _) (by intro literal member; simpa only [List.append_nil, List.nil_append] using member)
      · have aCount := longMerge_count state faulty ([negate healthy] ++ target) (target ++ [negate healthy]) a b
        have bCount := longMerge_count joined.state healthy target [] row held
        simp only [List.length_append]
        change joined.steps.length + final.steps.length ≤ 2
        dsimp only [joined, final] at *
        omega

def dischargePair (state : State v) (healthy faulty left right : Literal (Fin v))
    (one : DirectionPair state [negate healthy, negate faulty] left right)
    (zero : DirectionPair state [negate healthy, faulty] left right)
    (unit : AvailableSubclause state [healthy]) : PairedProjection state [] left right 4 := by
  let first := dischargeTransfer state healthy faulty left right one.forward zero.forward unit
  let second := dischargeTransfer first.state healthy faulty right left
    (one.backward.afterTrace first.state first.steps first.checked)
    (zero.backward.afterTrace first.state first.steps first.checked)
    (afterTrace unit first.state first.steps first.checked)
  refine ⟨second.state, first.steps ++ second.steps, ?_,
    ⟨first.result.afterTrace second.state second.steps second.checked, second.result⟩, ?_⟩
  · rw [runSteps_append, first.checked]; exact second.checked
  · have a := first.count; have b := second.count
    simp only [List.length_append]; omega

structure DrivenTable (rename : Nat → Fin v) (count : Nat) where
  summaries : SourceSupportSummaries.Table (parameters := parameters) rename parameters.decoder.nodeCount
  equalOne : ∀ output : Fin parameters.decoder.roots.length,
    DirectionPair summaries.prepared.proofPrefix.state (equalFlagContext (parameters := parameters) rename true)
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)
  healthyFlag : AvailableSubclause summaries.prepared.proofPrefix.state
    [nativeHealthyFirstFlag (parameters := parameters) rename]
  pairs : ∀ output : Fin parameters.decoder.roots.length, output.val < count →
    DirectionPair summaries.prepared.proofPrefix.state []
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)

def DrivenTable.afterTrace (table : DrivenTable (parameters := parameters) rename count)
    (next : State v) (steps : List (Step v))
    (checked : runSteps table.summaries.prepared.proofPrefix.state steps = some next) :
    DrivenTable (parameters := parameters) rename count where
  summaries := table.summaries.afterTrace next steps checked
  equalOne output := (table.equalOne output).afterTrace next steps checked
  healthyFlag := FoldProjection.afterTrace table.healthyFlag next steps checked
  pairs output bound := (table.pairs output bound).afterTrace next steps checked

def initialDriven (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) : DrivenTable (parameters := parameters) rename 0 := by
  let summaries := SourceSupportSummaries.allSummaries rename guarded (prepare rename drive guarded)
  let equal := equalDecoderProgram (parameters := parameters) rename true
  let replay := replayNativeProgram rename summaries.prepared.proofPrefix equal.table.prefixState.state
    equal.table.prefixState.steps equal.table.prefixState.checked
  let extended := summaries.afterTrace replay.next replay.added replay.checked
  let physical := SourceMismatchHandles.healthyFlagUnit rename drive
  let final := replayNativeProgram rename extended.prepared.proofPrefix physical.state physical.steps physical.checked
  refine ⟨extended.afterTrace final.next final.added final.checked, ?_, ?_, ?_⟩
  · intro output
    exact (replay.pair (compiledEqualDecoderRoot rename true output)).afterTrace final.next final.added final.checked
  · exact ⟨physical.result.clause, final.available physical.result.row, physical.result.subset⟩
  · intro output impossible
    exact False.elim (Nat.not_lt_zero output.val impossible)

def advanceDriven (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (absent : Decoder.NoDiscrepancy parameters Finset.univ) (count : Nat)
    (before : count < parameters.decoder.roots.length)
    (table : DrivenTable (parameters := parameters) rename count) :
    DrivenTable (parameters := parameters) rename (count + 1) := by
  let output : Fin parameters.decoder.roots.length := ⟨count, before⟩
  let mixed := if healthy : parameters.observations output (Controller.assignmentOfSet {parameters.bridge.target}) = true then
      SourceHealthyOneQuery.equality rename table.summaries.prepared guarded Finset.univ absent output (by simp) healthy
    else
      let actual := SourceSupportSummaries.equality rename table.summaries guarded Finset.univ absent output (by simp)
        (Bool.eq_false_of_not_eq_true healthy)
      (⟨actual.state, actual.steps, actual.checked, actual.pair, actual.count.trans (Nat.zero_le _)⟩ :
        PairedProjection table.summaries.prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
          (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)
          (parameters.channels + parameters.decoder.nodeCount))
  let current := table.afterTrace mixed.state mixed.steps mixed.checked
  have one : DirectionPair mixed.state
      [negate (nativeHealthyFirstFlag (parameters := parameters) rename), negate (nativeFaultyFirstFlag (parameters := parameters) rename)]
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output) := by
    simpa only [current, DrivenTable.afterTrace, SourceSupportSummaries.Table.afterTrace, Preparation.afterTrace, SourcePrefix.extend, equalFlagContext, SourceCongruence.assignmentGuard, ite_true, nativeHealthyFirstFlag, nativeFaultyFirstFlag] using current.equalOne output
  have zero : DirectionPair mixed.state
      [negate (nativeHealthyFirstFlag (parameters := parameters) rename), nativeFaultyFirstFlag (parameters := parameters) rename]
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output) := mixed.pair
  let final := dischargePair mixed.state _ _ _ _ one zero current.healthyFlag
  let extended := current.afterTrace final.state final.steps final.checked
  refine { extended with pairs := ?_ }
  intro query bound
  if same : query = output then exact same ▸ final.pair
  else
    have earlier : query.val < count := by
      have different : query.val ≠ count := fun h => same (Fin.ext h)
      omega
    exact extended.pairs query earlier

def buildDriven (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) (absent : Decoder.NoDiscrepancy parameters Finset.univ) :
    (count : Nat) → count ≤ parameters.decoder.roots.length → DrivenTable (parameters := parameters) rename count
  | 0, _ => initialDriven rename drive guarded
  | count + 1, bound => advanceDriven rename guarded absent count (by omega)
      (buildDriven rename drive guarded absent count (by omega))

structure EqualityPrefix (rename : Nat → Fin v) where
  proofPrefix : SourcePrefix (parameters := parameters) rename
  pairs : ∀ output : Fin parameters.decoder.roots.length,
    DirectionPair proofPrefix.state []
      (nativeRootLiteral rename .healthy output) (nativeRootLiteral rename .faulty output)

def outputPrefix (rename : Nat → Fin v) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    EqualityPrefix (parameters := parameters) rename := by
  if drive : parameters.drive = true then
    let absent := Decoder.source_unsat_noDiscrepancy parameters raw drive unsat Finset.univ
    let table := buildDriven rename drive guarded absent parameters.decoder.roots.length (Nat.le_refl _)
    exact ⟨table.summaries.prepared.proofPrefix, fun output => table.pairs output output.isLt⟩
  else
    have zero : parameters.drive = false := Bool.eq_false_of_not_eq_true drive
    exact ⟨driveZeroOutputPrefix rename zero, driveZeroOutputRoot rename zero⟩

def equalXor (state : State v) (a b output : Literal (Fin v))
    (rows : SourceStageXor.XorRows state a b output) (pair : DirectionPair state [] a b) :=
  LocalUnitCases.unit state [] (XorUnits.xorPremises rows ++ XorUnits.pairPremises pair)
    (negate output) (by
      intro values all
      have xor := XorUnits.xorPremises_value (context := []) rows values
        (fun p h => all p (List.mem_append_left _ h))
      have same := XorUnits.pair_value pair values (fun p h => all p (List.mem_append_right _ h))
      rw [literalHolds_negate]
      apply (literalValue_eq_false values output).mp
      rw [xor, same]
      cases literalValue values b <;> rfl)

def differenceLiteral (rename : Nat → Fin v) (output : Fin parameters.decoder.roots.length) :=
  mapLiteral rename (sourceRoleMap parameters (.internal (.difference output)))

structure DifferenceTable (rename : Nat → Fin v) (count : Nat) where
  equalities : EqualityPrefix (parameters := parameters) rename
  units : ∀ output : Fin parameters.decoder.roots.length, output.val < count →
    AvailableSubclause equalities.proofPrefix.state [negate (differenceLiteral rename output)]

def differenceStep (rename : Nat → Fin v) (count : Nat) (before : count < parameters.decoder.roots.length)
    (table : DifferenceTable (parameters := parameters) rename count) :
    DifferenceTable (parameters := parameters) rename (count + 1) := by
  let output : Fin parameters.decoder.roots.length := ⟨count, before⟩
  let original := SourceStageXor.xorRowsOriginal _ _ _ (observationDifferenceOriginalRows parameters rename output)
  let rows := original.afterTrace table.equalities.proofPrefix.state table.equalities.proofPrefix.steps
    table.equalities.proofPrefix.checked
  let actual := equalXor table.equalities.proofPrefix.state _ _ _ rows (table.equalities.pairs output)
  refine ⟨⟨table.equalities.proofPrefix.extend actual.state actual.steps actual.checked,
    fun query => (table.equalities.pairs query).afterTrace actual.state actual.steps actual.checked⟩, ?_⟩
  intro query bound
  if same : query = output then
    subst query
    exact actual.result
  else
    have earlier : query.val < count := by
      have different : query.val ≠ count := fun h => same (Fin.ext h)
      omega
    exact afterTrace (table.units query earlier) actual.state actual.steps actual.checked

def buildDifferences (rename : Nat → Fin v) (equalities : EqualityPrefix (parameters := parameters) rename) :
    (count : Nat) → count ≤ parameters.decoder.roots.length → DifferenceTable (parameters := parameters) rename count
  | 0, _ => ⟨equalities, fun output impossible => False.elim (Nat.not_lt_zero output.val impossible)⟩
  | count + 1, bound => differenceStep rename count (by omega)
      (buildDifferences rename equalities count (by omega))

def detectedInputs (parameters : Parameters) : List (Literal Nat) :=
  (List.finRange parameters.decoder.roots.length).map fun output =>
    (observationFinal parameters).slots (.internal (.difference output))

theorem finalFold (parameters : Parameters) :
    SourceController.compile parameters = (observationFinal parameters).foldNative (.internal .detected)
      .disjunction (detectedInputs parameters) := rfl

theorem differenceSlot (output : Fin parameters.decoder.roots.length) :
    sourceRoleMap parameters (.internal (.difference output)) =
      (observationFinal parameters).slots (.internal (.difference output)) := by
  rw [sourceRoleMap, finalFold]
  simp [Cursor.foldNative, Cursor.assign]

def detectedLiteral (rename : Nat → Fin v) :=
  mapLiteral rename (sourceRoleMap parameters (.internal .detected))

def detectionNegative (rename : Nat → Fin v)
    (table : DifferenceTable (parameters := parameters) rename parameters.decoder.roots.length) :
    SubclauseProjection table.equalities.proofPrefix.state [negate (detectedLiteral (parameters := parameters) rename)]
      (2 * (detectedInputs parameters).length + (detectedInputs parameters).length) := by
  let cursor := observationFinal parameters
  let inputs := detectedInputs parameters
  have retained : SourceFoldOwners.EntriesBefore
      (cursor.foldNative (.internal .detected) .disjunction inputs) (SourceController.compile parameters) := by
    rw [finalFold]
    exact .refl _
  let supply := SourceFoldOwners.foldRows rename cursor (.internal .detected) .disjunction inputs retained
  have root : detectedLiteral (parameters := parameters) rename =
      mapLiteral rename (SourceSerialFold.allocate .disjunction cursor.lastID inputs).output := by
    rw [detectedLiteral, sourceRoleMap, finalFold]
    simp [Cursor.foldNative, Cursor.assign, cursor, inputs]
  if empty : inputs = [] then
    have producer : (SourceSerialFold.allocate .disjunction cursor.lastID inputs).producers =
        [⟨(cursor.lastID + 1, true), .or []⟩] := by
      rw [empty, SourceSerialFold.allocate_empty]
      rfl
    let rows := supply ⟨0, by rw [producer]; simp⟩
    have unit : AvailableSubclause (initialState (relabel rename (formula parameters)))
        [negate (mapLiteral rename (cursor.lastID + 1, true))] := by
      have row := rows.row ⟨0, by simp only [producer, List.getElem_cons_zero]; change 0 < 1; decide⟩
      simpa only [producer, List.getElem_cons_zero, Bounded.Producer.rows, Gate.clauses,
        Rows.mapClause, List.nil_append, List.getElem_cons_zero, List.map_cons, List.map_nil, mapLiteral, negate, Std.Sat.Literal.negate] using ofRow row
    have output : detectedLiteral (parameters := parameters) rename = mapLiteral rename (cursor.lastID + 1, true) := by
      rw [root, empty, SourceSerialFold.allocate_empty]
    exact ⟨table.equalities.proofPrefix.state, [], rfl,
      output.symm ▸ afterTrace unit table.equalities.proofPrefix.state table.equalities.proofPrefix.steps
        table.equalities.proofPrefix.checked, by simp⟩
  else
    let tree := allocateOrForest (initialOrForest (state := initialState (relabel rename (formula parameters))) rename inputs)
      cursor.lastID empty supply
    let native := tree.afterTrace table.equalities.proofPrefix.state table.equalities.proofPrefix.steps
      table.equalities.proofPrefix.checked
    have units : ∀ input ∈ inputs.map (dualLiteral rename), AvailableSubclause table.equalities.proofPrefix.state [input] := by
      have handles : inputs.map (dualLiteral rename) =
          (List.finRange parameters.decoder.roots.length).map (fun output => negate (differenceLiteral rename output)) := by
        simp only [inputs, detectedInputs, List.map_map, Function.comp_def, dualLiteral, differenceLiteral, differenceSlot]
      rw [handles]
      exact TreeUnits.mappedUnit (List.finRange parameters.decoder.roots.length)
        (fun output => negate (differenceLiteral rename output)) []
        (fun output _ => table.units output output.isLt)
    let actual := TreeUnits.force native [] units
    refine ⟨actual.state, actual.steps, actual.checked, ?_, ?_⟩
    · simpa only [root, dualLiteral, List.nil_append] using actual.result
    · have count := actual.count
      have nodes := tree.nodes_leaves
      dsimp only [native] at count
      simp only [AndTree.afterTrace_nodes, List.length_map] at count nodes
      change actual.steps.length ≤ 2 * inputs.length + inputs.length
      omega

def detectedAssertion (rename : Nat → Fin v) :
    Rows.Available (initialState (relabel rename (formula parameters)))
      [detectedLiteral (parameters := parameters) rename] := by
  let equations := (SourceController.compile parameters).entries.flatMap fun entry => entry.producer.rows
  let position : Fin (formula parameters).clauses.size := ⟨equations.length + 3, by
    simp [SourceRows.formula_as_rows, ofClauses, assertions, equations]⟩
  have content : (formula parameters).clauses[position.val] =
      [sourceRoleMap parameters (.internal .detected)] := by
    simp [SourceRows.formula_as_rows, ofClauses, position, List.getElem_append, assertions, equations]
  refine ⟨position.val + 1, ?_, ?_⟩
  · simpa only [content, Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, detectedLiteral] using
      Rows.relabeled_row rename (formula parameters) position
  · simp only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map]
    exact Nat.succ_le_of_lt position.isLt

structure Refutation (rename : Nat → Fin v) where
  proofPrefix : SourcePrefix (parameters := parameters) rename
  empty : Rows.Available proofPrefix.state []

def refute (rename : Nat → Fin v) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    Refutation (parameters := parameters) rename := by
  let equalities := outputPrefix rename raw guarded unsat
  let differences := buildDifferences rename equalities parameters.decoder.roots.length (Nat.le_refl _)
  let negative := detectionNegative rename differences
  let current := differences.equalities.proofPrefix.extend negative.state negative.steps negative.checked
  let assertion := afterTrace (ofRow (detectedAssertion (parameters := parameters) rename))
    current.state current.steps current.checked
  let final := longMerge current.state (detectedLiteral (parameters := parameters) rename) [] [] negative.result assertion
  let result := longMerge_result current.state (detectedLiteral (parameters := parameters) rename) [] [] negative.result assertion
  have empty : result.clause = [] := by
    have subset := (longMerge_result current.state (detectedLiteral (parameters := parameters) rename) [] []
      negative.result assertion).subset
    cases shape : result.clause with
    | nil => rfl
    | cons head tail => exact False.elim (by have bad := subset head (by rw [shape]; simp); simpa using bad)
  have row : Rows.Available final.state [] :=
    ⟨result.row.id, by simpa only [empty] using result.row.present, result.row.bound⟩
  exact ⟨current.extend final.state final.steps (longMerge_run _ _ _ _ _ _), row⟩

def Refutation.trace {rename : Nat → Fin v} (result : Refutation (parameters := parameters) rename) : Trace v :=
  ⟨(formula parameters).clauses.size, result.proofPrefix.steps, result.empty.id⟩

theorem Refutation.checked {rename : Nat → Fin v} (result : Refutation (parameters := parameters) rename) :
    check (relabel rename (formula parameters)) result.trace = true := by
  have size : (relabel rename (formula parameters)).clauses.size = (formula parameters).clauses.size := by
    simp only [relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map]
  unfold check Refutation.trace
  rw [size, ite_eq_left rfl, result.proofPrefix.checked]
  simp only [result.empty.present]
  rfl

/-- Raw layout and absence of live-AND nodes are the supported family.
The finite node test is evaluated before the completeness construction. -/
def supported (parameters : Parameters) : Bool :=
  (parameters.layout == .raw) &&
    (List.finRange parameters.decoder.nodeCount).all (fun node => !(parameters.decoder.node node).isLiveAnd)

theorem supported_iff : supported parameters = true ↔ parameters.layout = .raw ∧ parameters.decoder.Guarded := by
  simp [supported, Controller.Decoder.DAG.Guarded, Controller.Decoder.Gate.IsGuarded]

/-- No fallback proof search participates in this total UNSAT constructor.
The UNSAT hypothesis is erased; all trace data come from the native macros. -/
def compile (rename : Nat → Fin v) (unsat : Unsatisfiable (formula parameters)) : Option (Trace v) :=
  if accepted : supported parameters = true then
    let hypotheses := supported_iff.mp accepted
    some (refute rename hypotheses.1 hypotheses.2 unsat).trace
  else none

theorem compile_complete (rename : Nat → Fin v) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    ∃ trace, compile rename unsat = some trace ∧ check (relabel rename (formula parameters)) trace = true := by
  have accepted := supported_iff.mpr ⟨raw, guarded⟩
  refine ⟨(refute rename raw guarded unsat).trace, ?_, (refute rename raw guarded unsat).checked⟩
  simp only [compile, accepted, ↓reduceDIte]

theorem compile_reject (rename : Nat → Fin v) (unsat : Unsatisfiable (formula parameters))
    (unsupported : supported parameters = false) : compile rename unsat = none := by
  simp [compile, unsupported]

theorem detector_none_of_unsat (raw : parameters.layout = .raw) (guarded : parameters.decoder.Guarded)
    (unsat : Unsatisfiable (formula parameters)) :
    parameters.decoder.detectSet parameters.buses parameters.bridge.target parameters.drive = none := by
  apply (parameters.decoder.detectSet_none_iff guarded _ _ _).mpr
  rintro ⟨drive, root, present, K, eligible, different⟩
  obtain ⟨output, same⟩ := List.get_of_mem present
  have absent := Decoder.source_unsat_noDiscrepancy parameters raw drive unsat Finset.univ
  exact different (by simpa only [Parameters.observations, same] using absent output (by simp) K eligible)

theorem unsat_of_detector_none (raw : parameters.layout = .raw) (guarded : parameters.decoder.Guarded)
    (none : parameters.decoder.detectSet parameters.buses parameters.bridge.target parameters.drive = none) :
    Unsatisfiable (formula parameters) := by
  have noDetect : ¬Controller.Physical.BridgeDetectable (b := parameters.buses)
      parameters.bridge parameters.drive parameters.decoder.observations :=
    (Controller.Physical.detectInput_none_iff parameters.bridge parameters.positiveBuses parameters.drive
      parameters.decoder guarded).mp (by simp only [Controller.Physical.detectInput, none, Option.map_none])
  intro sat
  obtain ⟨input, detected⟩ := (source_satisfiable_iff_physical_detection parameters raw).mp sat
  exact noDetect ⟨input, Controller.Physical.bridgeD parameters.bridge input, detected⟩

/-- The caller supplies only parameters and a finite literal renaming.
Unsupported families and detecting (SAT) instances return `none`. -/
def run (rename : Nat → Fin v) : Option (Trace v) :=
  if accepted : supported parameters = true then
    let hypotheses := supported_iff.mp accepted
    if noDetection : parameters.decoder.detectSet parameters.buses parameters.bridge.target parameters.drive = none then
      some (refute rename hypotheses.1 hypotheses.2
        (unsat_of_detector_none hypotheses.1 hypotheses.2 noDetection)).trace
    else none
  else none

theorem run_complete (rename : Nat → Fin v) (raw : parameters.layout = .raw)
    (guarded : parameters.decoder.Guarded) (unsat : Unsatisfiable (formula parameters)) :
    ∃ trace, run (parameters := parameters) rename = some trace ∧
      check (relabel rename (formula parameters)) trace = true := by
  have accepted := supported_iff.mpr ⟨raw, guarded⟩
  have none := detector_none_of_unsat raw guarded unsat
  refine ⟨(refute rename raw guarded unsat).trace, ?_, (refute rename raw guarded unsat).checked⟩
  simp only [run, accepted, none, ↓reduceDIte]

theorem run_reject (rename : Nat → Fin v) (unsupported : supported parameters = false) :
    run (parameters := parameters) rename = none := by simp [run, unsupported]

theorem run_checked (rename : Nat → Fin v) (trace : Trace v)
    (returned : run (parameters := parameters) rename = some trace) :
    check (relabel rename (formula parameters)) trace = true := by
  unfold run at returned
  split at returned
  · split at returned
    · cases Option.some.inj returned
      exact Refutation.checked _
    · simp at returned
  · simp at returned

def variableCount (parameters : Parameters) : Nat := (SourceController.compile parameters).lastID + 1

def canonicalRename (parameters : Parameters) : Nat → Fin (variableCount parameters) :=
  let count := variableCount parameters
  fun source => ⟨source % count, Nat.mod_lt _ (by unfold count variableCount; omega)⟩

theorem canonicalRename_allocated (source : Nat) (bounded : source ≤ (SourceController.compile parameters).lastID) :
    (canonicalRename parameters source).val = source := Nat.mod_eq_of_lt (by unfold variableCount; omega)

theorem source_literal_bounded (clause : Clause Nat) (present : clause ∈ (formula parameters).clauses)
    (literal : Literal Nat) (member : literal ∈ clause) : literal.1 ≤ (SourceController.compile parameters).lastID := by
  have split : clause ∈ (equationFormula parameters).clauses ∨
      clause ∈ (ofClauses ((assertions parameters).map fun l => [l])).clauses := by
    simpa only [formula, Controller.CNF.OrderedFormula.Internal.clauses_append, Array.mem_append] using present
  rcases split with equation | assertion
  · rw [← compile_source_rows_unconditional] at equation
    change clause ∈ ((SourceController.compile parameters).toState.circuit.formula.clauses.map
      (Controller.CNF.OrderedFormula.Clause.relabel SourceObservation.sourceID)) at equation
    obtain ⟨original, _, same⟩ := Array.mem_map.mp equation
    subst clause
    obtain ⟨old, _, same⟩ := List.mem_map.mp member
    subst literal
    change old.1.val + 1 ≤ _
    calc
      _ ≤ (SourceController.compile parameters).toState.count := Nat.succ_le_of_lt old.1.isLt
      _ = _ := Cursor.toState_count _
  · simp only [ofClauses, List.mem_toArray, List.mem_map] at assertion
    obtain ⟨original, listed, same⟩ := assertion
    subst clause
    have same : literal = original := by simpa using member
    subst literal
    exact (compile_assertions_bounded parameters original listed).2

def nativeFormula (parameters : Parameters) : FiniteFormula (variableCount parameters) :=
  let count := variableCount parameters
  relabel (fun source => ⟨source % count, Nat.mod_lt _ (by unfold count variableCount; omega)⟩) (formula parameters)

/-- Finite conversion preserves every ordered original clause and literal ID. -/
theorem nativeFormula_roundtrip : toNatFormula (nativeFormula parameters) = formula parameters := by
  change relabel Fin.val (relabel (canonicalRename parameters) (formula parameters)) = _
  unfold relabel
  rw [Controller.CNF.OrderedFormula.relabel_relabel]
  calc
    relabel (Fin.val ∘ canonicalRename parameters) (formula parameters) = relabel id (formula parameters) := by
      apply Controller.CNF.OrderedFormula.relabel_congr
      intro source membership
      obtain ⟨clause, present, member⟩ := membership
      rcases member with negative | positive
      · exact canonicalRename_allocated source (source_literal_bounded clause present (source, false) negative)
      · exact canonicalRename_allocated source (source_literal_bounded clause present (source, true) positive)
    _ = _ := Controller.CNF.OrderedFormula.relabel_id

def nativeCompile (parameters : Parameters) : Option (Trace (variableCount parameters)) :=
  let count := variableCount parameters
  run (parameters := parameters) (fun source => ⟨source % count, Nat.mod_lt _ (by unfold count variableCount; omega)⟩)

theorem nativeCompile_complete (raw : parameters.layout = .raw) (guarded : parameters.decoder.Guarded)
    (unsat : Unsatisfiable (formula parameters)) :
    ∃ trace, nativeCompile parameters = some trace ∧ check (nativeFormula parameters) trace = true :=
  run_complete (canonicalRename parameters) raw guarded unsat

theorem nativeCompile_checked (trace : Trace (variableCount parameters)) (returned : nativeCompile parameters = some trace) :
    check (nativeFormula parameters) trace = true := run_checked (canonicalRename parameters) trace returned

end Controller.NativeProof.Compiler
