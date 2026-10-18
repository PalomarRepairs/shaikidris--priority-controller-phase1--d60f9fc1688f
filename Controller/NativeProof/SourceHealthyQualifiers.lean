module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceHealthyMasks

@[expose] public section

/-! Healthy-singleton qualifier units constructed from original physical,
private NOT, guard OR, and qualifier-fold rows. -/
namespace Controller.NativeProof.SourceHealthyQualifiers
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceSuffixSelector
open Controller.NativeProof.SourceHealthyMasks
variable {parameters : Parameters} {v : Nat}

def targetFirstRequestAt (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) :
    SubclauseProjection prefixState.state
      [mapLiteral rename (sourceRoleMap parameters
        (.primary (.request parameters.firstBus parameters.bridge.target)))] 2 := by
  let channel := parameters.bridge.target
  let absent := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.absentBefore (parameters := parameters) channel).lastID + 1, true)
  let term := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.termBefore (parameters := parameters) channel).lastID + 1, true)
  let input := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.termBefore (parameters := parameters) channel).slots
      (.primary (.request parameters.firstBus channel)))
  let physical := Controller.NativeProof.SourceMismatchBranch.physicalUnitRow
    (parameters := parameters) rename ⟨0, by decide⟩
  let originalUnit : Rows.Available (initialState (relabel rename (formula parameters))) [negate absent] :=
    ⟨physical.id,
      (by simpa only [Controller.NativeProof.SourceMismatchSeed.targetUnit_at_occurrence rename drive]
        using physical.present), physical.bound⟩
  let unit := FoldProjection.afterTrace (ofRow originalUnit)
    prefixState.state prefixState.steps prefixState.checked
  have originalNot : AvailableSubclause (initialState (relabel rename (formula parameters))) [absent, term] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.absentRows rename channel).row
      ⟨0, by change 0 < 2; decide⟩)
    simpa only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil,
      Controller.NativeProof.SourceMismatchSeed.absentBefore_term_handle,
      absent, term, mapLiteral] using row
  let notRow := FoldProjection.afterTrace originalNot prefixState.state prefixState.steps prefixState.checked
  let first := longMerge prefixState.state absent [] [term] unit notRow
  have firstRun := longMerge_run prefixState.state absent [] [term] unit notRow
  have firstResult := longMerge_result prefixState.state absent [] [term] unit notRow
  have originalAnd : AvailableSubclause (initialState (relabel rename (formula parameters))) [negate term, input] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.termRows rename channel).row
      ⟨1, by change 1 < 3; decide⟩)
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
      negate, Std.Sat.Literal.negate] using row
  let kept := FoldProjection.afterTrace originalAnd prefixState.state prefixState.steps prefixState.checked
  let andRow := FoldProjection.afterTrace kept first.state first.steps firstRun
  let second := longMerge first.state term [input] [] andRow firstResult
  refine ⟨second.state, first.steps ++ second.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, firstRun]
    exact longMerge_run _ _ _ _ _ _
  · apply retarget (longMerge_result first.state term [input] [] andRow firstResult)
    intro literal member
    simpa only [input, channel, Controller.NativeProof.SourceMismatchSeed.termBefore_request,
      List.append_nil] using member
  · have one : first.steps.length ≤ 1 :=
      longMerge_count prefixState.state absent [] [term] unit notRow
    have two : second.steps.length ≤ 1 :=
      longMerge_count first.state term [input] [] andRow firstResult
    simp only [List.length_append]
    omega

def laterGuard (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    SubclauseProjection table.proofPrefix.state (context (parameters := parameters) rename ++
      [mapLiteral rename (guardHandle .healthy parameters.bridge.target
        (laterBuses (parameters := parameters))[position.val])]) 3 := by
  let bus := (laterBuses (parameters := parameters))[position.val]
  let guard := mapLiteral rename (guardHandle .healthy parameters.bridge.target bus)
  let flag := mapLiteral rename (flagInput .healthy bus)
  let request := targetRequest rename position
  let disjunction := guardOrFlagAt rename table.proofPrefix .healthy parameters.bridge.target bus
  have positive : AvailableSubclause disjunction.state
      (context (parameters := parameters) rename ++ [flag, guard]) :=
    retarget disjunction.result (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  have flagEq : flag = laterFlagOutput rename .healthy position := by
    dsimp only [flag, bus]
    rw [flagInput_busFlag]
    rfl
  have row : AvailableSubclause disjunction.state
      (context (parameters := parameters) rename ++ [negate request, guard]) := by
    let original := FoldProjection.afterTrace (guardRequestRow rename .healthy parameters.bridge.target bus)
      disjunction.state (table.proofPrefix.steps ++ disjunction.steps) (by
        rw [runSteps_append, table.proofPrefix.checked]
        exact disjunction.checked)
    apply retarget original
    intro literal member
    have requestEq : request = mapLiteral rename (requestHandle bus parameters.bridge.target) := by
      simp only [request, targetRequest, (termBefore_rootsExact .healthy position parameters.bridge.target).2,
        requestHandle, bus]
    simpa only [requestEq] using List.mem_append_right (context (parameters := parameters) rename) member
  let known := (table.flagRequests position position.isLt).forward.afterTrace
    disjunction.state disjunction.steps disjunction.checked
  have transfer : GuardedTransfer disjunction.state (context (parameters := parameters) rename) flag request := by
    simpa only [flagEq] using known
  let joined := TreeUnits.compose disjunction.state (context (parameters := parameters) rename) transfer (.derived row)
  let forced := TreeUnits.forceFromCases (root := guard) joined.state (context (parameters := parameters) rename) flag guard
    (FoldProjection.afterTrace positive joined.state joined.steps joined.checked) joined.result
  refine ⟨forced.state, (disjunction.steps ++ joined.steps) ++ forced.steps, ?_, forced.result, ?_⟩
  · simp only [runSteps_append, disjunction.checked, Option.bind_some, joined.checked, forced.checked]
  · have one := disjunction.count
    have two := joined.count
    have three := forced.count
    simp only [List.length_append]
    omega

def firstGuard (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (drive : parameters.drive = true) :
    SubclauseProjection prefixState.state (context (parameters := parameters) rename ++
      [mapLiteral rename (guardHandle .healthy parameters.bridge.target parameters.firstBus)]) 3 := by
  let request := targetFirstRequestAt rename prefixState drive
  let q := mapLiteral rename (requestHandle parameters.firstBus parameters.bridge.target)
  let g := mapLiteral rename (guardHandle .healthy parameters.bridge.target parameters.firstBus)
  let row := FoldProjection.afterTrace (guardRequestRow rename .healthy parameters.bridge.target parameters.firstBus)
    request.state (prefixState.steps ++ request.steps) (by
      rw [runSteps_append, prefixState.checked]
      exact request.checked)
  have unit : AvailableSubclause request.state [q] := by
    simpa only [q, requestHandle, sourceRoleMap, (compile_rootsExact parameters).2] using request.result
  let joined := longMerge request.state q [g] [] row unit
  refine ⟨joined.state, request.steps ++ joined.steps, ?_,
    retarget (longMerge_result _ _ _ _ _ _) (fun _ member => List.mem_append_right _ (by simpa using member)), ?_⟩
  · rw [runSteps_append, request.checked]
    exact longMerge_run _ _ _ _ _ _
  · have one := request.count
    have two : joined.steps.length ≤ 1 := longMerge_count _ _ _ _ _ _
    simp only [List.length_append]
    omega

structure GuardBank (rename : Nat → Fin v)
    (start : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (buses : List (Fin parameters.buses)) where
  table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length
  steps : List (Step v)
  checked : runSteps start.proofPrefix.state steps = some table.proofPrefix.state
  rows : ∀ bus ∈ buses, AvailableSubclause table.proofPrefix.state (context (parameters := parameters) rename ++
    [mapLiteral rename (guardHandle .healthy parameters.bridge.target bus)])

def guardAt (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (bus : Fin parameters.buses) :
    SubclauseProjection table.proofPrefix.state (context (parameters := parameters) rename ++
      [mapLiteral rename (guardHandle .healthy parameters.bridge.target bus)]) 3 :=
  if zero : bus.val = 0 then by
    have equal : bus = parameters.firstBus := Fin.ext zero
    exact equal ▸ firstGuard rename table.proofPrefix drive
  else by
    have actual := laterGuard rename table (laterPosition bus zero)
    simpa only [laterPosition_bus] using actual

def buildGuards (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (buses : List (Fin parameters.buses)) :
    GuardBank (parameters := parameters) rename table buses :=
  match buses with
  | [] => ⟨table, [], rfl, fun _ member => False.elim (List.not_mem_nil member)⟩
  | bus :: rest => by
    let one := guardAt rename table drive bus
    let next := table.afterTrace one.state one.steps one.checked
    let tail := buildGuards rename next drive rest
    refine ⟨tail.table, one.steps ++ tail.steps, ?_, ?_⟩
    · rw [runSteps_append, one.checked]
      exact tail.checked
    · intro query member
      by_cases equal : query = bus
      · subst query
        exact FoldProjection.afterTrace one.result tail.table.proofPrefix.state tail.steps tail.checked
      · exact tail.rows query ((List.mem_cons.mp member).resolve_left equal)

def targetQualifierInputs (parameters : Parameters) : List (Literal Nat) :=
  ((qualifierGuarded .healthy parameters.bridge.target).slots (.primary (.enable parameters.bridge.target)) ::
    (List.finRange parameters.buses).map fun bus =>
      (qualifierGuarded .healthy parameters.bridge.target).slots (.internal (.qualifierGuard .healthy bus parameters.bridge.target)))

def targetQualifierUnits (rename : Nat → Fin v)
    {table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length}
    (guards : GuardBank rename table (List.finRange parameters.buses)) (drive : parameters.drive = true) : ∀ input ∈ (targetQualifierInputs parameters).map (mapLiteral rename),
      AvailableSubclause (targetEnableAt rename guards.table.proofPrefix drive).state (context (parameters := parameters) rename ++ [input]) := by
  let enabled := targetEnableAt rename guards.table.proofPrefix drive
  let inputs := targetQualifierInputs parameters
  intro input member
  let enable := mapLiteral rename ((qualifierGuarded .healthy parameters.bridge.target).slots
    (.primary (.enable parameters.bridge.target)))
  by_cases equal : input = enable
  · subst input
    apply retarget enabled.result
    intro literal member
    have roots := (qualifierGuarded_roots .healthy parameters.bridge.target).1 parameters.bridge.target
    simpa only [enable, roots, sourceRoleMap, (compile_rootsExact parameters).1] using
      List.mem_append_right (context (parameters := parameters) rename) member
  · have rest : input ∈ (List.finRange parameters.buses).map
        (fun bus => mapLiteral rename (guardHandle .healthy parameters.bridge.target bus)) := by
      simpa only [inputs, List.map_cons, List.mem_cons, List.map_map,
        qualifierGuarded_guard_handle, Function.comp_def] using (List.mem_cons.mp member).resolve_left equal
    exact TreeUnits.mappedUnit (List.finRange parameters.buses) _ (context (parameters := parameters) rename)
      (fun bus listed => FoldProjection.afterTrace (guards.rows bus listed) enabled.state enabled.steps enabled.checked)
      input rest

def targetQualifier (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) :
    SubclauseProjection table.proofPrefix.state
      (context (parameters := parameters) rename ++ [Controller.NativeProof.SourceQualifierSchedule.qualifierOutput rename .healthy parameters.bridge.target])
      ((buildGuards rename table drive (List.finRange parameters.buses)).steps.length +
        2 + 2 * (qualifierTree rename .healthy parameters.bridge.target).nodes + parameters.buses + 1) := by
  let guards := buildGuards rename table drive (List.finRange parameters.buses)
  let enabled := targetEnableAt rename guards.table.proofPrefix drive
  let prefixState := guards.table.proofPrefix.extend enabled.state enabled.steps enabled.checked
  let tree := (qualifierTree rename .healthy parameters.bridge.target).afterTrace
    enabled.state prefixState.steps prefixState.checked
  let inputs := targetQualifierInputs parameters
  let units := targetQualifierUnits rename guards drive
  let forced := TreeUnits.force tree (context (parameters := parameters) rename) units
  refine ⟨forced.state, (guards.steps ++ enabled.steps) ++ forced.steps, ?_, forced.result, ?_⟩
  · have guardsRun : runSteps table.proofPrefix.state guards.steps = some guards.table.proofPrefix.state := guards.checked
    simp only [runSteps_append, guardsRun, Option.bind_some, enabled.checked, forced.checked]
  · have enableCount := enabled.count
    have nodeCount : tree.nodes = (qualifierTree rename .healthy parameters.bridge.target).nodes :=
      AndTree.afterTrace_nodes _ _ _ _
    have forceCount : forced.steps.length ≤ 2 * (qualifierTree rename .healthy parameters.bridge.target).nodes + parameters.buses + 1 := by
      calc
        forced.steps.length ≤ 2 * tree.nodes + (inputs.map (mapLiteral rename)).length := forced.count
        _ = _ := by
          rw [nodeCount]
          simp only [inputs, targetQualifierInputs, List.length_map, List.length_cons, List.length_finRange]
          omega
    change (guards.steps ++ enabled.steps ++ forced.steps).length ≤ guards.steps.length +
      2 + 2 * (qualifierTree rename .healthy parameters.bridge.target).nodes + parameters.buses + 1
    simp only [List.length_append]
    omega

open Controller.NativeProof.SourceQualifierSchedule
open Controller.NativeProof.SourceQualifierOccurrences
open Controller.NativeProof.LocalUnitCases

def otherQualifier (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target) :
    SubclauseProjection table.proofPrefix.state
      (context (parameters := parameters) rename ++ [negate (qualifierOutput rename .healthy channel)])
      (2 * (qualifierTree rename .healthy channel).nodes + 63) := by
  let prefixState := table.proofPrefix
  let tree := (qualifierTree rename .healthy channel).afterTrace prefixState.state prefixState.steps prefixState.checked
  let q := qualifierOutput rename .healthy channel
  let e := mapLiteral rename ((qualifierGuarded .healthy channel).slots (.primary (.enable channel)))
  let r := mapLiteral rename (requestHandle parameters.firstBus channel)
  let g := mapLiteral rename (guardHandle .healthy channel parameters.firstBus)
  let nf := mapLiteral rename (negatedHandle .healthy parameters.firstBus)
  let term := mapLiteral rename ((SourceMismatchSeed.termBefore (parameters := parameters) channel).lastID + 1, true)
  let absent := mapLiteral rename ((SourceMismatchSeed.absentBefore (parameters := parameters) channel).lastID + 1, true)
  let projected := nonunaryTreeInputs tree (by
    simp only [List.length_map, List.length_cons, List.length_finRange]
    have positive := parameters.positiveBuses
    omega)
  have enableMember : e ∈ ((qualifierGuarded .healthy channel).slots (.primary (.enable channel)) ::
      (List.finRange parameters.buses).map (fun bus =>
        (qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy bus channel)))).map (mapLiteral rename) := by simp [e]
  have guardMember : g ∈ ((qualifierGuarded .healthy channel).slots (.primary (.enable channel)) ::
      (List.finRange parameters.buses).map (fun bus =>
        (qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy bus channel)))).map (mapLiteral rename) := by
    simp only [List.map_cons, List.mem_cons, List.map_map, qualifierGuarded_guard_handle]
    exact Or.inr (List.mem_map.mpr ⟨parameters.firstBus, List.mem_finRange _, rfl⟩)
  let qe : AvailableSubclause projected.state [negate q, e] := projected.results e enableMember
  let qg : AvailableSubclause projected.state [negate q, g] := projected.results g guardMember
  have notFlag : AvailableSubclause projected.state (context (parameters := parameters) rename ++ [negate nf]) := by
    let rows := qualifierNotRows rename .healthy parameters.firstBus prefixState
    let original := FoldProjection.afterTrace rows.negative projected.state projected.steps projected.checked
    apply retarget original
    intro literal member
    simp only [rows, qualifierNotRows, negatedHandle, nf, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · exact List.mem_append_right _ (List.mem_singleton.mpr same)
    · subst literal
      apply List.mem_append_left
      rw [show (negateBefore .healthy parameters.firstBus).slots (.internal (.flag .healthy parameters.firstBus)) =
        sourceRoleMap parameters (.internal (.flag .healthy parameters.firstBus)) from firstFlagInput_eq_sourceRoleMap .healthy]
      exact List.mem_cons_self
  have longGuard : AvailableSubclause projected.state [negate g, nf, r] := by
    let original := ofRow ((guardRows rename .healthy channel parameters.firstBus).row ⟨2, by change 2 < 3; decide⟩)
    have row : AvailableSubclause prefixState.state [negate g, nf, r] := by
      simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, List.map_append, List.append_nil,
        guardHandle, guardBefore_negated, (guardBefore_roots .healthy channel parameters.firstBus).2,
        g, nf, r, requestHandle, mapLiteral, negate, Std.Sat.Literal.negate] using
        FoldProjection.afterTrace original prefixState.state prefixState.steps prefixState.checked
    exact FoldProjection.afterTrace row projected.state projected.steps projected.checked
  have negativeTerm : AvailableSubclause projected.state [negate absent, negate term] := by
    let original := ofRow ((SourceMismatchSeed.absentRows rename channel).row ⟨1, by change 1 < 2; decide⟩)
    have row : AvailableSubclause prefixState.state [negate absent, negate term] := by
      simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, SourceMismatchSeed.absentBefore_term_handle,
        term, absent, mapLiteral, negate, Std.Sat.Literal.negate] using
        FoldProjection.afterTrace original prefixState.state prefixState.steps prefixState.checked
    exact FoldProjection.afterTrace row projected.state projected.steps projected.checked
  have longTerm : AvailableSubclause projected.state [term, negate e, negate r] := by
    let original := ofRow ((SourceMismatchSeed.termRows rename channel).row ⟨2, by change 2 < 3; decide⟩)
    have row : AvailableSubclause prefixState.state [term, negate e, negate r] := by
      simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, List.map_append, List.append_nil,
        term, e, r, requestHandle, SourceMismatchSeed.termBefore_enable, SourceMismatchSeed.termBefore_request,
        sourceRoleMap, (compile_rootsExact parameters).1, (compile_rootsExact parameters).2,
        (qualifierGuarded_roots .healthy channel).1, mapLiteral, negate, Std.Sat.Literal.negate] using
        FoldProjection.afterTrace original prefixState.state prefixState.steps prefixState.checked
    exact FoldProjection.afterTrace row projected.state projected.steps projected.checked
  have absenceUnit : AvailableSubclause projected.state (context (parameters := parameters) rename ++ [absent]) := by
    simpa only [absent, SourceMismatchSeed.firstArrays_absent_handle] using
      FoldProjection.afterTrace (table.firstAbsent channel different) projected.state projected.steps projected.checked
  let premises : List (Premise projected.state (context (parameters := parameters) rename)) :=
    [XorUnits.contextual qe, XorUnits.contextual qg, ⟨[negate nf], notFlag⟩,
      XorUnits.contextual longGuard, XorUnits.contextual negativeTerm,
      XorUnits.contextual longTerm, ⟨[absent], absenceUnit⟩]
  have entails : EntailsUnit premises (negate q) := by
    intro values all
    have a := all (XorUnits.contextual qe) (by simp [premises])
    have b := all (XorUnits.contextual qg) (by simp [premises])
    have c := all ⟨[negate nf], notFlag⟩ (by simp [premises])
    have d := all (XorUnits.contextual longGuard) (by simp [premises])
    have f := all (XorUnits.contextual negativeTerm) (by simp [premises])
    have h := all (XorUnits.contextual longTerm) (by simp [premises])
    have j := all ⟨[absent], absenceUnit⟩ (by simp [premises])
    simp only [XorUnits.contextual, literalHolds_negate, clauseHolds_cons, clauseHolds_nil, or_false] at a b c d f h j ⊢
    tauto
  have covers : Covers premises [negate q] [e.1, r.1, g.1, nf.1, term.1, absent.1] := by
    intro premise member literal present
    simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [XorUnits.contextual, List.mem_cons, List.not_mem_nil, or_false] at present <;>
      rcases present with rfl | rfl | rfl <;>
      simp [labelsOf, negate, Std.Sat.Literal.negate]
  let forced := unitUsing projected.state (context (parameters := parameters) rename) premises (negate q)
    entails [e.1, r.1, g.1, nf.1, term.1, absent.1] covers
  refine ⟨forced.state, projected.steps ++ forced.steps, ?_, forced.result, ?_⟩
  · rw [runSteps_append, projected.checked]
    exact forced.checked
  · have projectedCount : projected.steps.length ≤ 2 * (qualifierTree rename .healthy channel).nodes := by
      calc
        projected.steps.length ≤ 2 * tree.nodes := projected.count
        _ = _ := congrArg (2 * ·) (AndTree.afterTrace_nodes _ _ _ _)
    have forcedCount : forced.steps.length ≤ 63 := by simpa using forced.count
    simp only [List.length_append] at *
    omega

structure QualifierBank (rename : Nat → Fin v)
    (start : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (channels : List (Fin parameters.channels)) where
  table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length
  steps : List (Step v)
  checked : runSteps start.proofPrefix.state steps = some table.proofPrefix.state
  rows : ∀ channel ∈ channels, AvailableSubclause table.proofPrefix.state (context (parameters := parameters) rename ++
    [valueLiteral (qualifierOutput rename .healthy channel) (decide (channel = parameters.bridge.target))])

def qualifierBudgetAt (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (channel : Fin parameters.channels) : Nat :=
  if channel = parameters.bridge.target then
      (buildGuards rename table drive (List.finRange parameters.buses)).steps.length +
        2 + 2 * (qualifierTree rename .healthy parameters.bridge.target).nodes + parameters.buses + 1
      else 2 * (qualifierTree rename .healthy channel).nodes + 63

def qualifierAt (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (channel : Fin parameters.channels) :
    SubclauseProjection table.proofPrefix.state (context (parameters := parameters) rename ++
      [valueLiteral (qualifierOutput rename .healthy channel) (decide (channel = parameters.bridge.target))])
      (qualifierBudgetAt rename table drive channel) := by
  let budget := qualifierBudgetAt rename table drive channel
  exact if same : channel = parameters.bridge.target then by
    subst channel
    simpa only [budget, qualifierBudgetAt, ite_eq_left rfl, decide_true, valueLiteral, ite_true] using targetQualifier rename table drive
  else by
    simpa only [budget, qualifierBudgetAt, ite_eq_right same, decide_eq_false same, valueLiteral, Bool.false_eq_true, ite_false] using
      otherQualifier rename table channel same

def buildQualifiers (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (channels : List (Fin parameters.channels)) :
    QualifierBank (parameters := parameters) rename table channels :=
  match channels with
  | [] => ⟨table, [], rfl, fun _ member => False.elim (List.not_mem_nil member)⟩
  | channel :: rest => by
    let one := qualifierAt rename table drive channel
    let next := table.afterTrace one.state one.steps one.checked
    let tail := buildQualifiers rename next drive rest
    refine ⟨tail.table, one.steps ++ tail.steps, ?_, ?_⟩
    · rw [runSteps_append, one.checked]
      exact tail.checked
    · intro query member
      by_cases equal : query = channel
      · subst query
        exact FoldProjection.afterTrace one.result tail.table.proofPrefix.state tail.steps tail.checked
      · exact tail.rows query ((List.mem_cons.mp member).resolve_left equal)

def allQualifiers (rename : Nat → Fin v) (drive : parameters.drive = true) :=
  buildQualifiers rename (allMasks rename drive) drive (List.finRange parameters.channels)

theorem buildGuardsSize (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (buses : List (Fin parameters.buses)) :
    (buildGuards rename table drive buses).steps.length ≤ 3 * buses.length := by
  induction buses generalizing table with
  | nil => simp [buildGuards]
  | cons bus rest ih =>
    have current := (guardAt rename table drive bus).count
    have later := ih (table.afterTrace (guardAt rename table drive bus).state
      (guardAt rename table drive bus).steps (guardAt rename table drive bus).checked)
    simp only [buildGuards, List.length_append, List.length_cons]
    omega

theorem qualifierTreeSize (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    (qualifierTree (parameters := parameters) rename side channel).nodes = parameters.buses := by
  have actual := (qualifierTree (parameters := parameters) rename side channel).nodes_leaves
  simp only [List.length_cons, List.length_map, List.length_finRange] at actual
  omega

theorem qualifierAtSize (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (channel : Fin parameters.channels) :
    (qualifierAt rename table drive channel).steps.length ≤ 6 * parameters.buses + 63 := by
  have actual := (qualifierAt rename table drive channel).count
  have guards := buildGuardsSize rename table drive (List.finRange parameters.buses)
  simp only [List.length_finRange] at guards
  simp only [qualifierBudgetAt, qualifierTreeSize] at actual
  split at actual <;> omega

theorem buildQualifiersSize (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (channels : List (Fin parameters.channels)) :
    (buildQualifiers rename table drive channels).steps.length ≤
      channels.length * (6 * parameters.buses + 63) := by
  induction channels generalizing table with
  | nil => simp [buildQualifiers]
  | cons channel rest ih =>
    have current := qualifierAtSize rename table drive channel
    have later := ih (table.afterTrace (qualifierAt rename table drive channel).state
      (qualifierAt rename table drive channel).steps (qualifierAt rename table drive channel).checked)
    simp only [buildQualifiers, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem buildQualifiers_prefix (rename : Nat → Fin v)
    (table : Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (channels : List (Fin parameters.channels)) :
    (buildQualifiers rename table drive channels).table.proofPrefix.steps =
      table.proofPrefix.steps ++ (buildQualifiers rename table drive channels).steps := by
  induction channels generalizing table with
  | nil => simp [buildQualifiers]
  | cons channel rest ih =>
    let one := qualifierAt rename table drive channel
    let next := table.afterTrace one.state one.steps one.checked
    have later := ih next
    simpa only [buildQualifiers, next, one, Table.afterTrace, SourcePrefix.extend, List.append_assoc] using later

end Controller.NativeProof.SourceHealthyQualifiers
