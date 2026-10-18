module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperHealthyMasks

@[expose] public section

/-! Retained native origins for healthy singleton qualifier construction. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceSuffixSelector
open Controller.NativeProof.SourceHealthyMasks Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceFoldProvenance
open Controller.NativeProof.SourceQualifierOccurrences Controller.NativeProof.SourceSlotFrames
variable {parameters : Parameters} {v : Nat}

theorem targetFirstRequestAt_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState (SourceHealthyQualifiers.targetFirstRequestAt rename prefixState drive) := by
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
  let originalNot : AvailableSubclause (initialState (relabel rename (formula parameters))) [absent, term] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.absentRows rename channel).row
      ⟨0, by change 0 < 2; decide⟩)
    simpa only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil,
      Controller.NativeProof.SourceMismatchSeed.absentBefore_term_handle,
      absent, term, mapLiteral] using row
  let notRow := FoldProjection.afterTrace originalNot prefixState.state prefixState.steps prefixState.checked
  let first := longMerge prefixState.state absent [] [term] unit notRow
  have firstRun := longMerge_run prefixState.state absent [] [term] unit notRow
  let firstResult := longMerge_result prefixState.state absent [] [term] unit notRow
  let originalAnd : AvailableSubclause (initialState (relabel rename (formula parameters))) [negate term, input] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.termRows rename channel).row
      ⟨1, by change 1 < 3; decide⟩)
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
      negate, Std.Sat.Literal.negate] using row
  let kept := FoldProjection.afterTrace originalAnd prefixState.state prefixState.steps prefixState.checked
  let andRow := FoldProjection.afterTrace kept first.state first.steps firstRun
  let second := longMerge first.state term [input] [] andRow firstResult
  have notId : originalNot.row.id =
      ((Controller.NativeProof.SourceMismatchSeed.absentRows rename channel).row
        ⟨0, by change 0 < 2; decide⟩).id := by
    dsimp only [originalNot]
    apply subclause_cast_id
    simp only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil,
      Controller.NativeProof.SourceMismatchSeed.absentBefore_term_handle,
      absent, term, mapLiteral]
  have andId : originalAnd.row.id =
      ((Controller.NativeProof.SourceMismatchSeed.termRows rename channel).row
        ⟨1, by change 1 < 3; decide⟩).id := by
    dsimp only [originalAnd]
    refine (subclause_indices_mpr_id ?_ ?_ _ _).trans ?_
    · rfl
    · simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
        negate, Std.Sat.Literal.negate]
    · apply subclause_indices_cast_id
      · rfl
      · simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
        negate, Std.Sat.Literal.negate]
  have unitOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps unit.row.id :=
    Or.inl (Controller.NativeProof.SourceMismatchBranch.physicalUnit_allowed rename ⟨0, by decide⟩)
  have notOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps notRow.row.id := by
    change Controller.NativeProof.SourceMismatchHandles.ResultOrigin _ _ _ originalNot.row.id
    rw [notId]
    exact Or.inl (Controller.NativeProof.SourceMismatchSeed.absentRows_allowed rename channel
      ⟨0, by change 0 < 2; decide⟩)
  have firstSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps prefixState.state absent [] [term] unit notRow supported
    (allowed_native_count_le rename) (prefix_native_count_le rename prefixState) unitOrigin notOrigin
  have andOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ first.steps) andRow.row.id := by
    change Controller.NativeProof.SourceMismatchHandles.ResultOrigin _ _ _ originalAnd.row.id
    rw [andId]
    exact Or.inl (Controller.NativeProof.SourceMismatchSeed.termRows_allowed rename channel
      ⟨1, by change 1 < 3; decide⟩)
  have firstBound := Nat.le_trans (prefix_native_count_le rename prefixState)
    (runSteps_lastId_le firstRun)
  have secondSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ first.steps) first.state term [input] [] andRow firstResult
    firstSupport.1 (allowed_native_count_le rename) firstBound andOrigin firstSupport.2
  simpa only [ProjectionOriginalSupport, SourceHealthyQualifiers.targetFirstRequestAt, List.append_assoc, retarget,
    channel, absent, term, input, physical, originalUnit, unit, originalNot, notRow,
    first, firstRun, firstResult, originalAnd, kept, andRow, second] using secondSupport


theorem healthyFirstGuard_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) (drive : parameters.drive = true)
    (supported : PrefixOriginalSupport rename prefixState) :
    ProjectionOriginalSupport rename prefixState (SourceHealthyQualifiers.firstGuard rename prefixState drive) := by
  let request := SourceHealthyQualifiers.targetFirstRequestAt rename prefixState drive
  let q := mapLiteral rename (requestHandle parameters.firstBus parameters.bridge.target)
  let g := mapLiteral rename (guardHandle .healthy parameters.bridge.target parameters.firstBus)
  let row := FoldProjection.afterTrace (guardRequestRow rename .healthy parameters.bridge.target parameters.firstBus)
    request.state (prefixState.steps ++ request.steps) (by
      rw [runSteps_append, prefixState.checked]
      exact request.checked)
  let unit : AvailableSubclause request.state [q] := by
    simpa only [q, requestHandle, sourceRoleMap, (compile_rootsExact parameters).2] using request.result
  let joined := longMerge request.state q [g] [] row unit
  have requestOrigins := targetFirstRequestAt_origins rename prefixState drive supported
  have unitId : unit.row.id = request.result.row.id := by
    dsimp only [unit]
    apply subclause_cast_id
    simp only [q, requestHandle, sourceRoleMap, (compile_rootsExact parameters).2]
  have unitOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ request.steps) unit.row.id := by
    rw [unitId]
    exact requestOrigins.2
  have rowOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ request.steps) row.row.id :=
    Or.inl (guardRequestRow_allowed rename .healthy parameters.bridge.target parameters.firstBus)
  let current := prefixState.extend request.state request.steps request.checked
  have actual := longMerge_supported (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    current.steps request.state q [g] [] row unit requestOrigins.1
    (allowed_native_count_le rename) (prefix_native_count_le rename current) rowOrigin unitOrigin
  simpa only [ProjectionOriginalSupport, SourceHealthyQualifiers.firstGuard, retarget,
    request, q, g, row, unit, joined, current, SourcePrefix.extend, List.append_assoc] using actual

theorem guardedTransfer_indices_mpr_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {beforeContext afterContext : Clause (Fin v)}
    {beforeInput afterInput beforeOutput afterOutput : Literal (Fin v)}
    (contextEqual : beforeContext = afterContext)
    (inputEqual : beforeInput = afterInput) (outputEqual : beforeOutput = afterOutput)
    (typeEqual : GuardedTransfer prefixState.state beforeContext beforeInput beforeOutput =
      GuardedTransfer prefixState.state afterContext afterInput afterOutput)
    (value : GuardedTransfer prefixState.state afterContext afterInput afterOutput)
    (origins : ControllerOrigins.GuardedTransferOrigin rename prefixState value) :
    ControllerOrigins.GuardedTransferOrigin rename prefixState (Eq.mpr typeEqual value) := by
  subst afterContext
  subst afterInput
  subst afterOutput
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  exact origins

theorem healthyLaterGuard_origins (rename : Nat → Fin v)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (position : Fin (laterBuses (parameters := parameters)).length)
    (origins : HealthyMaskOrigins rename table) :
    ProjectionOriginalSupport rename table.proofPrefix (SourceHealthyQualifiers.laterGuard rename table position) := by
  let bus := (laterBuses (parameters := parameters))[position.val]
  let guard := mapLiteral rename (guardHandle .healthy parameters.bridge.target bus)
  let flag := mapLiteral rename (flagInput .healthy bus)
  let request := targetRequest rename position
  let disjunction := guardOrFlagAt rename table.proofPrefix .healthy parameters.bridge.target bus
  let positive : AvailableSubclause disjunction.state
      (context (parameters := parameters) rename ++ [flag, guard]) :=
    retarget disjunction.result (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  have flagEq : flag = laterFlagOutput rename .healthy position := by
    dsimp only [flag, bus]
    rw [flagInput_busFlag]
    rfl
  let row : AvailableSubclause disjunction.state
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
  let transfer : GuardedTransfer disjunction.state (context (parameters := parameters) rename) flag request := by
    simpa only [flagEq] using known
  let joined := TreeUnits.compose disjunction.state (context (parameters := parameters) rename) transfer (.derived row)
  let forced := TreeUnits.forceFromCases (root := guard) joined.state (context (parameters := parameters) rename) flag guard
    (FoldProjection.afterTrace positive joined.state joined.steps joined.checked) joined.result
  let current := table.proofPrefix.extend disjunction.state disjunction.steps disjunction.checked
  have disjunctionOrigins := guardOrFlagAt_supported rename table.proofPrefix .healthy parameters.bridge.target bus origins.supported
  have knownOrigin := ControllerOrigins.GuardedTransferOrigin.afterTrace rename table.proofPrefix
    (table.flagRequests position position.isLt).forward (origins.flagRequests position position.isLt).1
    disjunction.state disjunction.steps disjunction.checked
  have transferOrigin : ControllerOrigins.GuardedTransferOrigin rename current transfer := by
    dsimp only [transfer]
    apply guardedTransfer_indices_mpr_origins rename current rfl flagEq rfl _ _
    exact knownOrigin
  have rowOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps row.row.id :=
    Or.inl (guardRequestRow_allowed rename .healthy parameters.bridge.target bus)
  have joinedOrigins := ControllerOrigins.compose_supported rename current (context (parameters := parameters) rename)
    flag request guard transfer (.derived row) disjunctionOrigins.1 transferOrigin rowOrigin
  let next := current.extend joined.state joined.steps joined.checked
  have positiveOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) next.steps
      (FoldProjection.afterTrace positive joined.state joined.steps joined.checked).row.id :=
    resultOrigin_append_right _ _ current.steps joined.steps _ disjunctionOrigins.2
  have actual := ControllerOrigins.forceFromCases_supported rename next (context (parameters := parameters) rename)
    flag guard (FoldProjection.afterTrace positive joined.state joined.steps joined.checked) joined.result
    joinedOrigins.1 positiveOrigin joinedOrigins.2
  simpa only [ProjectionOriginalSupport, SourceHealthyQualifiers.laterGuard, id,
    bus, guard, flag, request, disjunction, positive, row, known, transfer, joined, forced,
    current, next, SourcePrefix.extend, List.append_assoc] using actual

theorem projection_dite_result_id {state : State v} {clause : Clause (Fin v)} {budget : Nat}
    (condition : Prop) [Decidable condition]
    (yes : condition → SubclauseProjection state clause budget)
    (no : ¬condition → SubclauseProjection state clause budget) :
    ((dite condition yes no).result).row.id =
      dite condition (fun proof => ((yes proof).result).row.id) (fun proof => ((no proof).result).row.id) := by
  by_cases proof : condition
  · calc
      _ = ((yes proof).result).row.id :=
        congrArg (fun projection : SubclauseProjection state clause budget => projection.result.row.id) (dite_eq_left proof)
      _ = _ := by symm; exact dite_eq_left proof
  · calc
      _ = ((no proof).result).row.id :=
        congrArg (fun projection : SubclauseProjection state clause budget => projection.result.row.id) (dite_eq_right proof)
      _ = _ := by symm; exact dite_eq_right proof

theorem healthyGuardAt_origins (rename : Nat → Fin v)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (bus : Fin parameters.buses) (origins : HealthyMaskOrigins rename table) :
    ProjectionOriginalSupport rename table.proofPrefix (SourceHealthyQualifiers.guardAt rename table drive bus) := by
  by_cases zero : bus.val = 0
  · have equal : bus = parameters.firstBus := Fin.ext zero
    subst bus
    simpa only [SourceHealthyQualifiers.guardAt, id, ProjectionOriginalSupport,
      projection_dite_result_id, dite_eq_left zero] using
      healthyFirstGuard_origins rename table.proofPrefix drive origins.supported
  · unfold SourceHealthyQualifiers.guardAt
    rw [dite_eq_right zero]
    apply ControllerOrigins.projection_indices_mp_supported rename table.proofPrefix
      (by simp only [laterPosition_bus]) rfl _ _
    exact healthyLaterGuard_origins rename table (laterPosition bus zero) origins

structure GuardBankOrigins (rename : Nat → Fin v)
    (start : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    {buses : List (Fin parameters.buses)}
    (bank : SourceHealthyQualifiers.GuardBank rename start buses) : Prop where
  table : HealthyMaskOrigins rename bank.table
  sameSteps : bank.table.proofPrefix.steps = start.proofPrefix.steps ++ bank.steps
  rows : ∀ bus member, ControllerRowOrigin rename bank.table.proofPrefix (bank.rows bus member)

theorem healthyBuildGuards_origins (rename : Nat → Fin v)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (buses : List (Fin parameters.buses)) (origins : HealthyMaskOrigins rename table) :
    GuardBankOrigins rename table (SourceHealthyQualifiers.buildGuards rename table drive buses) := by
  induction buses generalizing table with
  | nil =>
    refine ⟨origins, ?_, ?_⟩
    · simp only [SourceHealthyQualifiers.buildGuards, List.append_nil]
    · intro bus member; simp at member
  | cons bus rest ih =>
    let one := SourceHealthyQualifiers.guardAt rename table drive bus
    let next := table.afterTrace one.state one.steps one.checked
    let tailBank := SourceHealthyQualifiers.buildGuards rename next drive rest
    have oneOrigins := healthyGuardAt_origins rename table drive bus origins
    have nextOrigins := HealthyMaskOrigins.afterTrace rename table origins one.state one.steps one.checked oneOrigins.1
    have tail := ih next nextOrigins
    refine ⟨tail.table, ?_, ?_⟩
    · change tailBank.table.proofPrefix.steps = table.proofPrefix.steps ++ (one.steps ++ tailBank.steps)
      rw [tail.sameSteps]
      simp only [next, SourceHealthyMasks.Table.afterTrace, SourcePrefix.extend, List.append_assoc]
      rfl
    · intro query member
      by_cases equal : query = bus
      · subst query
        have indexEqual : ((SourceHealthyQualifiers.buildGuards rename table drive (bus :: rest)).rows bus member).row.id =
            one.result.row.id := by
          simp only [SourceHealthyQualifiers.buildGuards, id, SourceMixedSchedule.subclause_dite_id,
            dite_true, dite_eq_left rfl, afterTrace]
          rfl
        unfold ControllerRowOrigin
        rw [indexEqual]
        change ResultOrigin (formula parameters).clauses.size
          (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) tailBank.table.proofPrefix.steps _
        rw [tail.sameSteps]
        exact resultOrigin_append_right _ _ (table.proofPrefix.steps ++ one.steps) tailBank.steps _ oneOrigins.2
      · have indexEqual : ((SourceHealthyQualifiers.buildGuards rename table drive (bus :: rest)).rows query member).row.id =
            (tailBank.rows query ((List.mem_cons.mp member).resolve_left equal)).row.id := by
          simp only [SourceHealthyQualifiers.buildGuards, id, SourceMixedSchedule.subclause_dite_id,
            dite_eq_right equal, tailBank, next, one]
        unfold ControllerRowOrigin
        rw [indexEqual]
        exact tail.rows query ((List.mem_cons.mp member).resolve_left equal)

theorem targetQualifierUnits_origins (rename : Nat → Fin v)
    {table : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length}
    (guards : SourceHealthyQualifiers.GuardBank rename table (List.finRange parameters.buses))
    (drive : parameters.drive = true) (origins : GuardBankOrigins rename table guards) :
    ∀ input member, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (guards.table.proofPrefix.steps ++ (targetEnableAt rename guards.table.proofPrefix drive).steps)
      (SourceHealthyQualifiers.targetQualifierUnits rename guards drive input member).row.id := by
  let enabled := targetEnableAt rename guards.table.proofPrefix drive
  let current := guards.table.proofPrefix.extend enabled.state enabled.steps enabled.checked
  have enabledOrigins := targetEnableAt_supported rename guards.table.proofPrefix drive origins.table.supported
  intro input member
  let enable := mapLiteral rename ((qualifierGuarded .healthy parameters.bridge.target).slots
    (.primary (.enable parameters.bridge.target)))
  by_cases equal : input = enable
  · subst input
    simpa only [SourceHealthyQualifiers.targetQualifierUnits, id, SourceMixedSchedule.subclause_dite_id,
      enable, dite_eq_left rfl, dite_true, retarget] using enabledOrigins.2
  · have rest : input ∈ (List.finRange parameters.buses).map
        (fun bus => mapLiteral rename (guardHandle .healthy parameters.bridge.target bus)) := by
      simpa only [SourceHealthyQualifiers.targetQualifierInputs, List.map_cons, List.mem_cons, List.map_map,
        qualifierGuarded_guard_handle, Function.comp_def] using (List.mem_cons.mp member).resolve_left equal
    have actual := ControllerOrigins.mappedUnit_origin rename current (List.finRange parameters.buses)
      (fun bus => mapLiteral rename (guardHandle .healthy parameters.bridge.target bus))
      (context (parameters := parameters) rename)
      (fun bus listed => FoldProjection.afterTrace (guards.rows bus listed) enabled.state enabled.steps enabled.checked)
      (fun bus listed => resultOrigin_append_right _ _ guards.table.proofPrefix.steps enabled.steps _
        (origins.rows bus listed)) input rest
    simpa only [SourceHealthyQualifiers.targetQualifierUnits, id, SourceMixedSchedule.subclause_dite_id,
      dite_eq_right equal, current, SourcePrefix.extend, enabled, enable] using actual

theorem healthyTargetQualifier_origins (rename : Nat → Fin v)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (drive : parameters.drive = true) (origins : HealthyMaskOrigins rename table) :
    ProjectionOriginalSupport rename table.proofPrefix (SourceHealthyQualifiers.targetQualifier rename table drive) := by
  let guards := SourceHealthyQualifiers.buildGuards rename table drive (List.finRange parameters.buses)
  let enabled := targetEnableAt rename guards.table.proofPrefix drive
  let prefixState := guards.table.proofPrefix.extend enabled.state enabled.steps enabled.checked
  let tree := (qualifierTree rename .healthy parameters.bridge.target).afterTrace
    enabled.state prefixState.steps prefixState.checked
  let units := SourceHealthyQualifiers.targetQualifierUnits rename guards drive
  let forced := TreeUnits.force tree (context (parameters := parameters) rename) units
  have guardOrigins := healthyBuildGuards_origins rename table drive (List.finRange parameters.buses) origins
  have enableOrigins := targetEnableAt_supported rename guards.table.proofPrefix drive guardOrigins.table.supported
  have treeOrigins := treeOriginals_afterTrace
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (qualifierTree rename .healthy parameters.bridge.target)
    (qualifierTree_originals rename .healthy parameters.bridge.target)
    enabled.state prefixState.steps prefixState.checked
  have actual := ControllerOrigins.tree_force_supported rename prefixState tree
    (context (parameters := parameters) rename) units enableOrigins.1 treeOrigins
    (targetQualifierUnits_origins rename guards drive guardOrigins)
  let emitted := SourceHealthyQualifiers.targetQualifier rename table drive
  have emittedSteps : emitted.steps = (guards.steps ++ enabled.steps) ++ forced.steps := rfl
  have emittedId : emitted.result.row.id = forced.result.row.id := rfl
  have same : prefixState.steps ++ forced.steps = table.proofPrefix.steps ++ emitted.steps := by
    dsimp only [prefixState, SourcePrefix.extend]
    rw [guardOrigins.sameSteps, emittedSteps]
    simp only [List.append_assoc]
    rfl
  constructor
  · change TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) (table.proofPrefix.steps ++ emitted.steps)
    rw [← same]
    exact actual.1
  · change ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (table.proofPrefix.steps ++ emitted.steps) emitted.result.row.id
    rw [← same, emittedId]
    exact actual.2

end Controller.NativeProof.Wrapper
