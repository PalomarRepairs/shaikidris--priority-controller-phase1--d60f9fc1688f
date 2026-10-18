module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperPreparation
public import Controller.NativeProof.WrapperTreeProvenance
public import Controller.NativeProof.WrapperControllerOperations

@[expose] public section

/-! Controller-only provenance through healthy-singleton preparation tables. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceMismatchSeed Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceHealthyMasks
open Controller.NativeProof.SourceSuffixSelector Controller.NativeProof.SourceBusAdvance
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceMixedSchedule
variable {parameters : Parameters} {v : Nat}

def ControllerRowOrigin (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename) {clause : Clause (Fin v)}
    (row : AvailableSubclause prefixState.state clause) : Prop :=
  ResultOrigin (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps row.row.id

structure HealthyMaskOrigins (rename : Nat → Fin v)
    {count : Nat} (table : SourceHealthyMasks.Table (parameters := parameters) rename count) : Prop where
  supported : SourceMixedSchedule.PrefixOriginalSupport rename table.proofPrefix
  firstZero : ∀ channel different, ControllerRowOrigin rename table.proofPrefix (table.firstZero channel different)
  firstAbsent : ∀ channel different, ControllerRowOrigin rename table.proofPrefix (table.firstAbsent channel different)
  targetMasks : ∀ bus member, ControllerRowOrigin rename table.proofPrefix (table.targetMasks bus member)
  flagRequests : ∀ position before, ControllerOrigins.DirectionPairOrigin rename table.proofPrefix
    (table.flagRequests position before)

theorem HealthyMaskOrigins.afterTrace (rename : Nat → Fin v)
    {count : Nat} (table : SourceHealthyMasks.Table (parameters := parameters) rename count)
    (origins : HealthyMaskOrigins rename table)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.proofPrefix.state steps = some next)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename (table.proofPrefix.extend next steps checked)) :
    HealthyMaskOrigins rename (table.afterTrace next steps checked) := by
  refine ⟨supported, ?_, ?_, ?_, ?_⟩
  · intro channel different
    exact resultOrigin_append_right _ _ table.proofPrefix.steps steps _ (origins.firstZero channel different)
  · intro channel different
    exact resultOrigin_append_right _ _ table.proofPrefix.steps steps _ (origins.firstAbsent channel different)
  · intro bus member
    exact resultOrigin_append_right _ _ table.proofPrefix.steps steps _ (origins.targetMasks bus member)
  · intro position before
    exact ControllerOrigins.DirectionPairOrigin.afterTrace rename table.proofPrefix
      (table.flagRequests position before) (origins.flagRequests position before) next steps checked

theorem healthyMaskInitial_origins (rename : Nat → Fin v) (drive : parameters.drive = true) :
    HealthyMaskOrigins rename (SourceHealthyMasks.initial rename drive) := by
  let absences := allOtherAbsences (parameters := parameters) rename
  let masks := allFirstMasks (parameters := parameters) rename drive
  have maskOrigins := allFirstMasks_origins rename drive
  have absenceOrigins := allOtherAbsences_origins (parameters := parameters) rename
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [SourceHealthyMasks.initial, SourceMixedSchedule.PrefixOriginalSupport,
      absences, masks] using maskOrigins.1
  · intro channel different
    have origin := maskOrigins.2 .healthy channel (List.mem_finRange _)
    have indexEqual : ((SourceHealthyMasks.initial rename drive).firstZero channel different).row.id =
        (masks.rows .healthy channel (List.mem_finRange _)).row.id := by
      unfold SourceHealthyMasks.initial
      dsimp only [id]
      with_unfolding_all
        apply SourceMixedSchedule.subclause_indices_cast_id rfl
        simp [firstMaskValue, absenceBit, different, valueLiteral,
          SourceRoleFrames.maskOutput_eq_sourceRoleMap, SourceBusSchedule.sourceMask]
    unfold ControllerRowOrigin
    rw [indexEqual]
    exact origin
  · intro channel different
    have present : channel ∈ (List.finRange parameters.channels).filter
        (fun query => decide (query ≠ parameters.bridge.target)) :=
      List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true different⟩
    have origin := resultOrigin_append_right _ _ absences.steps masks.steps
      (absences.rows channel present).row.id (absenceOrigins.2 channel present)
    simpa only [ControllerRowOrigin, SourceHealthyMasks.initial, afterTrace,
      allOtherAbsences_complete, SourcePrefix.initial, List.nil_append, absences, masks] using origin
  · intro bus member
    have same : bus = parameters.firstBus := by simpa using member
    subst bus
    have origin := maskOrigins.2 .healthy parameters.bridge.target (List.mem_finRange _)
    have indexEqual : ((SourceHealthyMasks.initial rename drive).targetMasks parameters.firstBus member).row.id =
        (masks.rows .healthy parameters.bridge.target (List.mem_finRange _)).row.id := by
      unfold SourceHealthyMasks.initial
      dsimp only [id]
      with_unfolding_all
        apply Eq.trans (SourceMixedSchedule.subclause_indices_mpr_id
          (show masks.state = masks.state from rfl)
          (show context (parameters := parameters) rename ++ [SourceFoldProjection.mapLiteral rename
              ((SourceBusSchedule.stagesBefore (parameters := parameters) .healthy 0).slots
                (.internal (.mask .healthy parameters.firstBus parameters.bridge.target)))] =
            context (parameters := parameters) rename ++
              [SourceBusSchedule.sourceMask rename .healthy parameters.firstBus parameters.bridge.target] from by
            rw [SourceBusSchedule.stagesBefore_zero_first_mask]) _ _)
        apply SourceMixedSchedule.subclause_indices_cast_id rfl
        simp [firstMaskValue, absenceBit, valueLiteral,
          SourceRoleFrames.maskOutput_eq_sourceRoleMap, SourceBusSchedule.sourceMask]
    unfold ControllerRowOrigin
    rw [indexEqual]
    exact origin
  · intro position before
    exact False.elim (Nat.not_lt_zero _ before)

theorem healthyOtherTerm_origins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target)
    (origins : HealthyMaskOrigins rename table) :
    SourceMixedSchedule.ProjectionOriginalSupport rename table.proofPrefix
      (SourceHealthyMasks.otherTerm rename position table channel different) := by
  let tree := (SourceStageCongruence.laterTermTree rename .healthy position channel).afterTrace
    table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
  let input := mapLiteral rename ((SourceFoldOccurrences.termBefore .healthy position channel).slots
    (.internal (.mask .healthy parameters.firstBus channel)))
  have member : input ∈ (SourceStageCongruence.laterTermInputs .healthy position channel).map (mapLiteral rename) := by
    apply List.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    unfold SourceStageCongruence.laterTermInputs
    apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    refine ⟨parameters.firstBus, ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_finRange _, by simpa [Parameters.firstBus, Fin.lt_def] using
      SourceHealthyMasks.later_positive position⟩
  let unit : AvailableSubclause table.proofPrefix.state
      (context (parameters := parameters) rename ++ [negate input]) := by
    simpa only [input, SourceBusSchedule.termBefore_first_mask] using table.firstZero channel different
  have indexEqual : unit.row.id = (table.firstZero channel different).row.id := by
    dsimp only [unit]
    with_unfolding_all
      apply SourceMixedSchedule.subclause_indices_cast_id rfl
      simp only [input, SourceBusSchedule.termBefore_first_mask]
  have unitOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      table.proofPrefix.steps unit.row.id := by
    rw [indexEqual]
    exact origins.firstZero channel different
  have originals := SourceFoldProvenance.treeOriginals_afterTrace
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (SourceStageCongruence.laterTermTree rename .healthy position channel)
    (SourceMixedSchedule.laterTermTree_originals rename .healthy position channel)
    table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
  have actual := ControllerOrigins.tree_deny_supported rename table.proofPrefix tree
    (context (parameters := parameters) rename) input member unit origins.supported originals unitOrigin
  unfold SourceHealthyMasks.otherTerm
  dsimp only [id]
  exact ControllerOrigins.projection_indices_mp_supported rename table.proofPrefix
    (by simp only [tree, SourceStageCongruence.laterTermOutput])
    (by simp only [tree, AndTree.afterTrace_nodes]) _ _ actual

structure TermZerosOrigins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (start : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    {channels : List (Fin parameters.channels)}
    (bank : SourceHealthyMasks.TermZeros rename position start channels) : Prop where
  table : HealthyMaskOrigins rename bank.table
  sameSteps : bank.table.proofPrefix.steps = start.proofPrefix.steps ++ bank.steps
  rows : ∀ channel member different, ControllerRowOrigin rename bank.table.proofPrefix
    (bank.rows channel member different)

theorem termZeros_dite_row_id (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (start : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (channels : List (Fin parameters.channels))
    (condition : Prop) [Decidable condition]
    (yes : condition → SourceHealthyMasks.TermZeros rename position start channels)
    (no : ¬condition → SourceHealthyMasks.TermZeros rename position start channels)
    (channel : Fin parameters.channels) (member : channel ∈ channels)
    (different : channel ≠ parameters.bridge.target) :
    ((dite condition yes no).rows channel member different).row.id =
      dite condition (fun evidence => ((yes evidence).rows channel member different).row.id)
        (fun evidence => ((no evidence).rows channel member different).row.id) := by
  by_cases proof : condition
  · calc
      _ = ((yes proof).rows channel member different).row.id :=
        congrArg (fun bank : SourceHealthyMasks.TermZeros rename position start channels =>
          (bank.rows channel member different).row.id) (dite_eq_left proof)
      _ = _ := by
        have scalar : dite condition (fun evidence => ((yes evidence).rows channel member different).row.id)
            (fun evidence => ((no evidence).rows channel member different).row.id) =
            ((yes proof).rows channel member different).row.id := dite_eq_left proof
        exact scalar.symm
  · calc
      _ = ((no proof).rows channel member different).row.id :=
        congrArg (fun bank : SourceHealthyMasks.TermZeros rename position start channels =>
          (bank.rows channel member different).row.id) (dite_eq_right proof)
      _ = _ := by
        have scalar : dite condition (fun evidence => ((yes evidence).rows channel member different).row.id)
            (fun evidence => ((no evidence).rows channel member different).row.id) =
            ((no proof).rows channel member different).row.id := dite_eq_right proof
        exact scalar.symm

theorem collectOtherTerms_origins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (channels : List (Fin parameters.channels)) (origins : HealthyMaskOrigins rename table) :
    TermZerosOrigins rename position table (SourceHealthyMasks.collectOtherTerms rename position table channels) := by
  induction channels generalizing table with
  | nil =>
    refine ⟨origins, ?_, ?_⟩
    · simp only [SourceHealthyMasks.collectOtherTerms, List.append_nil]
    · intro channel member different
      simp at member
  | cons channel rest ih =>
    by_cases same : channel = parameters.bridge.target
    · have tail := ih table origins
      refine ⟨?_, ?_, ?_⟩
      · simpa only [SourceHealthyMasks.collectOtherTerms, dite_eq_left same] using tail.table
      · simpa only [SourceHealthyMasks.collectOtherTerms, dite_eq_left same] using tail.sameSteps
      · intro query member different
        have unequal : query ≠ channel := fun equal => different (equal.trans same)
        have origin := tail.rows query ((List.mem_cons.mp member).resolve_left unequal) different
        have indexEqual :
            ((SourceHealthyMasks.collectOtherTerms rename position table (channel :: rest)).rows query member different).row.id =
            ((SourceHealthyMasks.collectOtherTerms rename position table rest).rows query
              ((List.mem_cons.mp member).resolve_left unequal) different).row.id := by
          simp only [SourceHealthyMasks.collectOtherTerms, termZeros_dite_row_id, dite_eq_left same,
            SourceMixedSchedule.subclause_dite_id, dite_eq_right unequal,
            SourceHealthyMasks.Table.afterTrace, SourcePrefix.extend]
        unfold ControllerRowOrigin
        rw [indexEqual]
        simpa only [ControllerRowOrigin, SourceHealthyMasks.collectOtherTerms, dite_eq_left same] using origin
    · let added := SourceHealthyMasks.otherTerm rename position table channel same
      let nextTable := table.afterTrace added.state added.steps added.checked
      let tailBank := SourceHealthyMasks.collectOtherTerms rename position nextTable rest
      have one := healthyOtherTerm_origins rename position table channel same origins
      have nextOrigins := HealthyMaskOrigins.afterTrace rename table origins added.state added.steps added.checked one.1
      have tail := ih nextTable nextOrigins
      refine ⟨?_, ?_, ?_⟩
      · simpa only [SourceHealthyMasks.collectOtherTerms, dite_eq_right same, nextTable, added] using tail.table
      · simpa only [SourceHealthyMasks.collectOtherTerms, dite_eq_right same, nextTable, added,
          SourceHealthyMasks.Table.afterTrace, SourcePrefix.extend, List.append_assoc] using tail.sameSteps
      · intro query member different
        by_cases equal : query = channel
        · subst query
          have origin := resultOrigin_append_right _ _ (table.proofPrefix.steps ++ added.steps)
            tailBank.steps added.result.row.id one.2
          have prefixSteps : tailBank.table.proofPrefix.steps =
              (table.proofPrefix.steps ++ added.steps) ++ tailBank.steps := tail.sameSteps
          have indexEqual :
              ((SourceHealthyMasks.collectOtherTerms rename position table (channel :: rest)).rows channel member different).row.id =
              added.result.row.id := by
            simp only [SourceHealthyMasks.collectOtherTerms, termZeros_dite_row_id, dite_eq_right same,
              SourceMixedSchedule.subclause_dite_id, dite_eq_left rfl, dite_true, afterTrace, added, nextTable, SourceHealthyMasks.Table.afterTrace, SourcePrefix.extend]
          unfold ControllerRowOrigin
          rw [indexEqual]
          simp only [SourceHealthyMasks.collectOtherTerms, dite_eq_right same]
          rw [prefixSteps]
          exact origin
        · have origin := tail.rows query ((List.mem_cons.mp member).resolve_left equal) different
          have indexEqual :
              ((SourceHealthyMasks.collectOtherTerms rename position table (channel :: rest)).rows query member different).row.id =
              (tailBank.rows query ((List.mem_cons.mp member).resolve_left equal) different).row.id := by
            simp only [SourceHealthyMasks.collectOtherTerms, termZeros_dite_row_id, dite_eq_right same,
              SourceMixedSchedule.subclause_dite_id, dite_eq_right equal, tailBank, nextTable, added, SourceHealthyMasks.Table.afterTrace, SourcePrefix.extend]
          unfold ControllerRowOrigin
          rw [indexEqual]
          simpa only [ControllerRowOrigin, SourceHealthyMasks.collectOtherTerms, dite_eq_right same,
            nextTable, added] using origin

theorem targetTermUnits_origins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (drive : parameters.drive = true) (origins : HealthyMaskOrigins rename table) :
    ∀ other present different, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (table.proofPrefix.steps ++ (targetEnableAt rename table.proofPrefix drive).steps)
      (SourceHealthyMasks.targetTermUnits rename position table drive other present different).row.id := by
  let enabled := targetEnableAt rename table.proofPrefix drive
  let current := table.proofPrefix.extend enabled.state enabled.steps enabled.checked
  have enabledOrigins := SourceMixedSchedule.targetEnableAt_supported rename table.proofPrefix drive origins.supported
  intro other present different
  by_cases isEnable : other = mapLiteral rename ((SourceFoldOccurrences.termBefore .healthy position parameters.bridge.target).slots
      (.primary (.enable parameters.bridge.target)))
  · subst other
    simpa only [SourceHealthyMasks.targetTermUnits, id, SourceMixedSchedule.subclause_dite_id,
      dite_true, retarget, SourceMixedSchedule.ProjectionOriginalSupport, SourcePrefix.extend] using enabledOrigins.2
  · let buses := (List.finRange parameters.buses).filter
      (fun earlier => earlier < (SourceFoldOccurrences.laterBuses (parameters := parameters))[position.val])
    let handle := fun bus => mapLiteral rename ((SourceFoldOccurrences.termBefore .healthy position parameters.bridge.target).slots
      (.internal (.mask .healthy bus parameters.bridge.target)))
    have presentMask : other ∈ buses.map handle := by
      have classified : other = mapLiteral rename ((SourceFoldOccurrences.termBefore .healthy position parameters.bridge.target).slots
          (.primary (.enable parameters.bridge.target))) ∨ other = targetRequest rename position ∨ other ∈ buses.map handle := by
        simpa [SourceStageCongruence.laterTermInputs, targetRequest, buses, handle, List.mem_map, eq_comm] using present
      exact (classified.resolve_left isEnable).resolve_left different
    let rows : ∀ bus ∈ buses, AvailableSubclause enabled.state
        (context (parameters := parameters) rename ++ [handle bus]) := fun bus listed => by
      have before : bus < (SourceFoldOccurrences.laterBuses (parameters := parameters))[position.val] := by
        simpa using (List.mem_filter.mp listed).2
      have row := FoldProjection.afterTrace (table.targetMasks bus (earlier_bus_covered position bus before))
        enabled.state enabled.steps enabled.checked
      simpa only [handle, termBefore_mask, busBefore_eq_stagesBefore] using row
    have rowOrigins : ∀ bus member, ResultOrigin (formula parameters).clauses.size
        (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        current.steps (rows bus member).row.id := by
      intro bus member
      have before : bus < (SourceFoldOccurrences.laterBuses (parameters := parameters))[position.val] := by
        simpa using (List.mem_filter.mp member).2
      have indexEqual : (rows bus member).row.id =
          (table.targetMasks bus (earlier_bus_covered position bus before)).row.id := by
        dsimp only [rows]
        with_unfolding_all
          apply SourceMixedSchedule.subclause_indices_cast_id rfl
          simp only [handle, termBefore_mask, busBefore_eq_stagesBefore]
      rw [indexEqual]
      exact resultOrigin_append_right _ _ table.proofPrefix.steps enabled.steps _
        (origins.targetMasks bus (earlier_bus_covered position bus before))
    have mapped := ControllerOrigins.mappedUnit_origin rename current buses handle
      (context (parameters := parameters) rename) rows rowOrigins other presentMask
    simpa only [SourceHealthyMasks.targetTermUnits, id, SourceMixedSchedule.subclause_dite_id,
      dite_eq_right isEnable, buses, handle, rows, current, enabled, SourcePrefix.extend] using mapped

theorem healthyTargetTerm_origins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename position.val)
    (drive : parameters.drive = true) (origins : HealthyMaskOrigins rename table) :
    ControllerOrigins.PairedProjectionOriginalSupport rename table.proofPrefix
      (SourceHealthyMasks.targetTerm rename position table drive) := by
  let enabled := targetEnableAt rename table.proofPrefix drive
  let current := table.proofPrefix.extend enabled.state enabled.steps enabled.checked
  let tree := (SourceStageCongruence.laterTermTree rename .healthy position parameters.bridge.target).afterTrace
    enabled.state current.steps current.checked
  have member : targetRequest rename position ∈
      (SourceStageCongruence.laterTermInputs .healthy position parameters.bridge.target).map (mapLiteral rename) := by
    simp [targetRequest, SourceStageCongruence.laterTermInputs]
  have enabledOrigins := SourceMixedSchedule.targetEnableAt_supported rename table.proofPrefix drive origins.supported
  have originals := SourceFoldProvenance.treeOriginals_afterTrace
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (SourceStageCongruence.laterTermTree rename .healthy position parameters.bridge.target)
    (SourceMixedSchedule.laterTermTree_originals rename .healthy position parameters.bridge.target)
    enabled.state current.steps current.checked
  have actual := ControllerOrigins.reduceToInput_supported rename current tree
    (context (parameters := parameters) rename) (targetRequest rename position) member
    (SourceHealthyMasks.targetTermUnits rename position table drive) enabledOrigins.1 originals
    (targetTermUnits_origins rename position table drive origins)
  let reduced := TreeUnits.reduceToInput tree (context (parameters := parameters) rename)
    (targetRequest rename position) member (SourceHealthyMasks.targetTermUnits rename position table drive)
  let combined := SourceHealthyMasks.targetTerm rename position table drive
  have stateEqual : combined.state = reduced.state := by rfl
  have stepsEqual : combined.steps = enabled.steps ++ reduced.steps := by rfl
  have pairEqual : combined.pair = reduced.pair := by rfl
  let before := current.extend reduced.state reduced.steps reduced.checked
  let after := table.proofPrefix.extend combined.state combined.steps combined.checked
  have same : before.steps = after.steps := by
    dsimp only [before, after, current, SourcePrefix.extend]
    rw [stepsEqual, List.append_assoc]
  refine ⟨?_, ?_, ?_⟩
  · change TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) after.steps
    rw [← same]
    exact actual.1
  · have carried := ControllerOrigins.GuardedTransferOrigin.same_steps rename reduced.state
      before.steps after.steps same before.checked (by simpa only [after, SourcePrefix.extend, stateEqual] using after.checked)
      reduced.pair.forward actual.2.1
    simpa only [ControllerOrigins.GuardedTransferOrigin, after, pairEqual, combined,
      SourcePrefix.extend, SourceStageCongruence.laterTermOutput, reduced, tree, current,
      enabled, SourceHealthyMasks.targetTerm, id] using carried
  · have carried := ControllerOrigins.GuardedTransferOrigin.same_steps rename reduced.state
      before.steps after.steps same before.checked (by simpa only [after, SourcePrefix.extend, stateEqual] using after.checked)
      reduced.pair.backward actual.2.2
    simpa only [ControllerOrigins.GuardedTransferOrigin, after, pairEqual, combined,
      SourcePrefix.extend, SourceStageCongruence.laterTermOutput, reduced, tree, current,
      enabled, SourceHealthyMasks.targetTerm, id] using carried

theorem targetFlagUnits_origins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    {start : SourceHealthyMasks.Table (parameters := parameters) rename position.val}
    (zeros : SourceHealthyMasks.TermZeros rename position start (List.finRange parameters.channels))
    (origins : TermZerosOrigins rename position start zeros) :
    ∀ other present different, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      zeros.table.proofPrefix.steps
      (SourceHealthyMasks.targetFlagUnits rename position zeros other present different).row.id := by
  intro other present different
  let channels := (List.finRange parameters.channels).filter (fun channel => channel ≠ parameters.bridge.target)
  let handle := fun channel => negate (SourceStageCongruence.laterTermOutput rename .healthy position channel)
  have inputs : (SourceStageCongruence.laterFlagInputs .healthy position).map (dualLiteral rename) =
      (List.finRange parameters.channels).map handle := by
    rw [show (SourceStageCongruence.laterFlagInputs .healthy position).map (dualLiteral rename) =
        ((SourceStageCongruence.laterFlagInputs .healthy position).map (mapLiteral rename)).map negate from List.map_map.symm]
    rw [laterFlagInputs_eq_terms, List.map_map]
    rfl
  have covered : other ∈ channels.map handle := by
    rw [inputs] at present
    obtain ⟨channel, member, equal⟩ := List.mem_map.mp present
    have nonTarget : channel ≠ parameters.bridge.target := by
      intro same
      exact different (equal.symm.trans (congrArg handle same))
    exact List.mem_map.mpr ⟨channel, List.mem_filter.mpr ⟨member, by simpa using nonTarget⟩, equal⟩
  let rows := fun channel (member : channel ∈ channels) =>
    zeros.rows channel (List.mem_filter.mp member).1 (by simpa using (List.mem_filter.mp member).2)
  have actual := ControllerOrigins.mappedUnit_origin rename zeros.table.proofPrefix channels handle
    (context (parameters := parameters) rename) rows
    (fun channel member => origins.rows channel (List.mem_filter.mp member).1
      (by simpa using (List.mem_filter.mp member).2)) other covered
  simpa only [SourceHealthyMasks.targetFlagUnits, id, channels, handle, rows] using actual

theorem transferDual_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (transfer : SourceStageCongruence.GuardedTransfer prefixState.state cofactor input output)
    (origin : ControllerOrigins.GuardedTransferOrigin rename prefixState transfer) :
    ControllerOrigins.GuardedTransferOrigin rename prefixState (SourceStageXor.dualTransfer transfer) := by
  cases transfer with
  | identity same => trivial
  | derived row =>
    simpa only [ControllerOrigins.GuardedTransferOrigin, ControllerOrigins.TransferOrigin,
      SourceStageXor.dualTransfer, retarget] using origin

theorem directionPair_indices_mp_origins (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    {beforeContext afterContext : Clause (Fin v)}
    {beforeInput afterInput beforeOutput afterOutput : Literal (Fin v)}
    (contextEqual : beforeContext = afterContext)
    (inputEqual : beforeInput = afterInput) (outputEqual : beforeOutput = afterOutput)
    (typeEqual : DirectionPair prefixState.state beforeContext beforeInput beforeOutput =
      DirectionPair prefixState.state afterContext afterInput afterOutput)
    (value : DirectionPair prefixState.state beforeContext beforeInput beforeOutput)
    (origins : ControllerOrigins.DirectionPairOrigin rename prefixState value) :
    ControllerOrigins.DirectionPairOrigin rename prefixState (Eq.mp typeEqual value) := by
  subst afterContext
  subst afterInput
  subst afterOutput
  have same : typeEqual = rfl := Subsingleton.elim _ _
  rw [same]
  exact origins

theorem healthyTargetFlag_origins (rename : Nat → Fin v)
    (position : Fin (SourceFoldOccurrences.laterBuses (parameters := parameters)).length)
    {start : SourceHealthyMasks.Table (parameters := parameters) rename position.val}
    (zeros : SourceHealthyMasks.TermZeros rename position start (List.finRange parameters.channels))
    (origins : TermZerosOrigins rename position start zeros) :
    ControllerOrigins.PairedProjectionOriginalSupport rename zeros.table.proofPrefix
      (SourceHealthyMasks.targetFlag rename position zeros) := by
  let tree := (SourceStageCongruence.laterFlagTree rename .healthy position).afterTrace
    zeros.table.proofPrefix.state zeros.table.proofPrefix.steps zeros.table.proofPrefix.checked
  have inputs : (SourceStageCongruence.laterFlagInputs .healthy position).map (dualLiteral rename) =
      (List.finRange parameters.channels).map (fun channel => negate (SourceStageCongruence.laterTermOutput rename .healthy position channel)) := by
    rw [show (SourceStageCongruence.laterFlagInputs .healthy position).map (dualLiteral rename) =
        ((SourceStageCongruence.laterFlagInputs .healthy position).map (mapLiteral rename)).map negate from List.map_map.symm]
    rw [laterFlagInputs_eq_terms, List.map_map]
    rfl
  have member : negate (SourceStageCongruence.laterTermOutput rename .healthy position parameters.bridge.target) ∈
      (SourceStageCongruence.laterFlagInputs .healthy position).map (dualLiteral rename) := by
    rw [inputs]
    exact List.mem_map.mpr ⟨parameters.bridge.target, List.mem_finRange _, rfl⟩
  have originals := SourceFoldProvenance.treeOriginals_afterTrace
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (SourceStageCongruence.laterFlagTree rename .healthy position)
    (SourceMixedSchedule.laterFlagTree_originals rename .healthy position)
    zeros.table.proofPrefix.state zeros.table.proofPrefix.steps zeros.table.proofPrefix.checked
  let reduced := TreeUnits.reduceToInput tree (context (parameters := parameters) rename)
    (negate (SourceStageCongruence.laterTermOutput rename .healthy position parameters.bridge.target)) member
    (SourceHealthyMasks.targetFlagUnits rename position zeros)
  have actual := ControllerOrigins.reduceToInput_supported rename zeros.table.proofPrefix tree
    (context (parameters := parameters) rename)
    (negate (SourceStageCongruence.laterTermOutput rename .healthy position parameters.bridge.target)) member
    (SourceHealthyMasks.targetFlagUnits rename position zeros) origins.table.supported originals
    (targetFlagUnits_origins rename position zeros origins)
  let final := zeros.table.proofPrefix.extend reduced.state reduced.steps reduced.checked
  have forwards := transferDual_origins rename final reduced.pair.backward actual.2.2
  have backwards := transferDual_origins rename final reduced.pair.forward actual.2.1
  unfold ControllerOrigins.PairedProjectionOriginalSupport SourceHealthyMasks.targetFlag
  dsimp only [id]
  refine ⟨actual.1, ?_⟩
  apply directionPair_indices_mp_origins rename final rfl
    (by simp only [tree, dualLiteral, SourceStagePolarity.laterFlagOutput, negate_negate])
    (negate_negate _) _ _
  exact ⟨forwards, backwards⟩

end Controller.NativeProof.Wrapper
