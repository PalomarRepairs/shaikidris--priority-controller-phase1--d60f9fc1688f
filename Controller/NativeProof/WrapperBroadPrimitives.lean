module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperForwardTable

@[expose] public section

/-! Controller primitives retain their original occurrences after decoder traces. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceSuffixSelector
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
variable {parameters : Parameters} {v : Nat}

theorem broadTargetEnableAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prefixState) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename prefixState (targetEnableAt rename prefixState drive) := by
  let channel := parameters.bridge.target
  let absent := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.absentBefore (parameters := parameters) channel).lastID + 1, true)
  let term := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.termBefore (parameters := parameters) channel).lastID + 1, true)
  let input := mapLiteral rename
    ((Controller.NativeProof.SourceMismatchSeed.termBefore (parameters := parameters) channel).slots
      (.primary (.enable channel)))
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
    simpa only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil,
      Controller.NativeProof.SourceMismatchSeed.absentBefore_term_handle,
      absent, term, mapLiteral] using row
  let notRow := FoldProjection.afterTrace originalNot prefixState.state prefixState.steps prefixState.checked
  let first := longMerge prefixState.state absent [] [term] unit notRow
  have firstRun := longMerge_run prefixState.state absent [] [term] unit notRow
  let firstResult := longMerge_result prefixState.state absent [] [term] unit notRow
  let originalAnd : AvailableSubclause (initialState (relabel rename (formula parameters))) [negate term, input] := by
    have row := ofRow ((Controller.NativeProof.SourceMismatchSeed.termRows rename channel).row
      ⟨0, by change 0 < 3; decide⟩)
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
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
    simp only [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
      Rows.mapClause, List.map_cons, List.map_nil,
      Controller.NativeProof.SourceMismatchSeed.absentBefore_term_handle,
      absent, term, mapLiteral]
  have andId : originalAnd.row.id =
      ((Controller.NativeProof.SourceMismatchSeed.termRows rename channel).row
        ⟨0, by change 0 < 3; decide⟩).id := by
    dsimp only [originalAnd]
    refine (subclause_indices_mpr_id ?_ ?_ _ _).trans ?_
    · rfl
    · simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
        negate, Std.Sat.Literal.negate]
    · apply subclause_indices_cast_id
      · rfl
      · simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, mapLiteral, term, input,
        negate, Std.Sat.Literal.negate]
  have unitOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps unit.row.id :=
    Or.inl (Or.inl (Controller.NativeProof.SourceMismatchBranch.physicalUnit_allowed rename ⟨0, by decide⟩))
  have notOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps notRow.row.id := by
    change Controller.NativeProof.SourceMismatchHandles.ResultOrigin _ _ _ originalNot.row.id
    rw [notId]
    exact Or.inl (Or.inl (Controller.NativeProof.SourceMismatchSeed.absentRows_allowed rename channel
      ⟨0, by change 0 < 2; decide⟩))
  have firstSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps prefixState.state absent [] [term] unit notRow supported
    (SourceDecoderSchedule.allowed_native_count_le rename) (prefix_native_count_le rename prefixState) unitOrigin notOrigin
  have andOrigin : Controller.NativeProof.SourceMismatchHandles.ResultOrigin
      (formula parameters).clauses.size
      (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      (prefixState.steps ++ first.steps) andRow.row.id := by
    change Controller.NativeProof.SourceMismatchHandles.ResultOrigin _ _ _ originalAnd.row.id
    rw [andId]
    exact Or.inl (Or.inl (Controller.NativeProof.SourceMismatchSeed.termRows_allowed rename channel
      ⟨0, by change 0 < 3; decide⟩))
  have firstBound := Nat.le_trans (prefix_native_count_le rename prefixState)
    (runSteps_lastId_le firstRun)
  have secondSupport := longMerge_supported (formula parameters).clauses.size
    (Controller.NativeProof.SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (prefixState.steps ++ first.steps) first.state term [input] [] andRow firstResult
    firstSupport.1 (SourceDecoderSchedule.allowed_native_count_le rename) firstBound andOrigin firstSupport.2
  simpa only [SourceDecoderSchedule.ProjectionOriginalSupport, targetEnableAt, List.append_assoc, retarget,
    channel, absent, term, input, physical, originalUnit, unit, originalNot, notRow,
    first, firstRun, firstResult, originalAnd, kept, andRow, second] using secondSupport



theorem broadGuardOrFlagAt_supported (rename : Nat → Fin v)
    (prefixState : SourcePrefix (parameters := parameters) rename)
    (side : Side) (channel : Fin parameters.channels) (bus : Fin parameters.buses)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename prefixState) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename prefixState (guardOrFlagAt rename prefixState side channel bus) := by
  let q := mapLiteral rename (negatedHandle side bus)
  let g := mapLiteral rename (guardHandle side channel bus)
  let p := mapLiteral rename (flagInput side bus)
  let left := FoldProjection.afterTrace (guardNegatedRow rename side channel bus)
    prefixState.state prefixState.steps prefixState.checked
  let right := FoldProjection.afterTrace (privateFlagRow rename side bus)
    prefixState.state prefixState.steps prefixState.checked
  have one : ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps left.row.id := Or.inl (Or.inl (guardNegatedRow_allowed rename side channel bus))
  have two : ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
      prefixState.steps right.row.id := Or.inl (Or.inl (privateFlagRow_allowed rename side bus))
  exact longMerge_supported (formula parameters).clauses.size
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    prefixState.steps prefixState.state q [g] [p] left right supported
    (SourceDecoderSchedule.allowed_native_count_le rename) (prefix_native_count_le rename prefixState) one two

end Controller.NativeProof.Wrapper
