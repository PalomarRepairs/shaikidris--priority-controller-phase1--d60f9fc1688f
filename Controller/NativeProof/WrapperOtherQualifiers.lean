module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperHealthyQualifiers

@[expose] public section

/-! Non-target healthy qualifier propagation consumes retained source occurrences. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceSuffixSelector
open Controller.NativeProof.SourceHealthyMasks Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceQualifierSchedule
open Controller.NativeProof.SourceQualifierOccurrences Controller.NativeProof.SourceSlotFrames
open Controller.NativeProof.LocalUnitCases
variable {parameters : Parameters} {v : Nat}

theorem healthyOtherQualifier_origins (rename : Nat → Fin v)
    (table : SourceHealthyMasks.Table (parameters := parameters) rename (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target)
    (origins : HealthyMaskOrigins rename table) :
    ProjectionOriginalSupport rename table.proofPrefix
      (SourceHealthyQualifiers.otherQualifier rename table channel different) := by
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
  let notFlag : AvailableSubclause projected.state (context (parameters := parameters) rename ++ [negate nf]) := by
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
  let longGuard : AvailableSubclause projected.state [negate g, nf, r] := by
    let original := ofRow ((guardRows rename .healthy channel parameters.firstBus).row ⟨2, by change 2 < 3; decide⟩)
    have row : AvailableSubclause prefixState.state [negate g, nf, r] := by
      simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, List.map_append, List.append_nil,
        guardHandle, guardBefore_negated, (guardBefore_roots .healthy channel parameters.firstBus).2,
        g, nf, r, requestHandle, mapLiteral, negate, Std.Sat.Literal.negate] using
        FoldProjection.afterTrace original prefixState.state prefixState.steps prefixState.checked
    exact FoldProjection.afterTrace row projected.state projected.steps projected.checked
  let negativeTerm : AvailableSubclause projected.state [negate absent, negate term] := by
    let original := ofRow ((SourceMismatchSeed.absentRows rename channel).row ⟨1, by change 1 < 2; decide⟩)
    have row : AvailableSubclause prefixState.state [negate absent, negate term] := by
      simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, SourceMismatchSeed.absentBefore_term_handle,
        term, absent, mapLiteral, negate, Std.Sat.Literal.negate] using
        FoldProjection.afterTrace original prefixState.state prefixState.steps prefixState.checked
    exact FoldProjection.afterTrace row projected.state projected.steps projected.checked
  let longTerm : AvailableSubclause projected.state [term, negate e, negate r] := by
    let original := ofRow ((SourceMismatchSeed.termRows rename channel).row ⟨2, by change 2 < 3; decide⟩)
    have row : AvailableSubclause prefixState.state [term, negate e, negate r] := by
      simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, List.map_append, List.append_nil,
        term, e, r, requestHandle, SourceMismatchSeed.termBefore_enable, SourceMismatchSeed.termBefore_request,
        sourceRoleMap, (compile_rootsExact parameters).1, (compile_rootsExact parameters).2,
        (qualifierGuarded_roots .healthy channel).1, mapLiteral, negate, Std.Sat.Literal.negate] using
        FoldProjection.afterTrace original prefixState.state prefixState.steps prefixState.checked
    exact FoldProjection.afterTrace row projected.state projected.steps projected.checked
  let absenceUnit : AvailableSubclause projected.state (context (parameters := parameters) rename ++ [absent]) := by
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

  have two : 2 ≤ (((qualifierGuarded .healthy channel).slots (.primary (.enable channel)) ::
      (List.finRange parameters.buses).map (fun bus =>
        (qualifierGuarded .healthy channel).slots (.internal (.qualifierGuard .healthy bus channel)))).map (mapLiteral rename)).length := by
    simp only [List.length_map, List.length_cons, List.length_finRange]
    have positive := parameters.positiveBuses
    omega
  have treeOrigins := treeOriginals_afterTrace
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
    (qualifierTree rename .healthy channel) (qualifierTree_originals rename .healthy channel)
    prefixState.state prefixState.steps prefixState.checked
  have projectedOrigins := nonunaryTreeInputs_supported tree two (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) treeOrigins
    (allowed_native_count_le rename) (prefix_native_count_le rename prefixState)
  let current := prefixState.extend projected.state projected.steps projected.checked
  have currentSupported : PrefixOriginalSupport rename current :=
    traceOriginalSupport_append _ _ prefixState.steps projected.steps origins.supported projectedOrigins.1
  have qeOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps qe.row.id :=
    resultOrigin_append_left _ _ prefixState.steps projected.steps _ (projectedOrigins.2 e enableMember)
  have qgOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps qg.row.id :=
    resultOrigin_append_left _ _ prefixState.steps projected.steps _ (projectedOrigins.2 g guardMember)
  have notFlagOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps notFlag.row.id :=
    Or.inl (negatedFlagRows_allowed rename .healthy parameters.firstBus ⟨1, by decide⟩)
  have longGuardId : longGuard.row.id =
      ((guardRows rename .healthy channel parameters.firstBus).row ⟨2, by change 2 < 3; decide⟩).id := by
    dsimp only [longGuard]
    with_unfolding_all
      apply Eq.trans (subclause_indices_mpr_id rfl (by
        simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
          Rows.mapClause, List.map_cons, List.map_nil, List.map_append, List.append_nil,
          guardHandle, guardBefore_negated, (guardBefore_roots .healthy channel parameters.firstBus).2,
          g, nf, r, requestHandle, mapLiteral, negate, Std.Sat.Literal.negate]) _ _)
      apply subclause_indices_cast_id rfl
      simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, List.map_append, List.append_nil,
        guardHandle, guardBefore_negated, (guardBefore_roots .healthy channel parameters.firstBus).2,
        g, nf, r, requestHandle, mapLiteral, negate, Std.Sat.Literal.negate]
  have negativeTermId : negativeTerm.row.id =
      ((SourceMismatchSeed.absentRows rename channel).row ⟨1, by change 1 < 2; decide⟩).id := by
    dsimp only [negativeTerm]
    with_unfolding_all
      apply Eq.trans (subclause_indices_mpr_id rfl (by
        simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
          Rows.mapClause, List.map_cons, List.map_nil, SourceMismatchSeed.absentBefore_term_handle,
          term, absent, mapLiteral, negate, Std.Sat.Literal.negate]) _ _)
      apply subclause_indices_cast_id rfl
      simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, SourceMismatchSeed.absentBefore_term_handle,
        term, absent, mapLiteral, negate, Std.Sat.Literal.negate]
  have longTermId : longTerm.row.id =
      ((SourceMismatchSeed.termRows rename channel).row ⟨2, by change 2 < 3; decide⟩).id := by
    dsimp only [longTerm]
    with_unfolding_all
      apply Eq.trans (subclause_indices_mpr_id rfl (by
        simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
          Rows.mapClause, List.map_cons, List.map_nil, List.map_append, List.append_nil,
          term, e, r, requestHandle, SourceMismatchSeed.termBefore_enable, SourceMismatchSeed.termBefore_request,
          sourceRoleMap, (compile_rootsExact parameters).1, (compile_rootsExact parameters).2,
          (qualifierGuarded_roots .healthy channel).1, mapLiteral, negate, Std.Sat.Literal.negate]) _ _)
      apply subclause_indices_cast_id rfl
      simp [Bounded.Producer.rows, Gate.clauses, List.getElem_cons_succ, List.getElem_cons_zero,
        Rows.mapClause, List.map_cons, List.map_nil, List.map_append, List.append_nil,
        term, e, r, requestHandle, SourceMismatchSeed.termBefore_enable, SourceMismatchSeed.termBefore_request,
        sourceRoleMap, (compile_rootsExact parameters).1, (compile_rootsExact parameters).2,
        (qualifierGuarded_roots .healthy channel).1, mapLiteral, negate, Std.Sat.Literal.negate]
  have longGuardOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps longGuard.row.id := by
    rw [longGuardId]
    exact Or.inl (guardRows_allowed rename .healthy channel parameters.firstBus ⟨2, by decide⟩)
  have negativeTermOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps negativeTerm.row.id := by
    rw [negativeTermId]
    exact Or.inl (SourceMismatchSeed.absentRows_allowed rename channel ⟨1, by decide⟩)
  have longTermOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps longTerm.row.id := by
    rw [longTermId]
    exact Or.inl (SourceMismatchSeed.termRows_allowed rename channel ⟨2, by decide⟩)
  have absenceId : absenceUnit.row.id = (table.firstAbsent channel different).row.id := by
    dsimp only [absenceUnit]
    apply subclause_cast_id
    simp only [absent, SourceMismatchSeed.firstArrays_absent_handle]
  have absenceOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps absenceUnit.row.id := by
    rw [absenceId]
    exact resultOrigin_append_right _ _ prefixState.steps projected.steps _ (origins.firstAbsent channel different)
  have premiseOrigins : ∀ premise ∈ premises, ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps premise.row.row.id := by
    intro premise member
    simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact qeOrigin
    · exact qgOrigin
    · exact notFlagOrigin
    · exact longGuardOrigin
    · exact negativeTermOrigin
    · exact longTermOrigin
    · exact absenceOrigin
  have actual := Wrapper.local_unit_supported current.state
    (context (parameters := parameters) rename) premises (negate q) entails
    [e.1, r.1, g.1, nf.1, term.1, absent.1] covers
    (formula parameters).clauses.size (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) current.steps
    currentSupported (allowed_native_count_le rename) (prefix_native_count_le rename current) premiseOrigins
  simpa only [ProjectionOriginalSupport, SourceHealthyQualifiers.otherQualifier, id,
    prefixState, tree, q, e, r, g, nf, term, absent, projected, qe, qg, notFlag,
    longGuard, negativeTerm, longTerm, absenceUnit, premises, entails, covers,
    forced, current, SourcePrefix.extend, List.append_assoc] using actual

end Controller.NativeProof.Wrapper
