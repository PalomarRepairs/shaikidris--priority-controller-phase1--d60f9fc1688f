module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.WrapperBroadPrimitives

@[expose] public section

/-! The single-bus target unit retains native controller origins after preparation. -/
namespace Controller.NativeProof.Wrapper
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceBusAdvance Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceSuffixSelector
open Controller.NativeProof.SourceQualifierSchedule Controller.NativeProof.SourceDecoderTraversal
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceHealthyOne
variable {parameters : Parameters} {v : Nat}

theorem oneBusTarget_origins (rename : Nat → Fin v) (start : SourcePrefix (parameters := parameters) rename)
    (drive : parameters.drive = true) (one : parameters.buses = 1)
    (supported : SourceDecoderSchedule.PrefixOriginalSupport rename start) :
    SourceDecoderSchedule.ProjectionOriginalSupport rename start (SourceHealthyOne.oneBusTarget rename start drive one) := by
  let guard := guardOrFlagAt rename start .faulty parameters.bridge.target parameters.firstBus
  let g := mapLiteral rename (guardHandle .faulty parameters.bridge.target parameters.firstBus)
  let guardUnit : AvailableSubclause guard.state (cofactor (parameters := parameters) rename ++ [g]) := by
    apply retarget guard.result
    intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · exact List.mem_append_right _ (List.mem_singleton.mpr same)
    · subst literal
      rw [firstFlagInput_eq_sourceRoleMap]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  let afterGuard := start.extend guard.state guard.steps guard.checked
  let enabled := targetEnableAt rename afterGuard drive
  let prefixState := afterGuard.extend enabled.state enabled.steps enabled.checked
  let tree := (qualifierTree rename .faulty parameters.bridge.target).afterTrace
    enabled.state prefixState.steps prefixState.checked
  let inputs := (qualifierGuarded .faulty parameters.bridge.target).slots (.primary (.enable parameters.bridge.target)) ::
    (List.finRange parameters.buses).map (fun bus =>
      (qualifierGuarded .faulty parameters.bridge.target).slots (.internal (.qualifierGuard .faulty bus parameters.bridge.target)))
  let units : ∀ leaf ∈ inputs.map (mapLiteral rename),
      AvailableSubclause enabled.state (cofactor (parameters := parameters) rename ++ [leaf]) := by
    intro leaf member
    let e := mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots (.primary (.enable parameters.bridge.target)))
    have allGuard : ∀ bus : Fin parameters.buses, bus = parameters.firstBus := by
      intro bus
      apply Fin.ext
      have bound := bus.isLt
      simp only [Parameters.firstBus]
      omega
    have possibilities : leaf = e ∨ leaf = g := by
      have expanded : leaf = e ∨ ∃ bus ∈ List.finRange parameters.buses,
          mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
            (.internal (.qualifierGuard .faulty bus parameters.bridge.target))) = leaf := by
        simpa only [inputs, List.map_cons, List.mem_cons, List.map_map, List.mem_map, Function.comp_def] using member
      rcases expanded with enable | guarded
      · exact Or.inl enable
      · obtain ⟨bus, listed, equal⟩ := guarded
        exact Or.inr (by simpa only [qualifierGuarded_guard_handle, allGuard, g] using equal.symm)
    by_cases isEnable : leaf = e
    · subst leaf
      apply retarget enabled.result
      intro literal member
      simpa only [e, (qualifierGuarded_roots .faulty parameters.bridge.target).1,
        sourceRoleMap, (compile_rootsExact parameters).1] using List.mem_append_right (cofactor (parameters := parameters) rename) member
    · have same := possibilities.resolve_left isEnable
      exact same ▸ FoldProjection.afterTrace guardUnit enabled.state enabled.steps enabled.checked
  let forced := TreeUnits.force tree (cofactor (parameters := parameters) rename) units

  have guardOrigins := broadGuardOrFlagAt_supported rename start .faulty parameters.bridge.target parameters.firstBus supported
  have enableOrigins := broadTargetEnableAt_supported rename afterGuard drive guardOrigins.1
  have treeOrigins := treeOriginals_afterTrace
    (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename)
    (qualifierTree rename .faulty parameters.bridge.target)
    (treeOriginals_mono (SourceDecoderSchedule.controller_original_allowed rename) _
      (qualifierTree_originals rename .faulty parameters.bridge.target))
    enabled.state prefixState.steps prefixState.checked
  have unitOrigins : ∀ leaf member, ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) prefixState.steps (units leaf member).row.id := by
    intro leaf member
    let e := mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots (.primary (.enable parameters.bridge.target)))
    by_cases isEnable : leaf = e
    · subst leaf
      simpa only [units, id, subclause_dite_id, e, dite_eq_left rfl, dite_true, retarget,
        prefixState, SourcePrefix.extend, enabled] using enableOrigins.2
    · have allGuard : ∀ bus : Fin parameters.buses, bus = parameters.firstBus := by
        intro bus; apply Fin.ext
        have bound := bus.isLt
        simp only [Parameters.firstBus]
        omega
      have possibilities : leaf = e ∨ leaf = g := by
        have expanded : leaf = e ∨ ∃ bus ∈ List.finRange parameters.buses,
            mapLiteral rename ((qualifierGuarded .faulty parameters.bridge.target).slots
              (.internal (.qualifierGuard .faulty bus parameters.bridge.target))) = leaf := by
          simpa only [inputs, List.map_cons, List.mem_cons, List.map_map, List.mem_map, Function.comp_def] using member
        rcases expanded with enable | guarded
        · exact Or.inl enable
        · obtain ⟨bus, listed, equal⟩ := guarded
          exact Or.inr (by simpa only [qualifierGuarded_guard_handle, allGuard, g] using equal.symm)
      have same : leaf = g := possibilities.resolve_left isEnable
      subst leaf
      dsimp only [e] at isEnable
      have indexEqual : (units g member).row.id = guardUnit.row.id := by
        simp only [units, id, subclause_dite_id, dite_eq_right isEnable, afterTrace]
      rw [indexEqual]
      exact resultOrigin_append_right _ _ afterGuard.steps enabled.steps _ guardOrigins.2
  have actual := Wrapper.tree_force_supported rename prefixState tree (cofactor (parameters := parameters) rename) units
    enableOrigins.1 treeOrigins unitOrigins
  let emitted := SourceHealthyOne.oneBusTarget rename start drive one
  have emittedSteps : emitted.steps = (guard.steps ++ enabled.steps) ++ forced.steps := rfl
  have emittedId : emitted.result.row.id = forced.result.row.id := by
    unfold emitted SourceHealthyOne.oneBusTarget
    dsimp only [id]
    with_unfolding_all
      apply subclause_indices_mpr_id rfl
      simp only [SourceDecoderEvaluation.qualifierLiteral, ← qualifierOutput_decoderStart, qualifierOutput]
  have same : prefixState.steps ++ forced.steps = start.steps ++ emitted.steps := by
    rw [emittedSteps]
    simp only [prefixState, afterGuard, SourcePrefix.extend, List.append_assoc]
  constructor
  · change TraceOriginalSupport (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (start.steps ++ emitted.steps)
    rw [← same]
    exact actual.1
  · change ResultOrigin (formula parameters).clauses.size
      (SourceDecoderSchedule.AllowedOriginal (parameters := parameters) rename) (start.steps ++ emitted.steps) emitted.result.row.id
    rw [← same, emittedId]
    exact actual.2

end Controller.NativeProof.Wrapper
