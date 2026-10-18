module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.Wrapper

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Controller-only original support for physical seeds and first masks. These
stronger invariants compose with the shared controller preparation schedule. -/
namespace Controller.NativeProof.Wrapper.ControllerOrigins
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceBusSchedule
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldAggregateProvenance
open Controller.NativeProof.SourceMismatchSeed Controller.NativeProof.SourceMismatchAdvance
open Controller.NativeProof.SourceMixedSchedule
variable {parameters : Parameters} {v : Nat}
theorem firstMaskRows_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels)
    (index : Fin 4) :
    SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      ((SourceMismatchAdvance.initialMaskRowsExact rename side channel).row
        ⟨index.val, by change index.val < 4; exact index.isLt⟩).id := by
  simpa only [SourceMismatchAdvance.initialMaskRowsExact, SourceMismatchBranch.emitRowsExact,
    SourceMismatchBranch.ownedRow, SourceCongruence.emitOwner, SourceRows.before, id] using
    SourceMismatchBranch.emitRow_allowed rename (SourceCongruence.initialMaskBefore side channel)
      (.internal (.mask side parameters.firstBus channel))
      (.xor ((SourceCongruence.initialMaskBefore side channel).slots (.internal (.flag side parameters.firstBus)))
        ((SourceCongruence.initialMaskBefore side channel).slots (.internal (.absent side parameters.firstBus channel))))
      (SourceEqualSchedule.initial_mask_before_controller side channel)
      ⟨index.val, by change index.val < 4; exact index.isLt⟩

theorem groupTree_originals {parameters : Parameters} (rename : Nat → Fin v)
    (group : SourceMismatchSeed.Group)
    (nonempty : SourceMismatchSeed.groupInputs (parameters := parameters) group ≠ []) :
    TreeOriginals (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      (SourceMismatchSeed.groupTree rename group nonempty) := by
  cases group with
  | drivers =>
    unfold SourceMismatchSeed.groupTree
    apply allocateForest_originals
    · exact initialForest_originals _ _ _
    · simpa only [SourceFoldOwners.driverRows] using
        actualFoldRows_allowed rename (firstArrays parameters) (.internal .driver) .conjunction
          (SourceFoldOwners.driverInputs parameters)
          (SourceFoldOwners.driver_before_interface.trans SourceFoldOwners.interface_before_controller)
  | remaining =>
    unfold SourceMismatchSeed.groupTree
    apply allocateForest_originals
    · exact initialForest_originals _ _ _
    · simpa only [SourceFoldOwners.remainingRows] using
        actualFoldRows_allowed rename (SourceFoldOwners.driverCursor parameters) (.internal .remaining) .conjunction
          (SourceFoldOwners.remainingInputs parameters)
          (SourceFoldOwners.remaining_before_interface.trans SourceFoldOwners.interface_before_controller)

theorem firstMaskForward_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels) :
    SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      (SourceMismatchAdvance.initialMaskForward rename side channel).row.id := by
  cases side
  all_goals
    unfold SourceMismatchAdvance.initialMaskForward
    simp only [retarget, ofRow, id]
    repeat' rw [SourceMixedSchedule.subclause_indices_cast_id rfl (by
      simp [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceCongruence.maskFlag,
        SourceCongruence.maskAbsent, SourceCongruence.maskOutput, SourceFoldProjection.mapLiteral,
        negate, Std.Sat.Literal.negate])]
  · exact firstMaskRows_allowed (parameters := parameters) rename .healthy channel ⟨3, by decide⟩
  · exact firstMaskRows_allowed (parameters := parameters) rename .faulty channel ⟨2, by decide⟩

theorem firstMaskBackward_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels) :
    SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      (SourceMismatchAdvance.initialMaskBackward rename side channel).row.id := by
  cases side
  all_goals
    unfold SourceMismatchAdvance.initialMaskBackward
    simp only [retarget, ofRow, id]
    repeat' rw [SourceMixedSchedule.subclause_indices_cast_id rfl (by
      simp [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceCongruence.maskFlag,
        SourceCongruence.maskAbsent, SourceCongruence.maskOutput, SourceFoldProjection.mapLiteral,
        negate, Std.Sat.Literal.negate])]
  · exact firstMaskRows_allowed (parameters := parameters) rename .healthy channel ⟨1, by decide⟩
  · exact firstMaskRows_allowed (parameters := parameters) rename .faulty channel ⟨0, by decide⟩

theorem maskValueOriginal_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (side : Side) (channel : Fin parameters.channels) (absence : Bool) :
    SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      (SourceMismatchAdvance.maskValueOriginal rename side channel absence).row.id := by
  cases side <;> cases absence
  · exact firstMaskForward_allowed rename .healthy channel
  · exact firstMaskBackward_allowed rename .healthy channel
  · exact firstMaskBackward_allowed rename .faulty channel
  · exact firstMaskForward_allowed rename .faulty channel

theorem faultyProductRows_allowed {parameters : Parameters} (rename : Nat → Fin v) (index : Fin 4) :
    SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      ((SourceMismatchBranch.faultyProductRows (parameters := parameters) rename).row
        ⟨index.val, by change index.val < 4; exact index.isLt⟩).id := by
  have retained : SourceFoldOwners.EntriesBefore
      (SourceMismatchBranch.faultyProductCursor (parameters := parameters)) (controller parameters) :=
    (SourceFoldOwners.emitNative_before _ _ _).trans SourceFoldOwners.interface_before_controller
  simpa only [SourceMismatchBranch.faultyProductRows, SourceMismatchBranch.emitRowsExact,
    SourceMismatchBranch.ownedRow, SourceCongruence.emitOwner, SourceRows.before] using
    SourceMismatchBranch.emitRow_allowed rename (SourceMismatchBranch.healthyFlagCursor (parameters := parameters))
      (.internal (.firstProduct .faulty)) (.and (SourceMismatchBranch.faultyProductInputs (parameters := parameters)))
      retained ⟨index.val, by change index.val < 4; exact index.isLt⟩

theorem faultyFlagRows_allowed {parameters : Parameters} (rename : Nat → Fin v) (index : Fin 2) :
    SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      ((SourceMismatchBranch.faultyFlagRows (parameters := parameters) rename).row
        ⟨index.val, by change index.val < 2; exact index.isLt⟩).id := by
  simpa only [SourceMismatchBranch.faultyFlagRows, SourceMismatchBranch.emitRowsExact,
    SourceMismatchBranch.ownedRow, SourceCongruence.emitOwner, SourceRows.before] using
    SourceMismatchBranch.emitRow_allowed rename (SourceMismatchBranch.faultyProductCursor (parameters := parameters))
      (.internal (.flag .faulty parameters.firstBus))
      (.not ((SourceMismatchBranch.faultyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .faulty))))
      SourceFoldOwners.interface_before_controller ⟨index.val, by change index.val < 2; exact index.isLt⟩

theorem maskValueAt_supported {parameters : Parameters} (rename : Nat → Fin v)
    (proofPrefix : SourcePrefix (parameters := parameters) rename) (side : Side)
    (channel : Fin parameters.channels) (absence : Bool)
    (seed : AvailableSubclause proofPrefix.state
      (SourceMismatchAdvance.mixedContext (parameters := parameters) rename ++
        [SourceMismatchAdvance.absenceValue rename channel absence]))
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename proofPrefix)
    (seedOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps seed.row.id) :
    SourceMixedSchedule.ProjectionOriginalSupport rename proofPrefix
      (SourceMismatchAdvance.maskValueAt rename proofPrefix side channel absence seed) := by
  let input := SourceMismatchAdvance.absenceValue rename channel absence
  let output := SourceMismatchAdvance.firstMaskValue rename side channel absence
  let context := SourceMismatchAdvance.mixedContext (parameters := parameters) rename
  let original := SourceMismatchAdvance.maskValueOriginal rename side channel absence
  let row := FoldProjection.afterTrace original proofPrefix.state proofPrefix.steps proofPrefix.checked
  let left : AvailableSubclause proofPrefix.state (negate input :: (context ++ [output])) := retarget row (by
    intro literal member
    simp only [input, output, context, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with old | pivot | final
    · exact Or.inr (Or.inl old)
    · exact Or.inl pivot
    · exact Or.inr (Or.inr final))
  let right : AvailableSubclause proofPrefix.state (input :: context) := retarget seed (by
    intro literal member
    simp only [input, context, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact member.elim Or.inr Or.inl)
  have leftOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps left.row.id :=
    Or.inl (maskValueOriginal_allowed rename side channel absence)
  have actual := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps proofPrefix.state
    input (context ++ [output]) context left right supported
    (SourceMixedSchedule.allowed_native_count_le rename)
    (SourceMixedSchedule.prefix_native_count_le rename proofPrefix) leftOrigin seedOrigin
  simpa only [SourceMismatchAdvance.maskValueAt, SourceMixedSchedule.ProjectionOriginalSupport,
    input, output, context, original, row, left, right, retarget] using actual

/-- Complementary cofactor subclauses merge before the physical healthy unit
is discharged. Both operations are ordinary resolution with stronger-row reuse. -/

theorem faultyZeroInputAt_supported {parameters : Parameters} (rename : Nat → Fin v)
    (proofPrefix : SourcePrefix (parameters := parameters) rename) (index : Fin 3)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename proofPrefix) :
    SourceMixedSchedule.ProjectionOriginalSupport rename proofPrefix
      (SourceMismatchAdvance.faultyZeroInputAt rename proofPrefix index) := by
  let base := initialState (relabel rename (formula parameters))
  let product := SourceFoldProjection.mapLiteral rename ((SourceMismatchBranch.healthyFlagCursor (parameters := parameters)).lastID + 1, true)
  let flag := SourceFoldProjection.mapLiteral rename ((SourceMismatchBranch.faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := SourceFoldProjection.mapLiteral rename
    ((SourceMismatchBranch.faultyProductInputs (parameters := parameters))[index.val]'(by
      simpa [SourceMismatchBranch.faultyProductInputs] using index.isLt))
  let originalLeft : AvailableSubclause base [negate product, input] := by
    have row := ofRow ((SourceMismatchBranch.faultyProductRows (parameters := parameters) rename).row
      ⟨index.val, by change index.val < 4; omega⟩)
    have bound : index.val < (SourceMismatchBranch.faultyProductInputs (parameters := parameters)).length := by
      simpa [SourceMismatchBranch.faultyProductInputs] using index.isLt
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_append, bound,
      Rows.mapClause, SourceFoldProjection.mapLiteral, product, input, base, negate, Std.Sat.Literal.negate] using row
  let originalRight : AvailableSubclause base [product, flag] :=
    retarget (ofRow ((SourceMismatchBranch.faultyFlagRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 2; decide⟩)) (by
        intro literal member
        simp [SourceMismatchBranch.faultyProductCursor, Cursor.emitNative, Cursor.emit, Cursor.assign,
          Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceFoldProjection.mapLiteral, product, flag,
          List.mem_cons, List.not_mem_nil] at member ⊢ <;> aesop)
  let left := FoldProjection.afterTrace originalLeft proofPrefix.state proofPrefix.steps proofPrefix.checked
  let right := FoldProjection.afterTrace originalRight proofPrefix.state proofPrefix.steps proofPrefix.checked
  have leftAllowed : SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename originalLeft.row.id := by
    dsimp only [originalLeft]
    with_unfolding_all
      repeat' rw [SourceMixedSchedule.subclause_indices_mpr_id rfl (by
        fin_cases index <;> simp [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceFoldProjection.mapLiteral,
          SourceMismatchBranch.faultyProductInputs, product, input, base, negate, Std.Sat.Literal.negate]),
        SourceMixedSchedule.subclause_indices_cast_id rfl (by
        fin_cases index <;> simp [Bounded.Producer.rows, Gate.clauses, Rows.mapClause, SourceFoldProjection.mapLiteral,
          SourceMismatchBranch.faultyProductInputs, product, input, base, negate, Std.Sat.Literal.negate])]
    exact faultyProductRows_allowed rename ⟨index.val, by omega⟩
  have actual := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) proofPrefix.steps proofPrefix.state
    product [input] [flag] left right supported (SourceMixedSchedule.allowed_native_count_le rename)
    (SourceMixedSchedule.prefix_native_count_le rename proofPrefix) (Or.inl leftAllowed)
    (Or.inl (faultyFlagRows_allowed rename ⟨0, by decide⟩))
  simpa only [SourceMismatchAdvance.faultyZeroInputAt, SourceMixedSchedule.ProjectionOriginalSupport,
    base, product, flag, input, originalLeft, originalRight, left, right, retarget] using actual

/-- Optional requirements may choose any observed leaf as their discrepancy
witness. Their unsatisfiability therefore excludes every observed discrepancy. -/

theorem groupCofactorAt_supported {parameters : Parameters} (rename : Nat → Fin v)
    (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (group : SourceMismatchSeed.Group)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename proofPrefix) :
    SourceMixedSchedule.ProjectionOriginalSupport rename proofPrefix
      (SourceMismatchAdvance.groupCofactorAt rename proofPrefix group) := by
  have actual := faultyZeroInputAt_supported rename proofPrefix
    (SourceMismatchSeed.groupIndex group) supported
  simpa only [SourceMismatchAdvance.groupCofactorAt,
    SourceMixedSchedule.ProjectionOriginalSupport, retarget] using actual

/-- A negative input kills its native AND tree using only that input unit and
the tree's retained original rows, including unary identity trees. -/

theorem otherAbsenceAt_supported {parameters : Parameters} (rename : Nat → Fin v)
    (proofPrefix : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (different : channel ≠ parameters.bridge.target)
    (supported : SourceMixedSchedule.PrefixOriginalSupport rename proofPrefix) :
    SourceMixedSchedule.ProjectionOriginalSupport rename proofPrefix
      (otherAbsenceAt rename proofPrefix channel different) := by
  let group := otherGroup (parameters := parameters) channel
  let first := groupCofactorAt rename proofPrefix group
  let root := SourceFoldProjection.mapLiteral rename (groupOutput (parameters := parameters) group)
  let flag := SourceFoldProjection.mapLiteral rename ((SourceMismatchBranch.faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := SourceFoldProjection.mapLiteral rename ((firstArrays parameters).slots
    (.internal (.absent .healthy parameters.firstBus channel)))
  let originalTree := groupTree rename group (otherGroup_nonempty channel different)
  have combinedPrefix : runSteps (initialState (relabel rename (formula parameters)))
      (proofPrefix.steps ++ first.steps) = some first.state := by
    rw [runSteps_append, proofPrefix.checked]
    exact first.checked
  let tree := originalTree.afterTrace first.state (proofPrefix.steps ++ first.steps) combinedPrefix
  let projected := projectTreeInputs tree
  have inputMember : input ∈ (groupInputs (parameters := parameters) group).map (SourceFoldProjection.mapLiteral rename) :=
    List.mem_map.mpr ⟨_, otherGroup_member channel different, rfl⟩
  let rootClause : AvailableSubclause projected.state [flag, root] :=
    afterTrace first.result projected.state projected.steps projected.checked
  have firstSupport := groupCofactorAt_supported rename proofPrefix group supported
  have originals := treeOriginals_afterTrace
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) originalTree
    (groupTree_originals rename group (otherGroup_nonempty channel different))
    first.state (proofPrefix.steps ++ first.steps) combinedPrefix
  have projectionSupport := projectTreeInputs_supported tree (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) originals
    (SourceMixedSchedule.allowed_native_count_le rename)
    (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
      (runSteps_lastId_le first.checked))
  have complete := traceOriginalSupport_append _ _ (proofPrefix.steps ++ first.steps)
    projected.steps firstSupport.1 projectionSupport.1
  have rootOrigin := resultOrigin_append_right _ _ (proofPrefix.steps ++ first.steps)
    projected.steps first.result.row.id firstSupport.2
  have directionOrigin : CertificateOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      projected.steps (projected.results input inputMember) := projectionSupport.2 input inputMember
  unfold otherAbsenceAt
  dsimp only [id]
  split
  · rename_i same direction
    unfold SourceMixedSchedule.ProjectionOriginalSupport
    constructor
    · simpa only [id, projected, tree, originalTree, group, first, List.append_assoc] using complete
    · simpa only [projected, tree, originalTree, group, first, rootClause, afterTrace,
        retarget, id, List.append_assoc] using rootOrigin
  · rename_i implication direction
    let right : AvailableSubclause projected.state [root, flag] := retarget rootClause (by
      intro literal member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      exact member.elim (fun equal => Or.inr equal) (fun equal => Or.inl equal))
    have implicationOrigin : ResultOrigin (formula parameters).clauses.size
        (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
        ((proofPrefix.steps ++ first.steps) ++ projected.steps) implication.row.id := by
      apply resultOrigin_append_left
      with_unfolding_all
        rw [direction] at directionOrigin
      exact directionOrigin
    have joined := SourceMixedSchedule.longMerge_supported (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename)
      ((proofPrefix.steps ++ first.steps) ++ projected.steps) projected.state root [input] [flag]
      implication right complete (SourceMixedSchedule.allowed_native_count_le rename)
      (Nat.le_trans (SourceMixedSchedule.prefix_native_count_le rename proofPrefix)
        (Nat.le_trans (runSteps_lastId_le first.checked) (runSteps_lastId_le projected.checked)))
      implicationOrigin rootOrigin
    simpa only [SourceMixedSchedule.ProjectionOriginalSupport, projected, tree,
      originalTree, group, first, root, input, flag, right, rootClause, retarget,
      id, List.append_assoc] using joined

end Controller.NativeProof.Wrapper.ControllerOrigins
