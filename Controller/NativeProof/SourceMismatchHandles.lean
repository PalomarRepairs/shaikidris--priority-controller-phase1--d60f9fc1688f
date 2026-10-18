module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMismatchBranch

@[expose] public section

/-! Syntactic frames and allocated positive phases connect physical drive
units to the exact source interface rows. -/
namespace Controller.NativeProof.SourceMismatchHandles
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceSlotFrames
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceMismatchBranch
open Controller.NativeProof.SourceFoldProjection Controller.NativeProof.FoldProjection
variable {parameters : Parameters} {v : Nat}

theorem firstAbsentStep_positive (cursor : Cursor parameters)
    (side : Side) (channel : Fin parameters.channels) :
    ((firstAbsentStep parameters cursor channel).slots
      (.internal (.absent side parameters.firstBus channel))).2 = true := by
  cases side <;> simp [firstAbsentStep, Cursor.emitNative, Cursor.emit, Cursor.assign]

theorem firstAbsentStep_other (cursor : Cursor parameters) (side : Side)
    (query channel : Fin parameters.channels) (different : channel ≠ query) :
    (firstAbsentStep parameters cursor channel).slots (.internal (.absent side parameters.firstBus query)) =
      cursor.slots (.internal (.absent side parameters.firstBus query)) := by
  cases side <;> simp [firstAbsentStep, Cursor.emitNative, Cursor.emit, Cursor.assign,
    different, Ne.symm different]

/-- Membership selects an actual allocated NOT output; no positive-phase
assumption about the incoming cursor is needed. -/
theorem firstAbsentSteps_positive (side : Side) (query : Fin parameters.channels)
    (values : List (Fin parameters.channels)) (cursor : Cursor parameters) (member : query ∈ values) :
    ((values.foldl (firstAbsentStep parameters) cursor).slots
      (.internal (.absent side parameters.firstBus query))).2 = true := by
  induction values generalizing cursor with
  | nil => simp at member
  | cons channel rest ih =>
      by_cases later : query ∈ rest
      · exact ih (firstAbsentStep parameters cursor channel) later
      · have same : query = channel := (List.mem_cons.mp member).resolve_right later
        subst channel
        have frame := foldl_slot_mem (firstAbsentStep parameters)
          (.internal (.absent side parameters.firstBus query)) rest
          (by intro current index contained
              apply firstAbsentStep_other
              intro equal
              exact later (equal ▸ contained))
          (firstAbsentStep parameters cursor query)
        simpa only [List.foldl_cons, frame] using firstAbsentStep_positive cursor side query

theorem firstArrays_absent_positive (side : Side) (channel : Fin parameters.channels) :
    ((firstArrays parameters).slots (.internal (.absent side parameters.firstBus channel))).2 = true := by
  rw [firstArrays_eq]
  exact firstAbsentSteps_positive side channel _ _ (by simp)

theorem laterBus_first_absent (side querySide : Side) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) (different : bus ≠ parameters.firstBus) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.absent querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.absent querySide parameters.firstBus channel)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.absent querySide parameters.firstBus channel))
    (fun current index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign,
      different, Ne.symm different])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current index
  simp [Cursor.foldNative, Cursor.assign]

theorem eligible_first_absent (side querySide : Side) (channel query : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (eligible parameters side channel cursor).slots (.internal (.absent querySide parameters.firstBus query)) =
      cursor.slots (.internal (.absent querySide parameters.firstBus query)) := by
  unfold eligible
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current bus
  apply emitNative_other
  simp

theorem tail_first_absent (side querySide : Side) (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (SourceController.tail parameters side cursor).slots (.internal (.absent querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.absent querySide parameters.firstBus channel)) := by
  unfold SourceController.tail
  rw [foldl_slot _ (.internal (.absent querySide parameters.firstBus channel))
    (fun current query => eligible_first_absent side querySide query channel current)]
  rw [negateFlags_slot]
  rw [foldl_slot_mem _ (.internal (.absent querySide parameters.firstBus channel)) _ (by
    intro current bus member
    apply laterBus_first_absent
    have nonzero : bus.val ≠ 0 := by simpa using (List.mem_filter.mp member).2
    intro equal
    apply nonzero
    simpa [Parameters.firstBus] using congrArg Fin.val equal)]
  exact initialMasks_absent side querySide channel _ cursor

theorem decoderNode_first_absent (side querySide : Side) (channel : Fin parameters.channels)
    (node : Fin parameters.decoder.nodeCount) (cursor : Cursor parameters) :
    (decoderNode parameters side node cursor).slots (.internal (.absent querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.absent querySide parameters.firstBus channel)) := by
  unfold decoderNode
  cases parameters.decoder.node node with
  | zero => apply emitNative_other; simp
  | input query => apply assign_other; simp
  | disj children => apply foldNative_other; simp
  | guard child labels =>
      rw [assign_other _ _ _ _ (by simp)]
      exact guardChain_slot side node _ labels _ cursor
  | liveAnd left right => apply emitNative_other; simp

theorem attachDecoder_first_absent (side querySide : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (attachDecoder parameters side cursor).slots (.internal (.absent querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.absent querySide parameters.firstBus channel)) :=
  foldl_slot _ _ (fun current node => decoderNode_first_absent side querySide channel node current) _ cursor

theorem newObservations_first_absent (side : Side) (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (newObservations parameters cursor).slots (.internal (.absent side parameters.firstBus channel)) =
      cursor.slots (.internal (.absent side parameters.firstBus channel)) := by
  unfold newObservations
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current output
  apply emitNative_other
  simp

theorem compiled_first_absent (side : Side) (channel : Fin parameters.channels) :
    (compile parameters).slots (.internal (.absent side parameters.firstBus channel)) =
      (firstArrays parameters).slots (.internal (.absent side parameters.firstBus channel)) := by
  unfold compile
  rw [newObservations_first_absent, attachDecoder_first_absent, attachDecoder_first_absent,
    originalObservations_slot]
  unfold controller
  rw [tail_first_absent, tail_first_absent, interface_absent]

theorem wireCursor_first_absent (side : Side) (channel : Fin parameters.channels) :
    (wireCursor (parameters := parameters)).slots (.internal (.absent side parameters.firstBus channel)) =
      (firstArrays parameters).slots (.internal (.absent side parameters.firstBus channel)) := by
  simp [wireCursor, remainingCursor, driverCursor, Cursor.foldNative, Cursor.emitNative,
    Cursor.emit, Cursor.assign]

theorem targetPhysicalUnit (rename : Nat → Fin v) (drive : parameters.drive = true) :
    mapLiteral rename (physicalUnit (parameters := parameters) ⟨0, by decide⟩) =
      negate (mapLiteral rename ((wireCursor (parameters := parameters)).slots
        (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)))) := by
  have phase := firstArrays_absent_positive (parameters := parameters) .healthy parameters.bridge.target
  have unit := (physicalUnit_drive_one (parameters := parameters) drive).1
  rw [unit]
  unfold sourceRoleMap
  rw [compiled_first_absent, wireCursor_first_absent]
  simp [mapLiteral, negate, Std.Sat.Literal.negate, phase]

theorem healthyProduct_original_allowed (rename : Nat → Fin v) :
    AllowedOriginal (parameters := parameters) rename
      ((healthyProductRows (parameters := parameters) rename).row ⟨0, by change 0 < 4; decide⟩).id := by
  have retained : EntriesBefore (healthyProductCursor (parameters := parameters)) (controller parameters) :=
    (emitNative_before _ _ _).trans (healthyFlag_before_interface.trans interface_before_controller)
  simpa only [healthyProductRows, emitRowsExact, ownedRow, emitOwner, SourceRows.before] using emitRow_allowed rename (wireCursor (parameters := parameters))
    (.internal (.firstProduct .healthy))
    (.and [(wireCursor (parameters := parameters)).slots
      (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)),
      (wireCursor (parameters := parameters)).slots (.internal .driver),
      (wireCursor (parameters := parameters)).slots (.internal .remaining)]) retained
    ⟨0, by change 0 < 4; decide⟩

theorem healthyFlag_original_allowed (rename : Nat → Fin v) :
    AllowedOriginal (parameters := parameters) rename
      ((healthyFlagRows (parameters := parameters) rename).row ⟨0, by change 0 < 2; decide⟩).id := by
  simpa only [healthyFlagRows, emitRowsExact, ownedRow, emitOwner, SourceRows.before] using emitRow_allowed rename (healthyProductCursor (parameters := parameters))
    (.internal (.flag .healthy parameters.firstBus))
    (.not ((healthyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .healthy))))
    (healthyFlag_before_interface.trans interface_before_controller) ⟨0, by change 0 < 2; decide⟩

theorem healthyInterface_original_parents (rename : Nat → Fin v) :
    SourceBusSchedule.AllParentsAllowed (AllowedOriginal (parameters := parameters) rename)
      (healthyFlagFromTargetAbsent (parameters := parameters) rename).steps := by
  simp only [healthyFlagFromTargetAbsent, longMerge]
  apply SourceBusSchedule.merge_parents_allowed
  · exact healthyProduct_original_allowed rename
  · exact healthyFlag_original_allowed rename

/-- The drive-one physical U unit consumes the actual U ∨ P₁ derivation.
Missing pivots retain stronger rows; at most two resolutions are emitted. -/
def healthyFlagFromPhysicalUnit (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)] 2 := by
  let first := healthyFlagFromTargetAbsent (parameters := parameters) rename
  let absent := mapLiteral rename ((wireCursor (parameters := parameters)).slots
    (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)))
  let flag := mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)
  let physical := physicalUnitRow (parameters := parameters) rename ⟨0, by decide⟩
  have original : Rows.Available (initialState (relabel rename (formula parameters))) [negate absent] :=
    ⟨physical.id, (by simpa only [targetPhysicalUnit rename drive] using physical.present), physical.bound⟩
  let left := FoldProjection.afterTrace (ofRow original) first.state first.steps first.checked
  let joined := longMerge first.state absent [] [flag] left first.result
  refine ⟨joined.state, first.steps ++ joined.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact longMerge_run _ _ _ _ _ _
  · exact longMerge_result _ _ _ _ _ _
  · have one := first.count
    have two := longMerge_count first.state absent [] [flag] left first.result
    simp only [List.length_append, joined]
    omega


theorem healthyFlag_handle :
    sourceRoleMap parameters (.internal (.flag .healthy parameters.firstBus)) =
      ((healthyProductCursor (parameters := parameters)).lastID + 1, true) := by
  unfold sourceRoleMap
  rw [compiled_first_flag]
  change ((faultyProductCursor (parameters := parameters)).emitNative
      (.internal (.flag .faulty parameters.firstBus))
      (.not ((faultyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .faulty))))).slots
      (.internal (.flag .healthy parameters.firstBus)) = _
  rw [emitNative_other _ _ _ _ (by simp)]
  unfold faultyProductCursor
  rw [emitNative_other _ _ _ _ (by simp)]
  simp [healthyFlagCursor, Cursor.emitNative, Cursor.emit, Cursor.assign]

/-- The returned unit targets the final actual compiled healthy first flag. -/
def healthyFlagUnit (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (sourceRoleMap parameters (.internal (.flag .healthy parameters.firstBus)))] 2 := by
  let actual := healthyFlagFromPhysicalUnit (parameters := parameters) rename drive
  refine ⟨actual.state, actual.steps, actual.checked, retarget actual.result ?_, actual.count⟩
  intro literal member
  simpa only [healthyFlag_handle] using member


/-- A reused stronger result remains an original row; a fresh result names
its actual emitted inference, strictly beyond the original range. -/
def ResultOrigin (originalCount : Nat) (allowed : Nat → Prop)
    (steps : List (Step v)) (id : Nat) : Prop :=
  allowed id ∨ ∃ earlier ∈ steps, earlier.id = id ∧ originalCount < id

theorem originalMerge_result_origin (state : State v) (allowed : Nat → Prop)
    (leftId rightId : Nat) (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (one : allowed leftId) (two : allowed rightId) :
    ResultOrigin state.lastId allowed (merge state leftId rightId pivot left right).steps
      (merge state leftId rightId pivot left right).rowId := by
  unfold merge
  split
  · exact Or.inl one
  · split
    · exact Or.inl two
    · exact Or.inr ⟨RUP.resolutionStep state leftId rightId pivot left right, by simp,
        rfl, by change state.lastId < state.lastId + 1; omega⟩

/-- Appending one actual merge preserves original provenance and refers only
to the earlier emitted result when that result is not original. -/
theorem appendMerge_supported (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (state : State v)
    (leftId rightId : Nat) (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (supported : SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (one : allowed leftId) (two : ResultOrigin originalCount allowed priorSteps rightId)
    (rightBound : rightId ≤ state.lastId) :
    SourceBusSchedule.TraceOriginalSupport originalCount allowed
      (priorSteps ++ (merge state leftId rightId pivot left right).steps) := by
  unfold merge
  split
  · simpa only [List.append_nil] using supported
  · split
    · simpa only [List.append_nil] using supported
    · intro step member parent parentMember
      rcases List.mem_append.mp member with old | fresh
      · have previous := supported step old parent parentMember
        refine ⟨previous.1, ?_⟩
        intro derived
        rcases previous.2 derived with ⟨earlier, contained, same, order⟩
        exact ⟨earlier, List.mem_append_left _ contained, same, order⟩
      · have same := List.mem_singleton.mp fresh
        subst step
        change parent ∈ [leftId, rightId] at parentMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at parentMember
        rcases parentMember with same | same
        · subst parent
          refine ⟨fun _ => one, ?_⟩
          intro derived
          have bound := originalBound leftId one
          omega
        · subst parent
          rcases two with original | ⟨earlier, contained, same, derived⟩
          · refine ⟨fun _ => original, ?_⟩
            intro larger
            have bound := originalBound rightId original
            omega
          · refine ⟨?_, ?_⟩
            · intro old
              omega
            · intro _
              refine ⟨earlier, List.mem_append_left _ contained, same, ?_⟩
              change earlier.id < state.lastId + 1
              rw [same]
              omega


theorem allowedOriginal_initial_bound (rename : Nat → Fin v) (id : Nat)
    (allowed : AllowedOriginal (parameters := parameters) rename id) :
    id ≤ (initialState (relabel rename (formula parameters))).lastId := by
  have bound := allowedOriginal_bound rename id allowed
  simp only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map,
    SourceRows.formula_as_rows, ofClauses, List.size_toArray, List.length_append,
    List.length_map, assertions, List.length_cons, List.length_nil]
  change id ≤ (equationRows (parameters := parameters)).length + 4
  omega

theorem healthyInterface_trace_supported (rename : Nat → Fin v) :
    SourceBusSchedule.TraceOriginalSupport (initialState (relabel rename (formula parameters))).lastId
      (AllowedOriginal (parameters := parameters) rename)
      (healthyFlagFromTargetAbsent (parameters := parameters) rename).steps := by
  intro step member parent parentMember
  have both := healthyInterface_original_parents rename step member
  have original : AllowedOriginal (parameters := parameters) rename parent := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at parentMember
    rcases parentMember with same | same
    · exact same.symm ▸ both.1
    · exact same.symm ▸ both.2
  refine ⟨fun _ => original, ?_⟩
  intro derived
  have bound := allowedOriginal_initial_bound rename parent original
  omega

theorem healthyInterface_result_origin (rename : Nat → Fin v) :
    ResultOrigin (initialState (relabel rename (formula parameters))).lastId
      (AllowedOriginal (parameters := parameters) rename)
      (healthyFlagFromTargetAbsent (parameters := parameters) rename).steps
      (healthyFlagFromTargetAbsent (parameters := parameters) rename).result.row.id := by
  simp only [healthyFlagFromTargetAbsent, longMerge, longMerge_result]
  apply originalMerge_result_origin
  · exact healthyProduct_original_allowed rename
  · exact healthyFlag_original_allowed rename

theorem healthyPhysical_trace_supported (rename : Nat → Fin v) (drive : parameters.drive = true) :
    SourceBusSchedule.TraceOriginalSupport (initialState (relabel rename (formula parameters))).lastId
      (AllowedOriginal (parameters := parameters) rename)
      (healthyFlagFromPhysicalUnit (parameters := parameters) rename drive).steps := by
  simp only [healthyFlagFromPhysicalUnit, longMerge]
  apply appendMerge_supported
  · exact healthyInterface_trace_supported rename
  · exact allowedOriginal_initial_bound rename
  · exact physicalUnit_allowed rename ⟨0, by decide⟩
  · exact healthyInterface_result_origin rename
  · exact (healthyFlagFromTargetAbsent (parameters := parameters) rename).result.row.bound

end Controller.NativeProof.SourceMismatchHandles
