module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMixedSchedule

@[expose] public section

/-! Syntactic source frames for the physical wire used by the drive-zero
native branch. Every frame follows the actual stored source traversal. -/
namespace Controller.NativeProof.SourceDriveZero
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.NativeProof.SourceRoleFrames Controller.NativeProof.SourceSlotFrames

variable {parameters : Parameters}

theorem laterBus_wire (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.primary .wire) =
      cursor.slots (.primary .wire) := by
  unfold laterBus
  rw [foldl_slot _ (.primary .wire)
    (fun current index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign])]
  rw [foldNative_other _ _ _ _ _ (by simp )]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp


theorem eligible_wire (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (eligible parameters side channel cursor).slots (.primary .wire) =
      cursor.slots (.primary .wire) := by
  unfold eligible
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current bus
  apply emitNative_other
  simp


theorem decoderNode_wire (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) :
    (decoderNode parameters side node cursor).slots (.primary .wire) =
      cursor.slots (.primary .wire) := by
  unfold decoderNode
  cases parameters.decoder.node node with
  | zero => apply emitNative_other; simp
  | input channel => apply assign_other; simp
  | disj children => apply foldNative_other; simp
  | guard child labels =>
      rw [assign_other _ _ _ _ (by simp)]
      exact guardChain_slot side node _ labels _ cursor
  | liveAnd left right => apply emitNative_other; simp


theorem attachDecoder_wire (side : Side) (cursor : Cursor parameters) :
    (attachDecoder parameters side cursor).slots (.primary .wire) = cursor.slots (.primary .wire) :=
  foldl_slot _ _ (fun current node => decoderNode_wire side node current) _ cursor

theorem initialMasks_wire (side : Side) (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).slots (.primary .wire) = cursor.slots (.primary .wire) := by
  unfold initialMasks
  apply foldl_slot
  intro current channel
  apply emitNative_other
  simp

theorem tail_wire (side : Side) (cursor : Cursor parameters) :
    (SourceController.tail parameters side cursor).slots (.primary .wire) = cursor.slots (.primary .wire) := by
  unfold SourceController.tail
  rw [foldl_slot _ (.primary .wire) (fun current channel => eligible_wire side channel current)]
  rw [negateFlags_slot]
  rw [foldl_slot _ (.primary .wire) (fun current bus => laterBus_wire side bus current)]
  exact initialMasks_wire side cursor

theorem newObservations_wire (cursor : Cursor parameters) :
    (newObservations parameters cursor).slots (.primary .wire) = cursor.slots (.primary .wire) := by
  unfold newObservations
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current output
  apply emitNative_other
  simp

theorem compiled_wire_slot :
    (compile parameters).slots (.primary .wire) = (interface parameters).slots (.primary .wire) := by
  unfold compile
  rw [newObservations_wire, attachDecoder_wire, attachDecoder_wire, originalObservations_slot]
  unfold controller
  rw [tail_wire, tail_wire]

open Controller.Resolution Controller.NativeProof.SourceMismatchBranch
open Controller.NativeProof.SourceFoldProjection Controller.NativeProof.FoldProjection

/-- The final wire handle is the actual input of the faulty interface product. -/
theorem compiled_wire_input :
    sourceRoleMap parameters (.primary .wire) =
      (healthyFlagCursor (parameters := parameters)).slots (.primary .wire) := by
  unfold sourceRoleMap
  rw [compiled_wire_slot]
  change ((faultyProductCursor (parameters := parameters)).emitNative
    (.internal (.flag .faulty parameters.firstBus))
    (.not ((faultyProductCursor (parameters := parameters)).slots
      (.internal (.firstProduct .faulty))))).slots (.primary .wire) = _
  rw [emitNative_other _ _ _ _ (by simp)]
  unfold faultyProductCursor
  exact emitNative_other _ _ _ _ (by simp)

theorem wire_input_positive :
    ((healthyFlagCursor (parameters := parameters)).slots (.primary .wire)).2 = true := by
  simp [healthyFlagCursor, healthyProductCursor, wireCursor,
    Cursor.emitNative, Cursor.emit, Cursor.assign]

theorem physical_wire_zero (drive : parameters.drive = false) :
    physicalUnit (parameters := parameters) ⟨2, by decide⟩ =
      negate ((healthyFlagCursor (parameters := parameters)).slots (.primary .wire)) := by
  have phase := wire_input_positive (parameters := parameters)
  simp only [physicalUnit, assertions, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [drive, compiled_wire_input]
  simp [negate, Std.Sat.Literal.negate, phase]

/-- Two source resolutions combine the faulty product equations with the
physical wire-zero assertion. No observation producer is required. -/
def faultyFlagFromDriveZero {v : Nat} (rename : Nat → Fin v)
    (drive : parameters.drive = false) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)] 2 := by
  let first := faultyZeroInput (parameters := parameters) rename ⟨0, by decide⟩
  let input := mapLiteral rename ((healthyFlagCursor (parameters := parameters)).slots (.primary .wire))
  let flag := mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let physical : AvailableSubclause first.state [negate input] := by
    have row := afterTrace (ofRow (physicalUnitRow (parameters := parameters) rename ⟨2, by decide⟩))
      first.state first.steps first.checked
    simpa only [physical_wire_zero drive, mapLiteral, negate, Std.Sat.Literal.negate, input] using row
  let reason : AvailableSubclause first.state [input, flag] :=
    retarget first.result (by
      intro literal member
      simp only [faultyProductInputs, List.getElem_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false, input, flag] at member ⊢
      aesop)
  let joined := longMerge first.state input [] [flag] physical reason
  refine ⟨joined.state, first.steps ++ joined.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact longMerge_run _ _ _ _ _ _
  · simpa only [List.nil_append, flag] using longMerge_result first.state input [] [flag] physical reason
  · have one := first.count
    have two := longMerge_count first.state input [] [flag] physical reason
    simp only [List.length_append, joined]
    omega


open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceMismatchHandles
open Controller.NativeProof.SourceMixedSchedule Controller.NativeProof.SourceStageCongruence

theorem faultyProduct_original_allowed {v : Nat} (rename : Nat → Fin v) :
    AllowedOriginal (parameters := parameters) rename
      ((faultyProductRows (parameters := parameters) rename).row
        ⟨0, by change 0 < 4; decide⟩).id := by
  have retained : EntriesBefore (faultyProductCursor (parameters := parameters)) (controller parameters) :=
    (emitNative_before _ _ _).trans interface_before_controller
  simpa only [faultyProductRows, emitRowsExact, ownedRow, emitOwner, SourceRows.before] using
    emitRow_allowed rename (healthyFlagCursor (parameters := parameters))
      (.internal (.firstProduct .faulty)) (.and (faultyProductInputs (parameters := parameters)))
      retained ⟨0, by change 0 < 4; decide⟩

theorem faultyFlag_original_allowed {v : Nat} (rename : Nat → Fin v) :
    AllowedOriginal (parameters := parameters) rename
      ((faultyFlagRows (parameters := parameters) rename).row
        ⟨0, by change 0 < 2; decide⟩).id := by
  simpa only [faultyFlagRows, emitRowsExact, ownedRow, emitOwner, SourceRows.before] using
    emitRow_allowed rename (faultyProductCursor (parameters := parameters))
      (.internal (.flag .faulty parameters.firstBus))
      (.not ((faultyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .faulty))))
      interface_before_controller ⟨0, by change 0 < 2; decide⟩


theorem faultyWireOrFlag_supported {v : Nat} (rename : Nat → Fin v) :
    ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (faultyZeroInput (parameters := parameters) rename ⟨0, by decide⟩) := by
  let base := initialState (relabel rename (formula parameters))
  let product := mapLiteral rename ((healthyFlagCursor (parameters := parameters)).lastID + 1, true)
  let flag := mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := mapLiteral rename ((faultyProductInputs (parameters := parameters))[0]'(by simp [faultyProductInputs]))
  let raw := (faultyProductRows (parameters := parameters) rename).row ⟨0, by change 0 < 4; decide⟩
  let left : AvailableSubclause base [negate product, input] := by
    have row := ofRow raw
    have bound : 0 < (faultyProductInputs (parameters := parameters)).length := by simp [faultyProductInputs]
    simpa [raw, Bounded.Producer.rows, Gate.clauses, List.getElem_append, bound,
      Rows.mapClause, mapLiteral, product, input, base, negate, Std.Sat.Literal.negate] using row
  let right : AvailableSubclause base [product, flag] :=
    retarget (ofRow ((faultyFlagRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 2; decide⟩)) (by
        intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        simp [faultyProductCursor, Cursor.emitNative, Cursor.emit, Cursor.assign,
          Bounded.Producer.rows, Gate.clauses, Rows.mapClause, mapLiteral, product, flag] at member ⊢ <;> aesop)
  have leftId : left.row.id = raw.id := by
    dsimp only [left]
    rw [subclause_indices_mpr_id rfl (by
      simp [raw, Bounded.Producer.rows, Gate.clauses, Rows.mapClause,
        mapLiteral, product, input, negate, Std.Sat.Literal.negate, faultyProductInputs])]
    rw [subclause_indices_cast_id rfl (by
      simp [raw, Bounded.Producer.rows, Gate.clauses, Rows.mapClause,
        mapLiteral, product, input, negate, Std.Sat.Literal.negate, faultyProductInputs])]
    rfl
  have leftOrigin : ResultOrigin (formula parameters).clauses.size
      (AllowedOriginal (parameters := parameters) rename) ([] : List (Step v)) left.row.id := by
    apply Or.inl
    rw [leftId]
    exact faultyProduct_original_allowed rename
  have rightOrigin : ResultOrigin (formula parameters).clauses.size
      (AllowedOriginal (parameters := parameters) rename) ([] : List (Step v)) right.row.id :=
    Or.inl (faultyFlag_original_allowed rename)
  have emptySupport : SourceBusSchedule.TraceOriginalSupport (formula parameters).clauses.size
      (AllowedOriginal (parameters := parameters) rename) ([] : List (Step v)) := by
    intro step member
    cases member
  have baseBound : (formula parameters).clauses.size ≤ base.lastId :=
    prefix_native_count_le rename (SourcePrefix.initial (parameters := parameters) rename)
  have actual := longMerge_supported (formula parameters).clauses.size
    (AllowedOriginal (parameters := parameters) rename) [] base product [input] [flag] left right
    emptySupport (allowed_native_count_le rename) baseBound leftOrigin rightOrigin
  simpa only [ProjectionOriginalSupport, SourcePrefix.initial, faultyZeroInput, base,
    product, input, flag, raw, left, right, retarget, List.nil_append] using actual


theorem faultyFlagFromDriveZero_supported {v : Nat} (rename : Nat → Fin v)
    (drive : parameters.drive = false) :
    ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (faultyFlagFromDriveZero (parameters := parameters) rename drive) := by
  let first := faultyZeroInput (parameters := parameters) rename ⟨0, by decide⟩
  let input := mapLiteral rename ((healthyFlagCursor (parameters := parameters)).slots (.primary .wire))
  let flag := mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let physical : AvailableSubclause first.state [negate input] := by
    have row := afterTrace (ofRow (physicalUnitRow (parameters := parameters) rename ⟨2, by decide⟩))
      first.state first.steps first.checked
    simpa only [physical_wire_zero drive, mapLiteral, negate, Std.Sat.Literal.negate, input] using row
  let reason : AvailableSubclause first.state [input, flag] :=
    retarget first.result (by
      intro literal member
      simp only [faultyProductInputs, List.getElem_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false, input, flag] at member ⊢
      aesop)
  have firstSupport := faultyWireOrFlag_supported (parameters := parameters) rename
  have physicalId : physical.row.id =
      (physicalUnitRow (parameters := parameters) rename ⟨2, by decide⟩).id := by
    dsimp only [physical]
    apply subclause_indices_cast_id rfl
      (by simp only [physical_wire_zero drive, mapLiteral, negate, Std.Sat.Literal.negate, input])
  have physicalOrigin : ResultOrigin (formula parameters).clauses.size
      (AllowedOriginal (parameters := parameters) rename) first.steps physical.row.id := by
    apply Or.inl
    rw [physicalId]
    exact physicalUnit_allowed rename ⟨2, by decide⟩
  have reasonOrigin : ResultOrigin (formula parameters).clauses.size
      (AllowedOriginal (parameters := parameters) rename) first.steps reason.row.id := by
    simpa only [ProjectionOriginalSupport, SourcePrefix.initial, List.nil_append, first, reason, retarget] using
      firstSupport.2
  have bound : (formula parameters).clauses.size ≤ first.state.lastId :=
    Nat.le_trans (prefix_native_count_le rename (SourcePrefix.initial (parameters := parameters) rename))
      (runSteps_lastId_le first.checked)
  have actual := longMerge_supported (formula parameters).clauses.size
    (AllowedOriginal (parameters := parameters) rename) first.steps first.state input [] [flag] physical reason
    (by simpa only [ProjectionOriginalSupport, SourcePrefix.initial, List.nil_append, first] using firstSupport.1)
    (allowed_native_count_le rename) bound physicalOrigin reasonOrigin
  simpa only [ProjectionOriginalSupport, SourcePrefix.initial, faultyFlagFromDriveZero,
    first, input, flag, physical, reason, List.nil_append] using actual


open Controller.NativeProof.SourceMismatchAdvance Controller.NativeProof.SourceMismatchSeed

/-- With physical drive zero, the differing first-flag cofactor already has
a stronger original-supported conflict. The output clause can be any decoder
or controller conclusion; the actual trace is the same two-merge kernel. -/
def mixedDriveZero {v : Nat} (rename : Nat → Fin v)
    (drive : parameters.drive = false) (outputs : Clause (Fin v)) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      (mixedContext (parameters := parameters) rename ++ outputs) 2 := by
  let first := faultyFlagFromDriveZero (parameters := parameters) rename drive
  refine ⟨first.state, first.steps, first.checked, retarget first.result ?_, first.count⟩
  intro literal member
  have flagEq := faultyFlag_handle (parameters := parameters)
  have selected : literal =
      mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true) := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  rw [selected]
  apply List.mem_append_left
  simp only [mixedContext, flagEq, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr trivial

theorem mixedDriveZero_supported {v : Nat} (rename : Nat → Fin v)
    (drive : parameters.drive = false) (outputs : Clause (Fin v)) :
    ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (mixedDriveZero (parameters := parameters) rename drive outputs) := by
  simpa only [ProjectionOriginalSupport, mixedDriveZero, retarget] using
    faultyFlagFromDriveZero_supported (parameters := parameters) rename drive


theorem laterBus_driver (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal .driver) =
      cursor.slots (.internal .driver) := by
  unfold laterBus
  rw [foldl_slot _ (.internal .driver)
    (fun current index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign])]
  rw [foldNative_other _ _ _ _ _ (by simp )]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp


theorem eligible_driver (side : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (eligible parameters side channel cursor).slots (.internal .driver) =
      cursor.slots (.internal .driver) := by
  unfold eligible
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current bus
  apply emitNative_other
  simp


theorem decoderNode_driver (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) :
    (decoderNode parameters side node cursor).slots (.internal .driver) =
      cursor.slots (.internal .driver) := by
  unfold decoderNode
  cases parameters.decoder.node node with
  | zero => apply emitNative_other; simp
  | input channel => apply assign_other; simp
  | disj children => apply foldNative_other; simp
  | guard child labels =>
      rw [assign_other _ _ _ _ (by simp)]
      exact guardChain_slot side node _ labels _ cursor
  | liveAnd left right => apply emitNative_other; simp


theorem attachDecoder_driver (side : Side) (cursor : Cursor parameters) :
    (attachDecoder parameters side cursor).slots (.internal .driver) = cursor.slots (.internal .driver) :=
  foldl_slot _ _ (fun current node => decoderNode_driver side node current) _ cursor

theorem initialMasks_driver (side : Side) (cursor : Cursor parameters) :
    (initialMasks parameters side cursor).slots (.internal .driver) = cursor.slots (.internal .driver) := by
  unfold initialMasks
  apply foldl_slot
  intro current channel
  apply emitNative_other
  simp

theorem tail_driver (side : Side) (cursor : Cursor parameters) :
    (SourceController.tail parameters side cursor).slots (.internal .driver) = cursor.slots (.internal .driver) := by
  unfold SourceController.tail
  rw [foldl_slot _ (.internal .driver) (fun current channel => eligible_driver side channel current)]
  rw [negateFlags_slot]
  rw [foldl_slot _ (.internal .driver) (fun current bus => laterBus_driver side bus current)]
  exact initialMasks_driver side cursor

theorem newObservations_driver (cursor : Cursor parameters) :
    (newObservations parameters cursor).slots (.internal .driver) = cursor.slots (.internal .driver) := by
  unfold newObservations
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current output
  apply emitNative_other
  simp

theorem compiled_driver_slot :
    (compile parameters).slots (.internal .driver) = (interface parameters).slots (.internal .driver) := by
  unfold compile
  rw [newObservations_driver, attachDecoder_driver, attachDecoder_driver, originalObservations_slot]
  unfold controller
  rw [tail_driver, tail_driver]


theorem compiled_driver_input :
    sourceRoleMap parameters (.internal .driver) =
      (wireCursor (parameters := parameters)).slots (.internal .driver) := by
  unfold sourceRoleMap
  rw [compiled_driver_slot]
  change ((faultyProductCursor (parameters := parameters)).emitNative
    (.internal (.flag .faulty parameters.firstBus))
    (.not ((faultyProductCursor (parameters := parameters)).slots
      (.internal (.firstProduct .faulty))))).slots (.internal .driver) = _
  rw [emitNative_other _ _ _ _ (by simp)]
  unfold faultyProductCursor
  rw [emitNative_other _ _ _ _ (by simp)]
  unfold healthyFlagCursor
  rw [emitNative_other _ _ _ _ (by simp)]
  unfold healthyProductCursor
  exact emitNative_other _ _ _ _ (by simp)

theorem physical_driver_zero (drive : parameters.drive = false) :
    physicalUnit (parameters := parameters) ⟨1, by decide⟩ =
      negate ((wireCursor (parameters := parameters)).slots (.internal .driver)) := by
  have phase := SourceController.sourceRoleMap_positive parameters (.internal .driver)
  rw [compiled_driver_input] at phase
  simp only [physicalUnit, assertions, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [drive, compiled_driver_input]
  simp [negate, Std.Sat.Literal.negate, phase]



def healthyFlagOrDriver {v : Nat} (rename : Nat → Fin v) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true),
       mapLiteral rename ((wireCursor (parameters := parameters)).slots (.internal .driver))] 1 := by
  let state := initialState (relabel rename (formula parameters))
  let product := mapLiteral rename ((wireCursor (parameters := parameters)).lastID + 1, true)
  let driver := mapLiteral rename ((wireCursor (parameters := parameters)).slots (.internal .driver))
  let flag := mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)
  let left : AvailableSubclause state [negate product, driver] :=
    ofRow ((healthyProductRows (parameters := parameters) rename).row ⟨1, by change 1 < 4; decide⟩)
  let right : AvailableSubclause state [product, flag] :=
    retarget (ofRow ((healthyFlagRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 2; decide⟩)) (by
        intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        simp [healthyProductCursor, Cursor.emitNative, Cursor.emit, Cursor.assign,
          Bounded.Producer.rows, Gate.clauses, Rows.mapClause, mapLiteral, product, flag] at member ⊢ <;> aesop)
  let joined := longMerge state product [driver] [flag] left right
  refine ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    retarget (longMerge_result _ _ _ _ _ _) ?_, longMerge_count _ _ _ _ _ _⟩
  intro literal member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  aesop

def healthyFlagFromDriveZero {v : Nat} (rename : Nat → Fin v) (drive : parameters.drive = false) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)] 2 := by
  let first := healthyFlagOrDriver (parameters := parameters) rename
  let input := mapLiteral rename ((wireCursor (parameters := parameters)).slots (.internal .driver))
  let flag := mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)
  let physical : AvailableSubclause first.state [negate input] := by
    have row := afterTrace (ofRow (physicalUnitRow (parameters := parameters) rename ⟨1, by decide⟩))
      first.state first.steps first.checked
    simpa only [physical_driver_zero drive, mapLiteral, negate, Std.Sat.Literal.negate, input] using row
  let reason : AvailableSubclause first.state [input, flag] :=
    retarget first.result (by
      intro literal member
      simp only [List.mem_cons, List.not_mem_nil, or_false, input, flag] at member ⊢
      aesop)
  let joined := longMerge first.state input [] [flag] physical reason
  refine ⟨joined.state, first.steps ++ joined.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, first.checked]
    exact longMerge_run _ _ _ _ _ _
  · simpa only [List.nil_append, flag] using longMerge_result first.state input [] [flag] physical reason
  · have one := first.count
    have two := longMerge_count first.state input [] [flag] physical reason
    simp only [List.length_append, joined]
    omega


theorem healthyProduct_driver_original_allowed (rename : Nat → Fin v) :
    SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename
      ((healthyProductRows (parameters := parameters) rename).row ⟨1, by change 1 < 4; decide⟩).id := by
  have retained : EntriesBefore (healthyProductCursor (parameters := parameters)) (controller parameters) :=
    (emitNative_before _ _ _).trans (healthyFlag_before_interface.trans interface_before_controller)
  simpa only [healthyProductRows, emitRowsExact, ownedRow, emitOwner, SourceRows.before] using
    emitRow_allowed rename (wireCursor (parameters := parameters))
      (.internal (.firstProduct .healthy))
      (.and [(wireCursor (parameters := parameters)).slots
        (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)),
        (wireCursor (parameters := parameters)).slots (.internal .driver),
        (wireCursor (parameters := parameters)).slots (.internal .remaining)]) retained
      ⟨1, by change 1 < 4; decide⟩

theorem healthyFlagOrDriver_supported {v : Nat} (rename : Nat → Fin v) :
    ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (healthyFlagOrDriver (parameters := parameters) rename) := by
  let state := initialState (relabel rename (formula parameters))
  let product := mapLiteral rename ((wireCursor (parameters := parameters)).lastID + 1, true)
  let driver := mapLiteral rename ((wireCursor (parameters := parameters)).slots (.internal .driver))
  let flag := mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)
  let left : AvailableSubclause state [negate product, driver] :=
    ofRow ((healthyProductRows (parameters := parameters) rename).row ⟨1, by change 1 < 4; decide⟩)
  let right : AvailableSubclause state [product, flag] :=
    retarget (ofRow ((healthyFlagRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 2; decide⟩)) (by
        intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        simp [healthyProductCursor, Cursor.emitNative, Cursor.emit, Cursor.assign,
          Bounded.Producer.rows, Gate.clauses, Rows.mapClause, mapLiteral, product, flag] at member ⊢ <;> aesop)
  have emptySupport : SourceBusSchedule.TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) ([] : List (Step v)) := by
    intro step member
    cases member
  have leftOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) ([] : List (Step v)) left.row.id :=
    Or.inl (healthyProduct_driver_original_allowed rename)
  have rightOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) ([] : List (Step v)) right.row.id :=
    Or.inl (healthyFlag_original_allowed rename)
  have actual := longMerge_supported (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) [] state product [driver] [flag] left right
    emptySupport (allowed_native_count_le rename)
    (prefix_native_count_le rename (SourcePrefix.initial (parameters := parameters) rename)) leftOrigin rightOrigin
  simpa only [ProjectionOriginalSupport, SourcePrefix.initial, healthyFlagOrDriver, state,
    product, driver, flag, left, right, retarget, List.nil_append] using actual

theorem healthyFlagFromDriveZero_supported {v : Nat} (rename : Nat → Fin v)
    (drive : parameters.drive = false) :
    ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (healthyFlagFromDriveZero (parameters := parameters) rename drive) := by
  let first := healthyFlagOrDriver (parameters := parameters) rename
  let input := mapLiteral rename ((wireCursor (parameters := parameters)).slots (.internal .driver))
  let flag := mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)
  let physical : AvailableSubclause first.state [negate input] := by
    have row := afterTrace (ofRow (physicalUnitRow (parameters := parameters) rename ⟨1, by decide⟩))
      first.state first.steps first.checked
    simpa only [physical_driver_zero drive, mapLiteral, negate, Std.Sat.Literal.negate, input] using row
  let reason : AvailableSubclause first.state [input, flag] :=
    retarget first.result (by
      intro literal member
      simp only [List.mem_cons, List.not_mem_nil, or_false, input, flag] at member ⊢
      aesop)
  have firstSupport := healthyFlagOrDriver_supported (parameters := parameters) rename
  have physicalId : physical.row.id =
      (physicalUnitRow (parameters := parameters) rename ⟨1, by decide⟩).id := by
    dsimp only [physical]
    apply subclause_indices_cast_id rfl
      (by simp only [physical_driver_zero drive, mapLiteral, negate, Std.Sat.Literal.negate, input])
  have physicalOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) first.steps physical.row.id := by
    apply Or.inl
    rw [physicalId]
    exact physicalUnit_allowed rename ⟨1, by decide⟩
  have reasonOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) first.steps reason.row.id := by
    simpa only [ProjectionOriginalSupport, SourcePrefix.initial, List.nil_append, first, reason, retarget] using firstSupport.2
  have bound : (formula parameters).clauses.size ≤ first.state.lastId :=
    Nat.le_trans (prefix_native_count_le rename (SourcePrefix.initial (parameters := parameters) rename))
      (runSteps_lastId_le first.checked)
  have actual := longMerge_supported (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) first.steps first.state input [] [flag] physical reason
    firstSupport.1 (allowed_native_count_le rename) bound physicalOrigin reasonOrigin
  simpa only [ProjectionOriginalSupport, SourcePrefix.initial, healthyFlagFromDriveZero,
    first, input, flag, physical, reason, retarget, List.nil_append] using actual


theorem healthyFlagFromPhysicalUnit_supported {v : Nat} (rename : Nat → Fin v)
    (drive : parameters.drive = true) :
    ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (healthyFlagFromPhysicalUnit (parameters := parameters) rename drive) := by
  let first := healthyFlagFromTargetAbsent (parameters := parameters) rename
  let absent := mapLiteral rename ((wireCursor (parameters := parameters)).slots
    (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)))
  let flag := mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)
  let physical := physicalUnitRow (parameters := parameters) rename ⟨0, by decide⟩
  let original : Rows.Available (initialState (relabel rename (formula parameters))) [negate absent] :=
    ⟨physical.id, (by simpa only [targetPhysicalUnit rename drive, absent] using physical.present), physical.bound⟩
  let left := FoldProjection.afterTrace (ofRow original) first.state first.steps first.checked
  have trace : SourceBusSchedule.TraceOriginalSupport (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) first.steps := by
    simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map, first] using
      healthyInterface_trace_supported (parameters := parameters) rename
  have rightOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) first.steps first.result.row.id := by
    simpa only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map, first] using
      healthyInterface_result_origin (parameters := parameters) rename
  have leftOrigin : ResultOrigin (formula parameters).clauses.size
      (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) first.steps left.row.id := by
    apply Or.inl
    exact physicalUnit_allowed rename ⟨0, by decide⟩
  have bound : (formula parameters).clauses.size ≤ first.state.lastId :=
    Nat.le_trans (prefix_native_count_le rename (SourcePrefix.initial (parameters := parameters) rename))
      (runSteps_lastId_le first.checked)
  have actual := longMerge_supported (formula parameters).clauses.size
    (SourceMismatchBranch.AllowedOriginal (parameters := parameters) rename) first.steps first.state
    absent [] [flag] left first.result trace (allowed_native_count_le rename) bound leftOrigin rightOrigin
  simpa only [ProjectionOriginalSupport, SourcePrefix.initial, List.nil_append,
    healthyFlagFromPhysicalUnit, first, absent, flag, physical, original, left] using actual

def healthyFlagFromPhysicalDrive {v : Nat} (rename : Nat → Fin v) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (sourceRoleMap parameters (.internal (.flag .healthy parameters.firstBus)))] 2 :=
  if drive : parameters.drive = false then
    let actual := healthyFlagFromDriveZero (parameters := parameters) rename drive
    ⟨actual.state, actual.steps, actual.checked,
      retarget actual.result (by
        intro literal member
        simpa only [healthyFlag_handle] using member), actual.count⟩
  else
    healthyFlagUnit (parameters := parameters) rename (by
      cases value : parameters.drive with
      | false => exact False.elim (drive value)
      | true => rfl)

theorem healthyFlagFromPhysicalDrive_supported {v : Nat} (rename : Nat → Fin v) :
    ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (healthyFlagFromPhysicalDrive (parameters := parameters) rename) := by
  by_cases drive : parameters.drive = false
  · unfold ProjectionOriginalSupport healthyFlagFromPhysicalDrive
    rw [dite_eq_left drive]
    simpa only [ProjectionOriginalSupport, retarget] using
      healthyFlagFromDriveZero_supported (parameters := parameters) rename drive
  · have one : parameters.drive = true := by
      cases value : parameters.drive with
      | false => exact False.elim (drive value)
      | true => rfl
    unfold ProjectionOriginalSupport healthyFlagFromPhysicalDrive
    rw [dite_eq_right drive]
    simpa only [ProjectionOriginalSupport, healthyFlagUnit, retarget] using
      healthyFlagFromPhysicalUnit_supported (parameters := parameters) rename one


def healthyFalseCofactor {v : Nat} (rename : Nat → Fin v) (faulty : Bool)
    (outputs : Clause (Fin v)) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      ([assignmentGuard (mapLiteral rename (sourceRoleMap parameters
          (.internal (.flag .healthy parameters.firstBus)))) false,
        assignmentGuard (mapLiteral rename (sourceRoleMap parameters
          (.internal (.flag .faulty parameters.firstBus)))) faulty] ++ outputs) 2 := by
  let actual := healthyFlagFromPhysicalDrive (parameters := parameters) rename
  refine ⟨actual.state, actual.steps, actual.checked, retarget actual.result ?_, actual.count⟩
  intro literal member
  have selected : literal = mapLiteral rename
      (sourceRoleMap parameters (.internal (.flag .healthy parameters.firstBus))) := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  rw [selected]
  apply List.mem_append_left
  simp [assignmentGuard]

theorem healthyFalseCofactor_supported {v : Nat} (rename : Nat → Fin v) (faulty : Bool)
    (outputs : Clause (Fin v)) :
    ProjectionOriginalSupport rename (SourcePrefix.initial (parameters := parameters) rename)
      (healthyFalseCofactor (parameters := parameters) rename faulty outputs) := by
  simpa only [ProjectionOriginalSupport, healthyFalseCofactor, retarget] using
    healthyFlagFromPhysicalDrive_supported (parameters := parameters) rename


end Controller.NativeProof.SourceDriveZero
