module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceSlotFrames

@[expose] public section

/-! Actual role-handle frames connect local source occurrences with the final
compiled source role map. The proofs inspect assignments and traversals rather
than replacing syntactic identity with valuation equivalence. -/
namespace Controller.NativeProof.SourceRoleFrames
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceSlotFrames

variable {parameters : Parameters}

theorem foldl_slot_mem {α : Type} (step : Cursor parameters → α → Cursor parameters)
    (query : Controller.Native.Variable parameters) (values : List α)
    (preserves : ∀ cursor value, value ∈ values → (step cursor value).slots query = cursor.slots query)
    (cursor : Cursor parameters) :
    (values.foldl step cursor).slots query = cursor.slots query := by
  induction values generalizing cursor with
  | nil => rfl
  | cons value rest ih =>
      exact (ih (fun current index member => preserves current index (List.mem_cons_of_mem _ member))
        (step cursor value)).trans (preserves cursor value (by simp))

theorem masks_first_flag (side querySide : Side) (values : List (Fin parameters.channels))
    (cursor : Cursor parameters) :
    (values.foldl (initialMaskStep side) cursor).slots (.internal (.flag querySide parameters.firstBus)) =
      cursor.slots (.internal (.flag querySide parameters.firstBus)) := by
  apply foldl_slot
  intro current index
  apply emitNative_other
  simp

theorem laterBus_first_flag (side querySide : Side) (bus : Fin parameters.buses)
    (different : bus ≠ parameters.firstBus) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.flag querySide parameters.firstBus)) =
      cursor.slots (.internal (.flag querySide parameters.firstBus)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.flag querySide parameters.firstBus))
    (fun current index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign])]
  rw [foldNative_other _ _ _ _ _ (by simp [different, Ne.symm different])]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp

theorem eligible_first_flag (side querySide : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (eligible parameters side channel cursor).slots (.internal (.flag querySide parameters.firstBus)) =
      cursor.slots (.internal (.flag querySide parameters.firstBus)) := by
  unfold eligible
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current bus
  apply emitNative_other
  simp

theorem tail_first_flag (side querySide : Side) (cursor : Cursor parameters) :
    (SourceController.tail parameters side cursor).slots (.internal (.flag querySide parameters.firstBus)) =
      cursor.slots (.internal (.flag querySide parameters.firstBus)) := by
  unfold SourceController.tail
  rw [foldl_slot _ (.internal (.flag querySide parameters.firstBus))
    (fun current channel => eligible_first_flag side querySide channel current)]
  rw [negateFlags_slot]
  rw [foldl_slot_mem _ (.internal (.flag querySide parameters.firstBus)) _ (by
    intro current bus member
    apply laterBus_first_flag
    have nonzero : bus.val ≠ 0 := by simpa using (List.mem_filter.mp member).2
    intro equal
    apply nonzero
    simpa [Parameters.firstBus] using congrArg Fin.val equal)]
  exact masks_first_flag side querySide _ cursor

theorem pair_foldl_slot {α : Type}
    (step : Literal Nat × Cursor parameters → α → Literal Nat × Cursor parameters)
    (query : Controller.Native.Variable parameters)
    (preserves : ∀ current value, (step current value).2.slots query = current.2.slots query)
    (values : List α) (current : Literal Nat × Cursor parameters) :
    (values.foldl step current).2.slots query = current.2.slots query := by
  induction values generalizing current with
  | nil => rfl
  | cons value rest ih => exact (ih (step current value)).trans (preserves current value)

/-- Guard producers emit entries without assigning any native role slot. -/
theorem guardChain_slot (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Literal Nat) (labels : List (Fin parameters.channels))
    (query : Controller.Native.Variable parameters) (cursor : Cursor parameters) :
    (guardChain parameters side node child labels cursor).2.slots query = cursor.slots query := by
  unfold guardChain
  apply pair_foldl_slot
  intro current value
  rfl

theorem decoderNode_first_flag (side querySide : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) :
    (decoderNode parameters side node cursor).slots (.internal (.flag querySide parameters.firstBus)) =
      cursor.slots (.internal (.flag querySide parameters.firstBus)) := by
  unfold decoderNode
  cases parameters.decoder.node node with
  | zero => apply emitNative_other; simp
  | input channel => apply assign_other; simp
  | disj children => apply foldNative_other; simp
  | guard child labels =>
      rw [assign_other _ _ _ _ (by simp)]
      exact guardChain_slot side node _ labels _ cursor
  | liveAnd left right => apply emitNative_other; simp

theorem attachDecoder_first_flag (side querySide : Side) (cursor : Cursor parameters) :
    (attachDecoder parameters side cursor).slots (.internal (.flag querySide parameters.firstBus)) =
      cursor.slots (.internal (.flag querySide parameters.firstBus)) :=
  foldl_slot _ _ (fun current node => decoderNode_first_flag side querySide node current) _ cursor

theorem originalObservations_slot (query : Controller.Native.Variable parameters) (cursor : Cursor parameters) :
    (originalObservations parameters cursor).slots query = cursor.slots query := by
  unfold originalObservations
  apply foldl_slot
  intro current index
  rfl

theorem newObservations_first_flag (side : Side) (cursor : Cursor parameters) :
    (newObservations parameters cursor).slots (.internal (.flag side parameters.firstBus)) =
      cursor.slots (.internal (.flag side parameters.firstBus)) := by
  unfold newObservations
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current output
  apply emitNative_other
  simp

/-- All subsequent stored source stages retain the interface's first flags. -/
theorem compiled_first_flag (side : Side) :
    (compile parameters).slots (.internal (.flag side parameters.firstBus)) =
      (interface parameters).slots (.internal (.flag side parameters.firstBus)) := by
  unfold compile
  rw [newObservations_first_flag, attachDecoder_first_flag, attachDecoder_first_flag,
    originalObservations_slot]
  unfold controller
  rw [tail_first_flag, tail_first_flag]

theorem mask_input_first_flag (side : Side) (channel : Fin parameters.channels) :
    (initialMaskBefore side channel).slots (.internal (.flag side parameters.firstBus)) =
      (interface parameters).slots (.internal (.flag side parameters.firstBus)) := by
  unfold initialMaskBefore occurrenceCursor
  rw [masks_first_flag]
  cases side with
  | healthy => rfl
  | faulty => exact tail_first_flag .healthy .faulty (interface parameters)

/-- The two flag guards of the concrete mask proof are exactly the complete
source role handles, not merely equivalent Boolean values. -/
theorem maskFlag_eq_sourceRoleMap (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    maskFlag rename side channel =
      SourceFoldProjection.mapLiteral rename
        (sourceRoleMap parameters (.internal (.flag side parameters.firstBus))) := by
  unfold maskFlag sourceRoleMap
  rw [mask_input_first_flag, compiled_first_flag]

theorem laterBus_first_mask (side querySide : Side) (bus : Fin parameters.buses)
    (channel : Fin parameters.channels) (different : bus ≠ parameters.firstBus) (cursor : Cursor parameters) :
    (laterBus parameters side bus cursor).slots (.internal (.mask querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.mask querySide parameters.firstBus channel)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.mask querySide parameters.firstBus channel))
    (fun current index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign, different, Ne.symm different])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp

theorem eligible_first_mask (side querySide : Side) (index channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (eligible parameters side index cursor).slots (.internal (.mask querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.mask querySide parameters.firstBus channel)) := by
  unfold eligible
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current bus
  apply emitNative_other
  simp

theorem tail_after_masks_first_mask (side querySide : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (SourceController.tail parameters side cursor).slots (.internal (.mask querySide parameters.firstBus channel)) =
      (initialMasks parameters side cursor).slots (.internal (.mask querySide parameters.firstBus channel)) := by
  unfold SourceController.tail
  rw [foldl_slot _ (.internal (.mask querySide parameters.firstBus channel))
    (fun current index => eligible_first_mask side querySide index channel current)]
  rw [negateFlags_slot]
  rw [foldl_slot_mem _ (.internal (.mask querySide parameters.firstBus channel)) _ (by
    intro current bus member
    apply laterBus_first_mask
    have nonzero : bus.val ≠ 0 := by simpa using (List.mem_filter.mp member).2
    intro equal
    apply nonzero
    simpa [Parameters.firstBus] using congrArg Fin.val equal)]

theorem faulty_masks_healthy_mask (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (initialMasks parameters .faulty cursor).slots (.internal (.mask .healthy parameters.firstBus channel)) =
      cursor.slots (.internal (.mask .healthy parameters.firstBus channel)) := by
  apply foldl_slot
  intro current index
  apply emitNative_other
  simp

theorem decoderNode_first_mask (side querySide : Side) (node : Fin parameters.decoder.nodeCount)
    (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (decoderNode parameters side node cursor).slots (.internal (.mask querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.mask querySide parameters.firstBus channel)) := by
  unfold decoderNode
  cases parameters.decoder.node node with
  | zero => apply emitNative_other; simp
  | input index => apply assign_other; simp
  | disj children => apply foldNative_other; simp
  | guard child labels =>
      rw [assign_other _ _ _ _ (by simp)]
      exact guardChain_slot side node _ labels _ cursor
  | liveAnd left right => apply emitNative_other; simp

theorem attachDecoder_first_mask (side querySide : Side) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (attachDecoder parameters side cursor).slots (.internal (.mask querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.mask querySide parameters.firstBus channel)) :=
  foldl_slot _ _ (fun current node => decoderNode_first_mask side querySide node channel current) _ cursor

theorem newObservations_first_mask (side : Side) (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (newObservations parameters cursor).slots (.internal (.mask side parameters.firstBus channel)) =
      cursor.slots (.internal (.mask side parameters.firstBus channel)) := by
  unfold newObservations
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current output
  apply emitNative_other
  simp

/-- Mask handles are never reassigned by observations or decoder stages. -/
theorem compiled_first_mask_controller (side : Side) (channel : Fin parameters.channels) :
    (compile parameters).slots (.internal (.mask side parameters.firstBus channel)) =
      (controller parameters).slots (.internal (.mask side parameters.firstBus channel)) := by
  unfold compile
  rw [newObservations_first_mask, attachDecoder_first_mask, attachDecoder_first_mask,
    originalObservations_slot]

/-- The corresponding mask constructor appears once in the initial traversal. -/
theorem initialMasks_output (side : Side) (channel : Fin parameters.channels) :
    (initialMasks parameters side (tailStart side)).slots (.internal (.mask side parameters.firstBus channel)) =
      ((initialMaskBefore side channel).lastID + 1, true) := by
  let values := List.finRange parameters.channels
  have bound : channel.val < values.length := by simpa [values] using channel.isLt
  have split := positional_decomposition values ⟨channel.val, bound⟩
  have decomposition : values = values.take channel.val ++ channel :: values.drop (channel.val + 1) := by
    simpa [values] using split
  have unique : (values.take channel.val ++ channel :: values.drop (channel.val + 1)).Nodup := by
    rw [← decomposition]
    exact List.nodup_finRange parameters.channels
  have absent : channel ∉ values.drop (channel.val + 1) :=
    (List.nodup_cons.mp (List.nodup_append.mp unique).2.1).1
  change (values.foldl (initialMaskStep side) (tailStart side)).slots _ = _
  rw [decomposition, List.foldl_append, List.foldl_cons]
  rw [foldl_slot_mem _ (.internal (.mask side parameters.firstBus channel)) _ (by
    intro current index member
    apply emitNative_other
    have different : index ≠ channel := by
      intro equal
      exact absent (equal ▸ member)
    simp [different, Ne.symm different])]
  simp [initialMaskStep, initialMaskBefore, occurrenceCursor, Cursor.emitNative, Cursor.emit, Cursor.assign, values]

/-- The output of each actual initial-mask emission is the final source role
handle, including the continuation through the other copy and decoder. -/
theorem maskOutput_eq_sourceRoleMap (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    maskOutput rename side channel = SourceFoldProjection.mapLiteral rename
      (sourceRoleMap parameters (.internal (.mask side parameters.firstBus channel))) := by
  unfold maskOutput sourceRoleMap
  rw [compiled_first_mask_controller]
  cases side with
  | healthy =>
      change SourceFoldProjection.mapLiteral rename _ = SourceFoldProjection.mapLiteral rename
        ((SourceController.tail parameters .faulty
          (SourceController.tail parameters .healthy (interface parameters))).slots _)
      rw [tail_after_masks_first_mask, faulty_masks_healthy_mask, tail_after_masks_first_mask]
      change SourceFoldProjection.mapLiteral rename _ = SourceFoldProjection.mapLiteral rename
        ((initialMasks parameters .healthy (tailStart .healthy)).slots
          (.internal (.mask .healthy parameters.firstBus channel)))
      rw [initialMasks_output .healthy channel]
  | faulty =>
      change SourceFoldProjection.mapLiteral rename _ = SourceFoldProjection.mapLiteral rename
        ((SourceController.tail parameters .faulty (tailStart .faulty)).slots _)
      rw [tail_after_masks_first_mask, initialMasks_output .faulty channel]

end Controller.NativeProof.SourceRoleFrames

