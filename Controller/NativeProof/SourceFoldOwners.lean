module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceFoldProjection

@[expose] public section

/-! Source fold owners are computed from the original cursor entry offset.
Compiler prefix proofs retain the actual entry ordering without a supplied
owner lookup function. -/
namespace Controller.NativeProof.SourceFoldOwners
open Controller.Native Controller.Native.SourceController Controller.CNF

variable {parameters : Parameters}

def EntriesBefore (before after : Cursor parameters) : Prop :=
  ∃ suffix, after.entries = before.entries ++ suffix

theorem EntriesBefore.refl (cursor : Cursor parameters) : EntriesBefore cursor cursor :=
  ⟨[], by simp⟩

theorem EntriesBefore.trans {first middle last : Cursor parameters}
    (left : EntriesBefore first middle) (right : EntriesBefore middle last) : EntriesBefore first last := by
  rcases left with ⟨xs, firstEq⟩
  rcases right with ⟨ys, secondEq⟩
  exact ⟨xs ++ ys, by rw [secondEq, firstEq, List.append_assoc]⟩

theorem assign_before (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters) (handle : Literal Nat) :
    EntriesBefore cursor (cursor.assign slot handle) := ⟨[], by simp [Cursor.assign]⟩

theorem emit_before (cursor : Cursor parameters) (owner : Owner parameters) (gate : Gate Nat) :
    EntriesBefore cursor (cursor.emit owner gate).2 := by
  exact ⟨[⟨owner, ⟨(cursor.lastID + 1, true), gate⟩⟩], rfl⟩

theorem emitNative_before (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters) (gate : Gate Nat) :
    EntriesBefore cursor (cursor.emitNative slot gate) :=
  (emit_before cursor (.native slot) gate).trans (assign_before _ slot _)

theorem foldNative_before (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (Literal Nat)) :
    EntriesBefore cursor (cursor.foldNative slot junction inputs) := by
  exact ⟨(SourceSerialFold.allocate junction cursor.lastID inputs).producers.zipIdx.map
    (fun pair => Entry.mk (.fold slot pair.2) pair.1), rfl⟩

theorem foldl_before {α : Type} (step : Cursor parameters → α → Cursor parameters)
    (preservesEntries : ∀ cursor value, EntriesBefore cursor (step cursor value))
    (values : List α) (cursor : Cursor parameters) : EntriesBefore cursor (values.foldl step cursor) := by
  induction values generalizing cursor with
  | nil => exact .refl cursor
  | cons value rest ih => exact (preservesEntries cursor value).trans (ih (step cursor value))

theorem initialMasks_before (side : Side) (cursor : Cursor parameters) :
    EntriesBefore cursor (initialMasks parameters side cursor) := by
  unfold initialMasks
  apply foldl_before
  intro current channel
  exact emitNative_before current _ _

theorem laterBus_before (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters) :
    EntriesBefore cursor (laterBus parameters side bus cursor) := by
  unfold laterBus
  apply EntriesBefore.trans (foldl_before _ (fun current channel => foldNative_before current _ _ _) _ cursor)
  apply EntriesBefore.trans (foldNative_before _ _ _ _)
  apply foldl_before
  intro current channel
  exact (emitNative_before current _ _).trans (emitNative_before _ _ _)

theorem negateFlags_before (side : Side) (cursor : Cursor parameters) :
    EntriesBefore cursor (negateFlags parameters side cursor) := by
  unfold negateFlags
  apply foldl_before
  intro current bus
  exact emit_before current _ _

theorem eligible_before (side : Side) (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    EntriesBefore cursor (eligible parameters side channel cursor) := by
  unfold eligible
  exact (foldl_before _ (fun current bus => emitNative_before current _ _) _ cursor).trans
    (foldNative_before _ _ _ _)

theorem tail_before (side : Side) (cursor : Cursor parameters) :
    EntriesBefore cursor (tail parameters side cursor) := by
  unfold tail
  exact (initialMasks_before side cursor).trans
    ((foldl_before _ (fun current bus => laterBus_before side bus current) _ _).trans
      ((negateFlags_before side _).trans
        (foldl_before _ (fun current channel => eligible_before side channel current) _ _)))

theorem interface_before_controller : EntriesBefore (interface parameters) (controller parameters) :=
  (tail_before .healthy _).trans (tail_before .faulty _)

theorem pairFoldl_before {α : Type}
    (step : Literal Nat × Cursor parameters → α → Literal Nat × Cursor parameters)
    (preservesEntries : ∀ current value, EntriesBefore current.2 (step current value).2)
    (values : List α) (current : Literal Nat × Cursor parameters) :
    EntriesBefore current.2 (values.foldl step current).2 := by
  induction values generalizing current with
  | nil => exact .refl current.2
  | cons value rest ih => exact (preservesEntries current value).trans (ih (step current value))

theorem guardChain_before (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Literal Nat) (labels : List (Fin parameters.channels)) (cursor : Cursor parameters) :
    EntriesBefore cursor (guardChain parameters side node child labels cursor).2 := by
  unfold guardChain
  apply pairFoldl_before
  intro current pair
  exact emit_before current.2 _ _

theorem decoderNode_before (side : Side) (node : Fin parameters.decoder.nodeCount)
    (cursor : Cursor parameters) : EntriesBefore cursor (decoderNode parameters side node cursor) := by
  unfold decoderNode
  cases parameters.decoder.node node with
  | zero => exact emitNative_before cursor _ _
  | input channel => exact assign_before cursor _ _
  | disj children => exact foldNative_before cursor _ _ _
  | guard child labels =>
    let guarded := guardChain parameters side node
      (cursor.slots (.internal (.decoder side (parameters.decoder.childIndex node child)))) labels cursor
    exact (guardChain_before side node _ labels cursor).trans
      (assign_before guarded.2 (.internal (.decoder side node)) guarded.1)
  | liveAnd left right => exact emitNative_before cursor _ _

theorem attachDecoder_before (side : Side) (cursor : Cursor parameters) :
    EntriesBefore cursor (attachDecoder parameters side cursor) := by
  unfold attachDecoder
  exact foldl_before _ (fun current node => decoderNode_before side node current) _ cursor

theorem newObservations_before (cursor : Cursor parameters) :
    EntriesBefore cursor (newObservations parameters cursor) := by
  unfold newObservations
  exact (foldl_before _ (fun current output => emitNative_before current _ _) _ cursor).trans
    (foldNative_before _ _ _ _)

theorem originalObservations_before (cursor : Cursor parameters) :
    EntriesBefore cursor (originalObservations parameters cursor) := by
  unfold originalObservations
  let paired := (List.finRange (parameters.buses + parameters.channels)).foldl (fun current index =>
    let good := (SourceObservation.oldOutputRoles parameters .healthy)[index.val]?.getD .driver
    let bad := (SourceObservation.oldOutputRoles parameters .faulty)[index.val]?.getD .driver
    let emitted := current.emit (.oldDifference index)
      (.xor (current.slots (.internal good)) (current.slots (.internal bad)))
    { emitted.2 with oldDifferences := Function.update emitted.2.oldDifferences index emitted.1 }) cursor
  have beforePaired : EntriesBefore cursor paired := by
    apply foldl_before
    intro current index
    exact emit_before current _ _
  apply beforePaired.trans
  exact ⟨_, rfl⟩

theorem controller_before_compile : EntriesBefore (controller parameters) (compile parameters) :=
  (originalObservations_before _).trans
    ((attachDecoder_before .healthy _).trans
      ((attachDecoder_before .faulty _).trans (newObservations_before _)))

theorem interface_before_compile : EntriesBefore (interface parameters) (compile parameters) :=
  interface_before_controller.trans controller_before_compile

/-- The owner is the original cursor entry offset plus the local producer
index. A proved continuation prefix only verifies this fixed arithmetic index. -/
def foldOwner (cursor final : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (Literal Nat))
    (retained : EntriesBefore (cursor.foldNative slot junction inputs) final)
    (index : Fin (SourceSerialFold.allocate junction cursor.lastID inputs).producers.length) :
    Fin final.entries.length :=
  ⟨cursor.entries.length + index.val, by
    rcases retained with ⟨suffix, equality⟩
    rw [equality]
    simp only [Cursor.foldNative, Cursor.assign, List.length_append, List.length_map, List.length_zipIdx]
    have bound := index.isLt
    omega⟩

theorem foldOwner_producer (cursor final : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (Literal Nat))
    (retained : EntriesBefore (cursor.foldNative slot junction inputs) final)
    (index : Fin (SourceSerialFold.allocate junction cursor.lastID inputs).producers.length) :
    final.entries[(foldOwner cursor final slot junction inputs retained index).val].producer =
      (SourceSerialFold.allocate junction cursor.lastID inputs).producers[index.val] := by
  rcases retained with ⟨suffix, equality⟩
  have blockBound : index.val <
      ((SourceSerialFold.allocate junction cursor.lastID inputs).producers.zipIdx.map
        (fun pair => Entry.mk (.fold slot pair.2) pair.1)).length := by
    simpa only [List.length_map, List.length_zipIdx] using index.isLt
  simp [foldOwner, equality, Cursor.foldNative, Cursor.assign,
    List.getElem_append, List.getElem_map, blockBound, index.isLt, List.getElem_zipIdx]

/-- Full-input original rows are obtained from the arithmetic source owner. -/
def foldRows (rename : Nat → Fin v) (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (Literal Nat))
    (retained : EntriesBefore (cursor.foldNative slot junction inputs) (compile parameters)) :
    SourceFoldProjection.RowSupply (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (SourceSerialFold.allocate junction cursor.lastID inputs).producers :=
  SourceFoldProjection.sourceSupply parameters rename _
    (foldOwner cursor (compile parameters) slot junction inputs retained)
    (foldOwner_producer cursor (compile parameters) slot junction inputs retained)

def driverInputs (parameters : Parameters) : List (Literal Nat) :=
  parameters.bridge.drivers.sort.map fun channel =>
    (firstArrays parameters).slots (.internal (.absent .healthy parameters.firstBus channel))

def driverCursor (parameters : Parameters) : Cursor parameters :=
  (firstArrays parameters).foldNative (.internal .driver) .conjunction (driverInputs parameters)

def remainingInputs (parameters : Parameters) : List (Literal Nat) :=
  parameters.bridge.remaining.sort.map fun channel =>
    (driverCursor parameters).slots (.internal (.absent .healthy parameters.firstBus channel))

def remainingCursor (parameters : Parameters) : Cursor parameters :=
  (driverCursor parameters).foldNative (.internal .remaining) .conjunction (remainingInputs parameters)

/-- The interface suffix operates on an opaque already constructed cursor. -/
def finishInterface (parameters : Parameters) (cursor : Cursor parameters) : Cursor parameters :=
  let wire := cursor.emitNative (.primary .wire) (.and [cursor.slots (.internal .driver)])
  let healthyProduct := wire.emitNative (.internal (.firstProduct .healthy))
    (.and [wire.slots (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)),
      wire.slots (.internal .driver), wire.slots (.internal .remaining)])
  let healthyFlag := healthyProduct.emitNative (.internal (.flag .healthy parameters.firstBus))
    (.not (healthyProduct.slots (.internal (.firstProduct .healthy))))
  let faultyProduct := healthyFlag.emitNative (.internal (.firstProduct .faulty))
    (.and [healthyFlag.slots (.primary .wire), healthyFlag.slots (.internal .driver),
      healthyFlag.slots (.internal .remaining)])
  faultyProduct.emitNative (.internal (.flag .faulty parameters.firstBus))
    (.not (faultyProduct.slots (.internal (.firstProduct .faulty))))

theorem finishInterface_before (cursor : Cursor parameters) :
    EntriesBefore cursor (finishInterface parameters cursor) := by
  unfold finishInterface
  exact (emitNative_before _ _ _).trans
    ((emitNative_before _ _ _).trans
      ((emitNative_before _ _ _).trans
        ((emitNative_before _ _ _).trans (emitNative_before _ _ _))))

theorem interface_eq_finish : interface parameters = finishInterface parameters (remainingCursor parameters) := rfl

theorem remaining_before_interface : EntriesBefore (remainingCursor parameters) (interface parameters) := by
  rw [interface_eq_finish]
  exact finishInterface_before _

theorem driver_before_interface : EntriesBefore (driverCursor parameters) (interface parameters) :=
  (foldNative_before (driverCursor parameters) (.internal .remaining) .conjunction (remainingInputs parameters)).trans
    remaining_before_interface

theorem driver_before_compile : EntriesBefore (driverCursor parameters) (compile parameters) :=
  driver_before_interface.trans interface_before_compile

theorem remaining_before_compile : EntriesBefore (remainingCursor parameters) (compile parameters) :=
  remaining_before_interface.trans interface_before_compile

/-- The driver fold's complete original rows require no caller-provided owner
map or continuation-prefix hypothesis. -/
def driverRows (parameters : Parameters) (rename : Nat → Fin v) :
    SourceFoldProjection.RowSupply (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (SourceSerialFold.allocate .conjunction (firstArrays parameters).lastID (driverInputs parameters)).producers :=
  foldRows rename (firstArrays parameters) (.internal .driver) .conjunction (driverInputs parameters)
    driver_before_compile

def remainingRows (parameters : Parameters) (rename : Nat → Fin v) :
    SourceFoldProjection.RowSupply (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (SourceSerialFold.allocate .conjunction (driverCursor parameters).lastID (remainingInputs parameters)).producers :=
  foldRows rename (driverCursor parameters) (.internal .remaining) .conjunction (remainingInputs parameters)
    remaining_before_compile

end Controller.NativeProof.SourceFoldOwners
