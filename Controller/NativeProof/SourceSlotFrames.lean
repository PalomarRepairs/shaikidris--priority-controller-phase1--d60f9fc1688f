module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceCongruence

@[expose] public section

/-! Slot frames retain concrete source handles across unrelated assignments.
The two first-bus absent slots share one emitted handle, and later stages retain
that identity at the actual initial-mask occurrences. -/
namespace Controller.NativeProof.SourceSlotFrames
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceCongruence

variable {parameters : Parameters}

theorem assign_other (cursor : Cursor parameters) (slot query : Controller.Native.Variable parameters)
    (handle : Literal Nat) (different : query ≠ slot) :
    (cursor.assign slot handle).slots query = cursor.slots query := by
  simp [Cursor.assign, different]

theorem emitNative_other (cursor : Cursor parameters) (slot query : Controller.Native.Variable parameters)
    (gate : Gate Nat) (different : query ≠ slot) :
    (cursor.emitNative slot gate).slots query = cursor.slots query := by
  simp [Cursor.emitNative, Cursor.emit, Cursor.assign, different]

theorem foldNative_other (cursor : Cursor parameters) (slot query : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (Literal Nat)) (different : query ≠ slot) :
    (cursor.foldNative slot junction inputs).slots query = cursor.slots query := by
  simp [Cursor.foldNative, Cursor.assign, different]

theorem foldl_slot {α : Type} (step : Cursor parameters → α → Cursor parameters)
    (query : Controller.Native.Variable parameters)
    (preserves : ∀ cursor value, (step cursor value).slots query = cursor.slots query)
    (values : List α) (cursor : Cursor parameters) :
    (values.foldl step cursor).slots query = cursor.slots query := by
  induction values generalizing cursor with
  | nil => rfl
  | cons value rest ih => exact (ih (step cursor value)).trans (preserves cursor value)

theorem foldl_slot_invariant {α : Type} (step : Cursor parameters → α → Cursor parameters)
    (property : Cursor parameters → Prop)
    (preserves : ∀ cursor value, property cursor → property (step cursor value))
    (values : List α) (cursor : Cursor parameters) (initial : property cursor) :
    property (values.foldl step cursor) := by
  induction values generalizing cursor with
  | nil => exact initial
  | cons value rest ih => exact ih (step cursor value) (preserves cursor value initial)

theorem initialMasks_absent (side querySide : Side) (channel : Fin parameters.channels)
    (values : List (Fin parameters.channels)) (cursor : Cursor parameters) :
    (values.foldl (initialMaskStep side) cursor).slots (.internal (.absent querySide parameters.firstBus channel)) =
      cursor.slots (.internal (.absent querySide parameters.firstBus channel)) := by
  apply foldl_slot
  intro current index
  apply emitNative_other
  simp

/-- Paired source assignment identifies both copies with the fresh absent
producer's one physical output. -/
theorem firstArrays_absent_equal (channel : Fin parameters.channels) :
    (firstArrays parameters).slots (.internal (.absent .healthy parameters.firstBus channel)) =
      (firstArrays parameters).slots (.internal (.absent .faulty parameters.firstBus channel)) := by
  unfold firstArrays
  apply foldl_slot_invariant _ (fun cursor =>
    cursor.slots (.internal (.absent .healthy parameters.firstBus channel)) =
      cursor.slots (.internal (.absent .faulty parameters.firstBus channel)))
  · intro cursor index same
    by_cases equal : index = channel
    · subst index
      simp [Cursor.emitNative, Cursor.emit, Cursor.assign]
    · simp [Cursor.emitNative, Cursor.emit, Cursor.assign, equal, Ne.symm equal, same]
  · have healthy := foldl_slot
      (fun cursor index =>
        let emitted := cursor.emitNative (.internal (.term .healthy parameters.firstBus index))
          (.and [cursor.slots (.primary (.enable index)), cursor.slots (.primary (.request parameters.firstBus index))])
        emitted.assign (.internal (.term .faulty parameters.firstBus index))
          (emitted.slots (.internal (.term .healthy parameters.firstBus index))))
      (.internal (.absent .healthy parameters.firstBus channel))
      (fun cursor index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign])
      (List.finRange parameters.channels) (initial parameters)
    have faulty := foldl_slot
      (fun cursor index =>
        let emitted := cursor.emitNative (.internal (.term .healthy parameters.firstBus index))
          (.and [cursor.slots (.primary (.enable index)), cursor.slots (.primary (.request parameters.firstBus index))])
        emitted.assign (.internal (.term .faulty parameters.firstBus index))
          (emitted.slots (.internal (.term .healthy parameters.firstBus index))))
      (.internal (.absent .faulty parameters.firstBus channel))
      (fun cursor index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign])
      (List.finRange parameters.channels) (initial parameters)
    rw [healthy, faulty]
    rfl

theorem interface_absent (side : Side) (channel : Fin parameters.channels) :
    (interface parameters).slots (.internal (.absent side parameters.firstBus channel)) =
      (firstArrays parameters).slots (.internal (.absent side parameters.firstBus channel)) := by
  rw [interface_eq_finish]
  simp [finishInterface, remainingCursor, driverCursor, Cursor.emitNative,
    Cursor.emit, Cursor.assign, Cursor.foldNative]

theorem laterBus_faulty_absent (bus : Fin parameters.buses) (channel : Fin parameters.channels)
    (cursor : Cursor parameters) :
    (laterBus parameters .healthy bus cursor).slots (.internal (.absent .faulty parameters.firstBus channel)) =
      cursor.slots (.internal (.absent .faulty parameters.firstBus channel)) := by
  unfold laterBus
  rw [foldl_slot _ (.internal (.absent .faulty parameters.firstBus channel))
    (fun current index => by simp [Cursor.emitNative, Cursor.emit, Cursor.assign])]
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current index
  apply foldNative_other
  simp

theorem negateFlags_slot (side : Side) (query : Controller.Native.Variable parameters) (cursor : Cursor parameters) :
    (negateFlags parameters side cursor).slots query = cursor.slots query := by
  unfold negateFlags
  apply foldl_slot
  intro current bus
  rfl

theorem eligible_faulty_absent (index channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (eligible parameters .healthy index cursor).slots (.internal (.absent .faulty parameters.firstBus channel)) =
      cursor.slots (.internal (.absent .faulty parameters.firstBus channel)) := by
  unfold eligible
  rw [foldNative_other _ _ _ _ _ (by simp)]
  apply foldl_slot
  intro current bus
  apply emitNative_other
  simp

theorem healthy_tail_faulty_absent (channel : Fin parameters.channels) (cursor : Cursor parameters) :
    (SourceController.tail parameters .healthy cursor).slots (.internal (.absent .faulty parameters.firstBus channel)) =
      cursor.slots (.internal (.absent .faulty parameters.firstBus channel)) := by
  unfold SourceController.tail
  rw [foldl_slot _ (.internal (.absent .faulty parameters.firstBus channel))
    (fun current index => eligible_faulty_absent index channel current)]
  rw [negateFlags_slot]
  rw [foldl_slot _ (.internal (.absent .faulty parameters.firstBus channel))
    (fun current bus => laterBus_faulty_absent bus channel current)]
  exact initialMasks_absent .healthy .faulty channel _ cursor

/-- The two concrete mask-emission cursors read exactly the same original
first-bus absent handle. This is syntactic identity, independent of valuation. -/
theorem initial_mask_absent_handle_equal (channel : Fin parameters.channels) :
    (initialMaskBefore .healthy channel).slots (.internal (.absent .healthy parameters.firstBus channel)) =
      (initialMaskBefore .faulty channel).slots (.internal (.absent .faulty parameters.firstBus channel)) := by
  unfold initialMaskBefore occurrenceCursor
  rw [initialMasks_absent .healthy .healthy, initialMasks_absent .faulty .faulty]
  change (interface parameters).slots (.internal (.absent .healthy parameters.firstBus channel)) =
    (SourceController.tail parameters .healthy (interface parameters)).slots
      (.internal (.absent .faulty parameters.firstBus channel))
  rw [healthy_tail_faulty_absent, interface_absent, interface_absent]
  exact firstArrays_absent_equal channel

open Controller.Resolution Controller.Resolution.Cases Controller.Resolution.RUP

theorem maskAbsent_equal (rename : Nat → Fin v) (channel : Fin parameters.channels) :
    maskAbsent rename .healthy channel = maskAbsent rename .faulty channel :=
  congrArg (SourceFoldProjection.mapLiteral rename) (initial_mask_absent_handle_equal channel)

def firstFlagContext (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) : Clause (Fin v) :=
  [assignmentGuard (maskFlag rename .healthy channel) flag,
   assignmentGuard (maskFlag rename .faulty channel) flag]

theorem mask_context_subset (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    ClauseSubset
      (maskContext rename channel flag absent ++
        [negate (maskOutput rename .healthy channel), maskOutput rename .faulty channel])
      ((firstFlagContext rename channel flag ++
        [negate (maskOutput rename .healthy channel), maskOutput rename .faulty channel]) ++
        [assignmentGuard (maskAbsent rename .healthy channel) absent]) := by
  unfold maskContext firstFlagContext
  rw [← maskAbsent_equal rename channel]
  intro literal member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  aesop

/-- Retargeting retains the original row and empty reason trail. It never
inserts the enlarged requested target as a proof row. -/
theorem maskCofactor_flag_valid (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    ValidTree (initialState (relabel rename (SourceController.formula parameters)))
      ((firstFlagContext rename channel flag ++
        [negate (maskOutput rename .healthy channel), maskOutput rename .faulty channel]) ++
        [assignmentGuard (maskAbsent rename .healthy channel) absent])
      (maskCofactorTree rename channel flag absent) := by
  have valid := maskCofactorTree_valid rename channel flag absent
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at valid ⊢
  refine ⟨valid.1, valid.2.1, valid.2.2.1, ?_, ?_⟩
  · simp [ValidReasons]
  · intro literal member
    have included := valid.2.2.2.2 literal member
    simp only [negations, List.map_nil, List.nil_append] at included ⊢
    exact mask_context_subset rename channel flag absent literal included

/-- A single actual shared-absent split eliminates both absent guards. -/
def initialMaskFlagTree (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) : CaseTree v :=
  .fork (maskAbsent rename .healthy channel)
    (maskCofactorTree rename channel flag true)
    (maskCofactorTree rename channel flag false)

theorem initialMaskFlagTree_valid (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) :
    ValidTree (initialState (relabel rename (SourceController.formula parameters)))
      (firstFlagContext rename channel flag ++
        [negate (maskOutput rename .healthy channel), maskOutput rename .faulty channel])
      (initialMaskFlagTree rename channel flag) :=
  ⟨maskCofactor_flag_valid rename channel flag true, maskCofactor_flag_valid rename channel flag false⟩

theorem initialMaskFlagTree_budget (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) :
    inferenceBudget (initialMaskFlagTree rename channel flag) = 1 := rfl

def initialMaskFlagDerived (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) :
    DerivedSubclause (relabel rename (SourceController.formula parameters))
      (compileTree (initialState (relabel rename (SourceController.formula parameters)))
        (initialMaskFlagTree rename channel flag)).state
      (firstFlagContext rename channel flag ++
        [negate (maskOutput rename .healthy channel), maskOutput rename .faulty channel]) :=
  compileTree_derived _ _ [] rfl _ _ (initialMaskFlagTree_valid rename channel flag)

def reverseMaskSide (flag absent : Bool) : Side :=
  if flag ^^ absent then .healthy else .faulty

def reverseMaskClause (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) : Clause (Fin v) :=
  let side := reverseMaskSide flag absent
  let cursor := initialMaskBefore side channel
  let producer : Bounded.Producer Nat := ⟨(cursor.lastID + 1, true),
    .xor (cursor.slots (.internal (.flag side parameters.firstBus)))
      (cursor.slots (.internal (.absent side parameters.firstBus channel)))⟩
  Rows.mapClause rename (producer.rows[(maskCofactorIndex flag absent).val]'(by
    change (maskCofactorIndex flag absent).val < 4
    exact (maskCofactorIndex flag absent).isLt))

def reverseMaskRow (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    Rows.Available (initialState (relabel rename (SourceController.formula parameters)))
      (reverseMaskClause rename channel flag absent) :=
  (initialMaskOriginalRows rename (reverseMaskSide flag absent) channel).row
    ⟨(maskCofactorIndex flag absent).val, by
      change (maskCofactorIndex flag absent).val < 4
      exact (maskCofactorIndex flag absent).isLt⟩

def reverseMaskCofactorTree (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) : CaseTree v :=
  .leaf ⟨(reverseMaskRow rename channel flag absent).id, reverseMaskClause rename channel flag absent, []⟩

theorem reverseMaskClause_eq (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    reverseMaskClause rename channel flag absent =
      match flag, absent with
      | false, false => [maskFlag rename .faulty channel, maskAbsent rename .faulty channel,
          negate (maskOutput rename .faulty channel)]
      | true, true => [negate (maskFlag rename .faulty channel), negate (maskAbsent rename .faulty channel),
          negate (maskOutput rename .faulty channel)]
      | false, true => [maskFlag rename .healthy channel, negate (maskAbsent rename .healthy channel),
          maskOutput rename .healthy channel]
      | true, false => [negate (maskFlag rename .healthy channel), maskAbsent rename .healthy channel,
          maskOutput rename .healthy channel] := by
  cases flag <;> cases absent <;> rfl

theorem reverseMaskCofactor_valid (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    ValidTree (initialState (relabel rename (SourceController.formula parameters)))
      ((firstFlagContext rename channel flag ++
        [maskOutput rename .healthy channel, negate (maskOutput rename .faulty channel)]) ++
        [assignmentGuard (maskAbsent rename .healthy channel) absent])
      (reverseMaskCofactorTree rename channel flag absent) := by
  refine ⟨(reverseMaskRow rename channel flag absent).present,
    (reverseMaskRow rename channel flag absent).bound, ?_, ?_, ?_⟩
  · simp [KnownReasons]
  · simp [ValidReasons]
  · change ClauseSubset (reverseMaskClause rename channel flag absent)
      ((firstFlagContext rename channel flag ++
        [maskOutput rename .healthy channel, negate (maskOutput rename .faulty channel)]) ++
        [assignmentGuard (maskAbsent rename .healthy channel) absent])
    have same := maskAbsent_equal rename channel
    rw [reverseMaskClause_eq]
    cases flag <;> cases absent <;>
      simp [firstFlagContext, assignmentGuard, ← same, ClauseSubset, negations] <;> aesop

def reverseMaskFlagTree (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) : CaseTree v :=
  .fork (maskAbsent rename .healthy channel)
    (reverseMaskCofactorTree rename channel flag true)
    (reverseMaskCofactorTree rename channel flag false)

theorem reverseMaskFlagTree_valid (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) :
    ValidTree (initialState (relabel rename (SourceController.formula parameters)))
      (firstFlagContext rename channel flag ++
        [maskOutput rename .healthy channel, negate (maskOutput rename .faulty channel)])
      (reverseMaskFlagTree rename channel flag) :=
  ⟨reverseMaskCofactor_valid rename channel flag true, reverseMaskCofactor_valid rename channel flag false⟩

theorem reverseMaskFlagTree_budget (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) :
    inferenceBudget (reverseMaskFlagTree rename channel flag) = 1 := rfl

def reverseMaskFlagDerived (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag : Bool) :
    DerivedSubclause (relabel rename (SourceController.formula parameters))
      (compileTree (initialState (relabel rename (SourceController.formula parameters)))
        (reverseMaskFlagTree rename channel flag)).state
      (firstFlagContext rename channel flag ++
        [maskOutput rename .healthy channel, negate (maskOutput rename .faulty channel)]) :=
  compileTree_derived _ _ [] rfl _ _ (reverseMaskFlagTree_valid rename channel flag)

end Controller.NativeProof.SourceSlotFrames
