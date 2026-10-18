module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMismatchSeed

@[expose] public section

/-! Qualifier guards and private negated flags are bound to their actual
source emission positions. Original rows retain explicit occurrence IDs. -/
namespace Controller.NativeProof.SourceQualifierOccurrences
open Controller.CNF Controller.Native Controller.Native.SourceController
open Controller.Resolution
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceCongruence Controller.NativeProof.SourceMismatchBranch
open Controller.NativeProof.SourceFoldProjection
variable {parameters : Parameters} {v : Nat}

/-- The private NOT emission also updates the concrete negated-handle table. -/
def negateStep (side : Side) (cursor : Cursor parameters) (bus : Fin parameters.buses) : Cursor parameters :=
  let emitted := cursor.emit (.negatedFlag side bus) (.not (cursor.slots (.internal (.flag side bus))))
  { emitted.2 with negated := (Function.update emitted.2.negated side
      (Function.update (emitted.2.negated side) bus emitted.1)) }

def negateBefore (side : Side) (bus : Fin parameters.buses) : Cursor parameters :=
  occurrenceCursor (negateStep side) (tailStages side) ((List.finRange parameters.buses).take bus.val)

theorem negateStep_before (side : Side) (cursor : Cursor parameters) (bus : Fin parameters.buses) :
    EntriesBefore cursor (negateStep side cursor bus) := emit_before cursor _ _

theorem negate_traversal (side : Side) (cursor : Cursor parameters) :
    (List.finRange parameters.buses).foldl (negateStep side) cursor = negateFlags parameters side cursor := rfl

theorem tail_end_before_controller (side : Side) :
    EntriesBefore (SourceController.tail parameters side (tailStart side)) (controller parameters) := by
  cases side with
  | healthy => exact tail_before .faulty _
  | faulty => exact EntriesBefore.refl _

theorem negate_occurrence_before_controller (side : Side) (bus : Fin parameters.buses) :
    EntriesBefore (negateStep side (negateBefore side bus) bus) (controller parameters) := by
  have bound : bus.val < (List.finRange parameters.buses).length := by simpa using bus.isLt
  have decomposition : List.finRange parameters.buses =
      (List.finRange parameters.buses).take bus.val ++ bus ::
        (List.finRange parameters.buses).drop (bus.val + 1) := by
    simpa using positional_decomposition (List.finRange parameters.buses) ⟨bus.val, bound⟩
  have selected := occurrence_before_of_eq (negateStep side) (negateStep_before side)
    (tailStages side) (List.finRange parameters.buses) _ _ bus decomposition
  have later := foldl_before (fun cursor channel => eligible parameters side channel cursor)
    (fun cursor channel => eligible_before side channel cursor)
    (List.finRange parameters.channels) (negateFlags parameters side (tailStages side))
  exact selected.trans (later.trans (tail_end_before_controller side))

theorem negate_occurrence_before_compile (side : Side) (bus : Fin parameters.buses) :
    EntriesBefore (negateStep side (negateBefore side bus) bus) (compile parameters) :=
  (negate_occurrence_before_controller side bus).trans controller_before_compile

/-- Unlike native-slot emission, a private owner does not assign a named slot. -/
def rawEmitOwner (cursor : Cursor parameters) (owner : Owner parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emit owner gate).2 (compile parameters)) :
    Fin (compile parameters).entries.length :=
  ⟨cursor.entries.length, by
    rcases retained with ⟨suffix, equality⟩
    rw [equality]
    simp only [Cursor.emit, List.length_append, List.length_cons, List.length_nil]
    omega⟩

theorem rawEmitOwner_producer (cursor : Cursor parameters) (owner : Owner parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emit owner gate).2 (compile parameters)) :
    (compile parameters).entries[(rawEmitOwner cursor owner gate retained).val].producer =
      (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat) := by
  rcases retained with ⟨suffix, equality⟩
  simp [rawEmitOwner, equality, Cursor.emit, List.getElem_append]

def rawEmitRows (rename : Nat → Fin v) (cursor : Cursor parameters) (owner : Owner parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emit owner gate).2 (compile parameters)) :
    OriginalRows (initialState (relabel rename (formula parameters))) rename
      (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat) := by
  let actualOwner := rawEmitOwner cursor owner gate retained
  have producer : (compile parameters).entries[actualOwner.val].producer =
      (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat) :=
    rawEmitOwner_producer cursor owner gate retained
  refine ⟨?_⟩
  intro index
  have bound : index.val < (compile parameters).entries[actualOwner.val].producer.rows.length := by
    rw [producer]
    exact index.isLt
  let actual := ownedRow rename actualOwner ⟨index.val, bound⟩
  refine ⟨actual.id, ?_, actual.bound⟩
  simpa only [producer] using actual.present

theorem rawEmitRows_allowed (rename : Nat → Fin v) (cursor : Cursor parameters)
    (owner : Owner parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emit owner gate).2 (controller parameters))
    (index : Fin (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat).rows.length) :
    AllowedOriginal (parameters := parameters) rename
      ((rawEmitRows rename cursor owner gate (retained.trans controller_before_compile)).row index).id := by
  let actualOwner := rawEmitOwner cursor owner gate (retained.trans controller_before_compile)
  have ownerBound : actualOwner.val < (controller parameters).entries.length := by
    rcases retained with ⟨suffix, equality⟩
    simp only [actualOwner, rawEmitOwner]
    rw [equality]
    simp only [Cursor.emit, List.length_append, List.length_cons, List.length_nil]
    omega
  have producer : (compile parameters).entries[actualOwner.val].producer =
      (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat) :=
    rawEmitOwner_producer cursor owner gate (retained.trans controller_before_compile)
  have bound : index.val < (compile parameters).entries[actualOwner.val].producer.rows.length := by
    rw [producer]
    exact index.isLt
  exact Or.inl ⟨actualOwner, ownerBound, ⟨index.val, bound⟩, rfl⟩

def negatedFlagRows (rename : Nat → Fin v) (side : Side) (bus : Fin parameters.buses) :
    let cursor := negateBefore side bus
    OriginalRows (initialState (relabel rename (formula parameters))) rename
      (⟨(cursor.lastID + 1, true), .not (cursor.slots (.internal (.flag side bus)))⟩ : Bounded.Producer Nat) := by
  dsimp only
  exact rawEmitRows rename _ _ _ (negate_occurrence_before_compile side bus)

def guardBefore (side : Side) (channel : Fin parameters.channels) (bus : Fin parameters.buses) : Cursor parameters :=
  occurrenceCursor (eligibleGuardStep parameters side channel) (eligibleBefore side channel)
    ((List.finRange parameters.buses).take bus.val)

theorem eligible_occurrence_before_controller (side : Side) (channel : Fin parameters.channels) :
    EntriesBefore (eligible parameters side channel (eligibleBefore side channel)) (controller parameters) := by
  have bound : channel.val < (List.finRange parameters.channels).length := by simpa using channel.isLt
  have decomposition : List.finRange parameters.channels =
      (List.finRange parameters.channels).take channel.val ++ channel ::
        (List.finRange parameters.channels).drop (channel.val + 1) := by
    simpa using positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩
  have selected := occurrence_before_of_eq (fun cursor index => eligible parameters side index cursor)
    (fun cursor index => eligible_before side index cursor)
    (negateFlags parameters side (tailStages side)) (List.finRange parameters.channels) _ _ channel decomposition
  exact selected.trans (tail_end_before_controller side)

theorem guard_occurrence_before_controller (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    EntriesBefore (eligibleGuardStep parameters side channel (guardBefore side channel bus) bus)
      (controller parameters) := by
  have bound : bus.val < (List.finRange parameters.buses).length := by simpa using bus.isLt
  have decomposition : List.finRange parameters.buses =
      (List.finRange parameters.buses).take bus.val ++ bus ::
        (List.finRange parameters.buses).drop (bus.val + 1) := by
    simpa using positional_decomposition (List.finRange parameters.buses) ⟨bus.val, bound⟩
  have selected := occurrence_before_of_eq (eligibleGuardStep parameters side channel)
    (fun cursor bus => emitNative_before cursor _ _)
    (eligibleBefore side channel) (List.finRange parameters.buses) _ _ bus decomposition
  exact selected.trans ((foldNative_before (qualifierGuarded side channel) _ _ _).trans
    (eligible_occurrence_before_controller side channel))

theorem guard_occurrence_before_compile (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    EntriesBefore (eligibleGuardStep parameters side channel (guardBefore side channel bus) bus)
      (compile parameters) :=
  (guard_occurrence_before_controller side channel bus).trans controller_before_compile

/-- Native-slot emission retains the same explicit original occurrence ID. -/
theorem nativeEmitRows_allowed (rename : Nat → Fin v) (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emitNative slot gate) (controller parameters))
    (index : Fin (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat).rows.length) :
    AllowedOriginal (parameters := parameters) rename
      ((emitRowsExact rename cursor slot gate (retained.trans controller_before_compile)).row index).id := by
  let actualOwner := emitOwner cursor slot gate (retained.trans controller_before_compile)
  have ownerBound : actualOwner.val < (controller parameters).entries.length := by
    rcases retained with ⟨suffix, equality⟩
    simp only [actualOwner, emitOwner]
    rw [equality]
    simp only [Cursor.emitNative, Cursor.emit, Cursor.assign, List.length_append, List.length_cons, List.length_nil]
    omega
  have producer := emitOwner_producer cursor slot gate (retained.trans controller_before_compile)
  have bound : index.val < (compile parameters).entries[actualOwner.val].producer.rows.length := by
    rw [producer]
    exact index.isLt
  exact Or.inl ⟨actualOwner, ownerBound, ⟨index.val, bound⟩, rfl⟩

def guardRows (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) :
    let cursor := guardBefore side channel bus
    OriginalRows (initialState (relabel rename (formula parameters))) rename
      (⟨(cursor.lastID + 1, true), .or [cursor.negated side bus,
        cursor.slots (.primary (.request bus channel))]⟩ : Bounded.Producer Nat) := by
  dsimp only
  exact emitRowsExact rename _ _ _ (guard_occurrence_before_compile side channel bus)

theorem negatedFlagRows_allowed (rename : Nat → Fin v) (side : Side) (bus : Fin parameters.buses)
    (index : Fin 2) : AllowedOriginal (parameters := parameters) rename
      ((negatedFlagRows rename side bus).row ⟨index.val, by change index.val < 2; exact index.isLt⟩).id :=
  rawEmitRows_allowed rename _ _ _ (negate_occurrence_before_controller side bus) _

theorem guardRows_allowed (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels)
    (bus : Fin parameters.buses) (index : Fin 3) : AllowedOriginal (parameters := parameters) rename
      ((guardRows rename side channel bus).row ⟨index.val, by change index.val < 3; exact index.isLt⟩).id :=
  nativeEmitRows_allowed rename _ _ _ (guard_occurrence_before_controller side channel bus) _

end Controller.NativeProof.SourceQualifierOccurrences
