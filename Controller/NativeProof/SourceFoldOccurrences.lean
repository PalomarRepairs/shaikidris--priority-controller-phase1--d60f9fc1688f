module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceFoldOwners

@[expose] public section

/-! Original producer blocks at traversal occurrences. Cursors are formed by
executing the actual preceding list prefix; continuation preserves their entry
positions in the source formula. -/
namespace Controller.NativeProof.SourceFoldOccurrences
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.NativeProof.SourceFoldOwners

variable {parameters : Parameters}

/-- The cursor immediately before an occurrence in a source traversal. -/
def occurrenceCursor {α : Type} (step : Cursor parameters → α → Cursor parameters)
    (start : Cursor parameters) (before : List α) : Cursor parameters :=
  before.foldl step start

/-- A selected step survives the exact remaining traversal suffix. -/
theorem occurrence_before {α : Type}
    (step : Cursor parameters → α → Cursor parameters)
    (preservesEntries : ∀ cursor value, EntriesBefore cursor (step cursor value))
    (start : Cursor parameters) (before after : List α) (value : α) :
    EntriesBefore (step (occurrenceCursor step start before) value)
      ((before ++ value :: after).foldl step start) := by
  simpa only [List.foldl_append, List.foldl_cons, occurrenceCursor] using
    foldl_before step preservesEntries after (step (before.foldl step start) value)

/-- An explicit traversal decomposition fixes the occurrence, including
repeated values, without searching for an owner. -/
theorem occurrence_before_of_eq {α : Type}
    (step : Cursor parameters → α → Cursor parameters)
    (preservesEntries : ∀ cursor value, EntriesBefore cursor (step cursor value))
    (start : Cursor parameters) (values before after : List α) (value : α)
    (decomposition : values = before ++ value :: after) :
    EntriesBefore (step (occurrenceCursor step start before) value)
      (values.foldl step start) := by
  rw [decomposition]
  exact occurrence_before step preservesEntries start before after value

/-- A traversal position supplies its own decomposition from the actual list. -/
theorem positional_decomposition {α : Type} (values : List α) (index : Fin values.length) :
    values = values.take index.val ++ values[index.val] :: values.drop (index.val + 1) := by
  have split := List.take_append_drop index.val values
  rw [List.drop_eq_getElem_cons index.isLt] at split
  exact split.symm

/-- Every decoder occurrence retains the entry block emitted by that node. -/
theorem decoder_occurrence_before (side : Side) (start : Cursor parameters)
    (before after : List (Fin parameters.decoder.nodeCount))
    (node : Fin parameters.decoder.nodeCount) :
    EntriesBefore
      (decoderNode parameters side node
        (occurrenceCursor (fun cursor index => decoderNode parameters side index cursor) start before))
      ((before ++ node :: after).foldl
        (fun cursor index => decoderNode parameters side index cursor) start) :=
  occurrence_before _ (fun cursor index => decoderNode_before side index cursor) start before after node

/-- The actual input cursor of the selected decoder side. -/
def decoderStart (side : Side) : Cursor parameters :=
  match side with
  | .healthy => originalObservations parameters (controller parameters)
  | .faulty => attachDecoder parameters .healthy
      (originalObservations parameters (controller parameters))

theorem decoder_end_before_compile (side : Side) :
    EntriesBefore (attachDecoder parameters side (decoderStart side)) (compile parameters) := by
  cases side with
  | healthy =>
      exact (attachDecoder_before .faulty _).trans (newObservations_before _)
  | faulty => exact newObservations_before _

/-- The actual cursor prefix preceding a decoder occurrence. -/
def decoderBefore (side : Side) (before : List (Fin parameters.decoder.nodeCount)) :
    Cursor parameters :=
  occurrenceCursor (fun cursor node => decoderNode parameters side node cursor)
    (decoderStart side) before

theorem decoder_occurrence_before_compile (side : Side)
    (before after : List (Fin parameters.decoder.nodeCount))
    (node : Fin parameters.decoder.nodeCount)
    (decomposition : List.finRange parameters.decoder.nodeCount = before ++ node :: after) :
    EntriesBefore (decoderNode parameters side node (decoderBefore side before)) (compile parameters) := by
  have localPrefix := occurrence_before_of_eq
    (fun cursor index => decoderNode parameters side index cursor)
    (fun cursor index => decoderNode_before side index cursor)
    (decoderStart side) (List.finRange parameters.decoder.nodeCount) before after node decomposition
  exact localPrefix.trans (decoder_end_before_compile side)

/-- A disjunction's allocator is the actual selected source step, including
empty and unary disjunctions. -/
theorem decoder_disjunction_before_compile (side : Side)
    (before after : List (Fin parameters.decoder.nodeCount))
    (node : Fin parameters.decoder.nodeCount)
    (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children)
    (decomposition : List.finRange parameters.decoder.nodeCount = before ++ node :: after) :
    EntriesBefore
      ((decoderBefore side before).foldNative (.internal (.decoder side node)) .disjunction
        (children.map fun child => (decoderBefore side before).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child)))))
      (compile parameters) := by
  have retained := decoder_occurrence_before_compile side before after node decomposition
  simpa only [decoderNode, shape] using retained

/-- The decoder position determines its cursor without a supplied owner map. -/
def decoderPositionBefore (side : Side) (node : Fin parameters.decoder.nodeCount) : Cursor parameters :=
  decoderBefore side ((List.finRange parameters.decoder.nodeCount).take node.val)

theorem decoder_position_before_compile (side : Side) (node : Fin parameters.decoder.nodeCount) :
    EntriesBefore (decoderNode parameters side node (decoderPositionBefore side node)) (compile parameters) := by
  have bound : node.val < (List.finRange parameters.decoder.nodeCount).length := by simpa using node.isLt
  have split := positional_decomposition (List.finRange parameters.decoder.nodeCount) ⟨node.val, bound⟩
  have decomposition : List.finRange parameters.decoder.nodeCount =
      (List.finRange parameters.decoder.nodeCount).take node.val ++ node ::
        (List.finRange parameters.decoder.nodeCount).drop (node.val + 1) := by
    simpa using split
  exact decoder_occurrence_before_compile side _ _ node decomposition

/-- Actual full-input rows for the allocator at a represented disjunction.
Empty and unary cases retain their actual producer counts. -/
def decoderDisjunctionRows (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) :
    SourceFoldProjection.RowSupply (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (SourceSerialFold.allocate .disjunction (decoderPositionBefore side node).lastID
        (children.map fun child => (decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child))))).producers := by
  apply foldRows rename (decoderPositionBefore side node) (.internal (.decoder side node)) .disjunction
  have retained := decoder_position_before_compile side node
  simpa only [decoderNode, shape] using retained

/-- The controller tail starts at its actual preceding side cursor. -/
def tailStart (side : Side) : Cursor parameters :=
  match side with
  | .healthy => interface parameters
  | .faulty => SourceController.tail parameters .healthy (interface parameters)

theorem tail_end_before_compile (side : Side) :
    EntriesBefore (SourceController.tail parameters side (tailStart side)) (compile parameters) := by
  cases side with
  | healthy => exact (tail_before .faulty _).trans controller_before_compile
  | faulty => exact controller_before_compile

def laterBuses : List (Fin parameters.buses) :=
  (List.finRange parameters.buses).filter fun bus => bus.val != 0

def busBefore (side : Side) (position : Fin (laterBuses (parameters := parameters)).length) : Cursor parameters :=
  occurrenceCursor (fun cursor bus => laterBus parameters side bus cursor)
    (initialMasks parameters side (tailStart side))
    ((laterBuses (parameters := parameters)).take position.val)

theorem bus_occurrence_before_compile (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    EntriesBefore
      (laterBus parameters side (laterBuses (parameters := parameters))[position.val] (busBefore side position))
      (compile parameters) := by
  have selected := occurrence_before_of_eq
    (fun cursor bus => laterBus parameters side bus cursor)
    (fun cursor bus => laterBus_before side bus cursor)
    (initialMasks parameters side (tailStart side)) (laterBuses (parameters := parameters))
    ((laterBuses (parameters := parameters)).take position.val)
    ((laterBuses (parameters := parameters)).drop (position.val + 1))
    ((laterBuses (parameters := parameters))[position.val])
    (positional_decomposition _ position)
  let stages := (laterBuses (parameters := parameters)).foldl
    (fun cursor bus => laterBus parameters side bus cursor)
    (initialMasks parameters side (tailStart side))
  have continuation : EntriesBefore stages (SourceController.tail parameters side (tailStart side)) :=
    (negateFlags_before side stages).trans
      (foldl_before (fun cursor channel => eligible parameters side channel cursor)
        (fun cursor channel => eligible_before side channel cursor)
        (List.finRange parameters.channels) (negateFlags parameters side stages))
  exact selected.trans (continuation.trans (tail_end_before_compile side))

def termStep (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters)
    (channel : Fin parameters.channels) : Cursor parameters :=
  cursor.foldNative (.internal (.term side bus channel)) .conjunction
    ([cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request bus channel))] ++
      ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map fun earlier =>
        cursor.slots (.internal (.mask side earlier channel)))

def busTerms (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters) : Cursor parameters :=
  (List.finRange parameters.channels).foldl (termStep side bus) cursor

def busFlag (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters) : Cursor parameters :=
  let terms := busTerms side bus cursor
  terms.foldNative (.internal (.flag side bus)) .disjunction
    ((List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel)))

theorem flag_before_laterBus (side : Side) (bus : Fin parameters.buses) (cursor : Cursor parameters) :
    EntriesBefore (busFlag side bus cursor) (laterBus parameters side bus cursor) := by
  exact foldl_before _ (fun current channel =>
    (emitNative_before current _ _).trans (emitNative_before _ _ _))
    (List.finRange parameters.channels) (busFlag side bus cursor)

/-- All flag-fold rows come from the represented bus occurrence in the full
source input; the bus position determines the original producer offsets. -/
def laterFlagRows (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) :
    let bus := (laterBuses (parameters := parameters))[position.val]
    let terms := busTerms side bus (busBefore side position)
    SourceFoldProjection.RowSupply (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (SourceSerialFold.allocate .disjunction terms.lastID
        ((List.finRange parameters.channels).map fun channel => terms.slots (.internal (.term side bus channel)))).producers := by
  dsimp only
  apply foldRows
  exact (flag_before_laterBus side _ _).trans (bus_occurrence_before_compile side position)

def termBefore (side : Side) (position : Fin (laterBuses (parameters := parameters)).length)
    (channel : Fin parameters.channels) : Cursor parameters :=
  occurrenceCursor (termStep side ((laterBuses (parameters := parameters))[position.val]))
    (busBefore side position) ((List.finRange parameters.channels).take channel.val)

theorem term_occurrence_before_compile (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    EntriesBefore
      (termStep side ((laterBuses (parameters := parameters))[position.val])
        (termBefore side position channel) channel) (compile parameters) := by
  have bound : channel.val < (List.finRange parameters.channels).length := by simpa using channel.isLt
  have split := positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩
  have decomposition : List.finRange parameters.channels =
      (List.finRange parameters.channels).take channel.val ++ channel ::
        (List.finRange parameters.channels).drop (channel.val + 1) := by simpa using split
  have selected := occurrence_before_of_eq
    (termStep side ((laterBuses (parameters := parameters))[position.val]))
    (fun cursor index => foldNative_before cursor _ _ _)
    (busBefore side position) (List.finRange parameters.channels) _ _ channel decomposition
  exact selected.trans ((foldNative_before _ _ _ _).trans
    ((flag_before_laterBus side _ _).trans (bus_occurrence_before_compile side position)))

/-- Actual original rows for a high-fanin term AND, loaded at its concrete
channel position within its represented later bus. -/
def laterTermRows (rename : Nat → Fin v) (side : Side)
    (position : Fin (laterBuses (parameters := parameters)).length) (channel : Fin parameters.channels) :
    let bus := (laterBuses (parameters := parameters))[position.val]
    let cursor := termBefore side position channel
    SourceFoldProjection.RowSupply (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (SourceSerialFold.allocate .conjunction cursor.lastID
        ([cursor.slots (.primary (.enable channel)), cursor.slots (.primary (.request bus channel))] ++
          ((List.finRange parameters.buses).filter (fun earlier => earlier < bus)).map fun earlier =>
            cursor.slots (.internal (.mask side earlier channel)))).producers := by
  dsimp only
  apply foldRows
  exact term_occurrence_before_compile side position channel

def tailStages (side : Side) : Cursor parameters :=
  (laterBuses (parameters := parameters)).foldl
    (fun cursor bus => laterBus parameters side bus cursor)
    (initialMasks parameters side (tailStart side))

def eligibleBefore (side : Side) (channel : Fin parameters.channels) : Cursor parameters :=
  occurrenceCursor (fun cursor index => eligible parameters side index cursor)
    (negateFlags parameters side (tailStages side))
    ((List.finRange parameters.channels).take channel.val)

def qualifierGuarded (side : Side) (channel : Fin parameters.channels) : Cursor parameters :=
  (List.finRange parameters.buses).foldl (fun cursor bus =>
    cursor.emitNative (.internal (.qualifierGuard side bus channel))
      (.or [cursor.negated side bus, cursor.slots (.primary (.request bus channel))]))
    (eligibleBefore side channel)

theorem eligible_occurrence_before_compile (side : Side) (channel : Fin parameters.channels) :
    EntriesBefore (eligible parameters side channel (eligibleBefore side channel)) (compile parameters) := by
  have bound : channel.val < (List.finRange parameters.channels).length := by simpa using channel.isLt
  have split := positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩
  have decomposition : List.finRange parameters.channels =
      (List.finRange parameters.channels).take channel.val ++ channel ::
        (List.finRange parameters.channels).drop (channel.val + 1) := by simpa using split
  have selected := occurrence_before_of_eq
    (fun cursor index => eligible parameters side index cursor)
    (fun cursor index => eligible_before side index cursor)
    (negateFlags parameters side (tailStages side)) (List.finRange parameters.channels) _ _ channel decomposition
  exact selected.trans (tail_end_before_compile side)

/-- Actual qualifier-AND rows follow the concrete guard-emission traversal.
No external owner lookup or already-derived gate clause is assumed. -/
def qualifierRows (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    let cursor := qualifierGuarded side channel
    SourceFoldProjection.RowSupply (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (SourceSerialFold.allocate .conjunction cursor.lastID
        (cursor.slots (.primary (.enable channel)) ::
          (List.finRange parameters.buses).map fun bus => cursor.slots (.internal (.qualifierGuard side bus channel)))).producers := by
  dsimp only
  apply foldRows
  exact eligible_occurrence_before_compile side channel

end Controller.NativeProof.SourceFoldOccurrences
