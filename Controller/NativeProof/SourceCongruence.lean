module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceFoldOccurrences
public import Controller.NativeProof.Selector

@[expose] public section

/-! Native congruence stages consume rows of the actual source input. The
source cursor and original producer position are computed from the traversal,
including the continuation to the complete compiled formula. -/
namespace Controller.NativeProof.SourceCongruence
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceFoldOccurrences

variable {parameters : Parameters}

/-- A single emission occupies the entry offset of its actual input cursor. -/
def emitOwner (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (gate : Gate Nat) (retained : EntriesBefore (cursor.emitNative slot gate) (compile parameters)) :
    Fin (compile parameters).entries.length :=
  ⟨cursor.entries.length, by
    rcases retained with ⟨suffix, equality⟩
    rw [equality]
    simp only [Cursor.emitNative, Cursor.emit, Cursor.assign, List.length_append, List.length_cons, List.length_nil]
    omega⟩

theorem emitOwner_producer (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (gate : Gate Nat) (retained : EntriesBefore (cursor.emitNative slot gate) (compile parameters)) :
    (compile parameters).entries[(emitOwner cursor slot gate retained).val].producer =
      (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat) := by
  rcases retained with ⟨suffix, equality⟩
  simp [emitOwner, equality, Cursor.emitNative, Cursor.emit, Cursor.assign, List.getElem_append]

def emitRows (rename : Nat → Fin v) (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emitNative slot gate) (compile parameters)) :
    SourceFoldProjection.OriginalRows (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat) := by
  have equality := emitOwner_producer cursor slot gate retained
  refine ⟨?_⟩
  intro index
  have bound : index.val <
      (compile parameters).entries[(emitOwner cursor slot gate retained).val].producer.rows.length := by
    simpa only [equality] using index.isLt
  have row := SourceRows.fullProducerRow parameters rename (emitOwner cursor slot gate retained) ⟨index.val, bound⟩
  simpa only [equality] using row

def initialMaskStep (side : Side) (cursor : Cursor parameters) (channel : Fin parameters.channels) :
    Cursor parameters :=
  cursor.emitNative (.internal (.mask side parameters.firstBus channel))
    (.xor (cursor.slots (.internal (.flag side parameters.firstBus)))
      (cursor.slots (.internal (.absent side parameters.firstBus channel))))

def initialMaskBefore (side : Side) (channel : Fin parameters.channels) : Cursor parameters :=
  occurrenceCursor (initialMaskStep side) (tailStart side)
    ((List.finRange parameters.channels).take channel.val)

theorem initialMasks_before_tail (side : Side) :
    EntriesBefore (initialMasks parameters side (tailStart side))
      (SourceController.tail parameters side (tailStart side)) := by
  have stages := foldl_before (fun cursor bus => laterBus parameters side bus cursor)
    (fun cursor bus => laterBus_before side bus cursor)
    (laterBuses (parameters := parameters)) (initialMasks parameters side (tailStart side))
  exact stages.trans ((negateFlags_before side _).trans
    (foldl_before (fun cursor channel => eligible parameters side channel cursor)
      (fun cursor channel => eligible_before side channel cursor)
      (List.finRange parameters.channels) (negateFlags parameters side (tailStages side))))

theorem initial_mask_before_compile (side : Side) (channel : Fin parameters.channels) :
    EntriesBefore (initialMaskStep side (initialMaskBefore side channel) channel) (compile parameters) := by
  have bound : channel.val < (List.finRange parameters.channels).length := by simpa using channel.isLt
  have split := positional_decomposition (List.finRange parameters.channels) ⟨channel.val, bound⟩
  have decomposition : List.finRange parameters.channels =
      (List.finRange parameters.channels).take channel.val ++ channel ::
        (List.finRange parameters.channels).drop (channel.val + 1) := by simpa using split
  have selected := occurrence_before_of_eq (initialMaskStep side)
    (fun cursor index => emitNative_before cursor _ _) (tailStart side)
    (List.finRange parameters.channels) _ _ channel decomposition
  exact selected.trans ((initialMasks_before_tail side).trans (tail_end_before_compile side))

/-- These four XOR rows are original input rows at the actual initial mask
emission, rather than a named-gate semantic adapter. -/
def initialMaskOriginalRows (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :
    let cursor := initialMaskBefore side channel
    SourceFoldProjection.OriginalRows (Controller.Resolution.initialState
      (relabel rename (SourceController.formula parameters))) rename
      (⟨(cursor.lastID + 1, true), .xor (cursor.slots (.internal (.flag side parameters.firstBus)))
        (cursor.slots (.internal (.absent side parameters.firstBus channel)))⟩ : Bounded.Producer Nat) := by
  dsimp only
  apply emitRows
  exact initial_mask_before_compile side channel

open Controller.Resolution Controller.Resolution.Cases Controller.Resolution.RUP
open Controller.NativeProof.SourceFoldProjection

/-- The mapped inputs and output belong to the actual selected source XOR. -/
def maskFlag (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename ((initialMaskBefore side channel).slots (.internal (.flag side parameters.firstBus)))

def maskAbsent (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename ((initialMaskBefore side channel).slots (.internal (.absent side parameters.firstBus channel)))

def maskOutput (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) : Literal (Fin v) :=
  mapLiteral rename ((initialMaskBefore side channel).lastID + 1, true)

def assignmentGuard (literal : Literal (Fin v)) (value : Bool) : Literal (Fin v) :=
  if value then negate literal else literal

/-- Both copies' actual input guards express one fixed XOR cofactor. -/
def maskContext (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) : Clause (Fin v) :=
  [assignmentGuard (maskFlag rename .healthy channel) flag,
   assignmentGuard (maskAbsent rename .healthy channel) absent,
   assignmentGuard (maskFlag rename .faulty channel) flag,
   assignmentGuard (maskAbsent rename .faulty channel) absent]

/-- Even parity contradicts the assumed healthy output; odd parity propagates
from the original faulty XOR row. The row choice is computational Boolean data. -/
def maskCofactorIndex (flag absent : Bool) : Fin 4 :=
  match flag, absent with
  | false, false => ⟨0, by decide⟩
  | true, true => ⟨1, by decide⟩
  | false, true => ⟨2, by decide⟩
  | true, false => ⟨3, by decide⟩

def maskCofactorSide (flag absent : Bool) : Side :=
  if flag ^^ absent then .faulty else .healthy

def maskCofactorClause (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) : Clause (Fin v) :=
  let side := maskCofactorSide flag absent
  let cursor := initialMaskBefore side channel
  let producer : Bounded.Producer Nat := ⟨(cursor.lastID + 1, true),
    .xor (cursor.slots (.internal (.flag side parameters.firstBus)))
      (cursor.slots (.internal (.absent side parameters.firstBus channel)))⟩
  Rows.mapClause rename (producer.rows[(maskCofactorIndex flag absent).val]'(by
    change (maskCofactorIndex flag absent).val < 4
    exact (maskCofactorIndex flag absent).isLt))

def maskCofactorRow (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    Rows.Available (initialState (relabel rename (SourceController.formula parameters)))
      (maskCofactorClause rename channel flag absent) :=
  let side := maskCofactorSide flag absent
  (initialMaskOriginalRows rename side channel).row
    ⟨(maskCofactorIndex flag absent).val, by change (maskCofactorIndex flag absent).val < 4; exact (maskCofactorIndex flag absent).isLt⟩

def maskCofactorTree (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) : CaseTree v :=
  let row := maskCofactorRow rename channel flag absent
  .leaf ⟨row.id, maskCofactorClause rename channel flag absent, []⟩

theorem maskCofactorTree_valid (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    ValidTree (initialState (relabel rename (SourceController.formula parameters)))
      (maskContext rename channel flag absent ++
        [negate (maskOutput rename .healthy channel), maskOutput rename .faulty channel])
      (maskCofactorTree rename channel flag absent) := by
  refine ⟨(maskCofactorRow rename channel flag absent).present,
    (maskCofactorRow rename channel flag absent).bound, ?_, ?_, ?_⟩
  · simp [KnownReasons, maskCofactorTree]
  · simp [ValidReasons, maskCofactorTree]
  · cases flag <;> cases absent <;>
      simp [maskCofactorClause, maskCofactorSide, maskCofactorIndex,
        Bounded.Producer.rows, Gate.clauses, Rows.mapClause, maskContext, assignmentGuard,
        maskFlag, maskAbsent, maskOutput, mapLiteral, ClauseSubset, negations] <;> aesop

/-- This cofactor reuses one original row and emits no resolution step. -/
theorem maskCofactorTree_budget (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    inferenceBudget (maskCofactorTree rename channel flag absent) = 0 := rfl

/-- The concrete native cofactor has an actual accepted trace and retains its
stronger original clause rather than inserting the requested conclusion. -/
def maskCofactorDerived (rename : Nat → Fin v) (channel : Fin parameters.channels) (flag absent : Bool) :
    DerivedSubclause (relabel rename (SourceController.formula parameters))
      (compileTree (initialState (relabel rename (SourceController.formula parameters)))
        (maskCofactorTree rename channel flag absent)).state
      (maskContext rename channel flag absent ++
        [negate (maskOutput rename .healthy channel), maskOutput rename .faulty channel]) :=
  compileTree_derived _ _ [] rfl _ _ (maskCofactorTree_valid rename channel flag absent)

end Controller.NativeProof.SourceCongruence
