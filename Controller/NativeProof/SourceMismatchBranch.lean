module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceBusSchedule

@[expose] public section

/-! Original physical units and interface equations supply the differing
first-flag branch. The permitted original IDs include drive units and exclude
observation equations and the detection assertion. -/
namespace Controller.NativeProof.SourceMismatchBranch
open Controller.Native Controller.Native.SourceController Controller.CNF
open Controller.Resolution Controller.Resolution.Cases
open Controller.NativeProof.SourceFoldOwners Controller.NativeProof.SourceCongruence
open Controller.NativeProof.SourceFoldProjection Controller.NativeProof.FoldProjection
open Controller.NativeProof.SourceBusSchedule
variable {parameters : Parameters} {v : Nat}

def equationRows := (compile parameters).entries.flatMap fun entry => entry.producer.rows

def physicalUnit (index : Fin 3) : Literal Nat :=
  (assertions parameters)[index.val]'(by simp [assertions]; omega)

/-- Only the first three assertion occurrences are physical input units. -/
def physicalUnitRow (rename : Nat → Fin v) (index : Fin 3) :
    Rows.Available (initialState (relabel rename (formula parameters)))
      [mapLiteral rename (physicalUnit (parameters := parameters) index)] := by
  let position : Fin (formula parameters).clauses.size :=
    ⟨(equationRows (parameters := parameters)).length + index.val, by
      simp [SourceRows.formula_as_rows, ofClauses, assertions, equationRows]; omega⟩
  have content : (formula parameters).clauses[position.val] =
      [physicalUnit (parameters := parameters) index] := by
    simp [SourceRows.formula_as_rows, ofClauses, position, List.getElem_append,
      physicalUnit, equationRows]
  refine ⟨position.val + 1, ?_, ?_⟩
  · simpa only [content, Rows.mapClause, List.map_cons, List.map_nil, mapLiteral] using
      Rows.relabeled_row rename (formula parameters) position
  · simp only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map]
    exact Nat.succ_le_of_lt position.isLt

/-- The original owner/index occurrence ID is explicit; clause equalities occur
only in its row-presence proof. -/
def ownedRow (rename : Nat → Fin v) (owner : Fin (compile parameters).entries.length)
    (index : Fin (compile parameters).entries[owner.val].producer.rows.length) :
    Rows.Available (initialState (relabel rename (formula parameters)))
      (Rows.mapClause rename (compile parameters).entries[owner.val].producer.rows[index.val]) := by
  let position : Fin (formula parameters).clauses.size :=
    ⟨(SourceRows.before parameters owner).length + index.val, by
      simp only [SourceRows.formula_as_rows, ofClauses, List.size_toArray, List.length_append]
      rw [SourceRows.sourceClauses_split parameters owner]
      simp only [List.length_append]
      have bound := index.isLt
      omega⟩
  have content : (formula parameters).clauses[position.val] =
      (compile parameters).entries[owner.val].producer.rows[index.val] := by
    simp [SourceRows.formula_as_rows, ofClauses, position,
      SourceRows.sourceClauses_split parameters owner, List.getElem_append, index.isLt]
  refine ⟨position.val + 1, ?_, ?_⟩
  · simpa only [content] using Rows.relabeled_row rename (formula parameters) position
  · simp only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map]
    exact Nat.succ_le_of_lt position.isLt

def emitRowsExact (rename : Nat → Fin v) (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emitNative slot gate) (compile parameters)) :
    OriginalRows (initialState (relabel rename (formula parameters))) rename
      (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat) := by
  let owner := emitOwner cursor slot gate retained
  have producer : (compile parameters).entries[owner.val].producer =
      (⟨(cursor.lastID + 1, true), gate⟩ : Bounded.Producer Nat) :=
    emitOwner_producer cursor slot gate retained
  refine ⟨?_⟩
  intro index
  have bound : index.val < (compile parameters).entries[owner.val].producer.rows.length := by
    rw [producer]
    exact index.isLt
  let row := ownedRow rename owner ⟨index.val, bound⟩
  refine ⟨row.id, ?_, row.bound⟩
  simpa only [producer] using row.present

theorem physicalUnitRow_id (rename : Nat → Fin v) (index : Fin 3) :
    (physicalUnitRow (parameters := parameters) rename index).id =
      (equationRows (parameters := parameters)).length + index.val + 1 := rfl

/-- Equation support is restricted to the controller prefix; the three
physical units occupy separate original occurrences after all equations. -/
def AllowedOriginal (rename : Nat → Fin v) (id : Nat) : Prop :=
  (∃ owner : Fin (compile parameters).entries.length,
    owner.val < (controller parameters).entries.length ∧
    ∃ index : Fin (compile parameters).entries[owner.val].producer.rows.length,
      id = (ownedRow rename owner index).id) ∨
  ∃ index : Fin 3, id = (physicalUnitRow (parameters := parameters) rename index).id

theorem physicalUnit_allowed (rename : Nat → Fin v) (index : Fin 3) :
    AllowedOriginal (parameters := parameters) rename
      (physicalUnitRow (parameters := parameters) rename index).id := Or.inr ⟨index, rfl⟩

theorem physicalUnit_drive_one (drive : parameters.drive = true) :
    physicalUnit (parameters := parameters) ⟨0, by decide⟩ =
      ((sourceRoleMap parameters (.internal (.absent .healthy parameters.firstBus parameters.bridge.target))).1, false) ∧
    physicalUnit (parameters := parameters) ⟨1, by decide⟩ =
      ((sourceRoleMap parameters (.internal .driver)).1, true) ∧
    physicalUnit (parameters := parameters) ⟨2, by decide⟩ =
      ((sourceRoleMap parameters (.primary .wire)).1, true) := by
  simp [physicalUnit, assertions, drive]

theorem allowedOriginal_bound (rename : Nat → Fin v) (id : Nat)
    (allowed : AllowedOriginal (parameters := parameters) rename id) :
    id ≤ (equationRows (parameters := parameters)).length + 3 := by
  rcases allowed with ⟨owner, _, index, same⟩ | ⟨index, same⟩
  · rw [same]
    have split := SourceRows.sourceClauses_split parameters owner
    have indexBound := index.isLt
    have length := congrArg List.length split
    simp only [List.length_append] at length
    change (SourceRows.before parameters owner).length + index.val + 1 ≤ _
    unfold equationRows
    omega
  · rw [same, physicalUnitRow_id]
    have bound := index.isLt
    omega

/-- The fourth assertion is the observation/detection unit and is excluded. -/
theorem detectedAssertion_not_allowed (rename : Nat → Fin v) :
    ¬AllowedOriginal (parameters := parameters) rename
      ((equationRows (parameters := parameters)).length + 4) := by
  intro allowed
  have bound := allowedOriginal_bound rename _ allowed
  omega

/-- An emitted controller occurrence has its actual entry owner, not a
caller-provided map to an available clause. -/
theorem emitRow_allowed (rename : Nat → Fin v) (cursor : Cursor parameters)
    (slot : Controller.Native.Variable parameters) (gate : Gate Nat)
    (retained : EntriesBefore (cursor.emitNative slot gate) (controller parameters))
    (index : Fin (gate.clauses (cursor.lastID + 1, true)).length) :
    AllowedOriginal (parameters := parameters) rename
      ((emitRowsExact rename cursor slot gate (retained.trans controller_before_compile)).row index).id := by
  let retainedCompile := retained.trans controller_before_compile
  let owner := emitOwner cursor slot gate retainedCompile
  have ownerBound : owner.val < (controller parameters).entries.length := by
    rcases retained with ⟨suffix, equality⟩
    simp only [equality, Cursor.emitNative, Cursor.emit, Cursor.assign,
      List.length_append, List.length_cons, List.length_nil, owner, emitOwner]
    omega
  have producer := emitOwner_producer cursor slot gate retainedCompile
  have indexBound : index.val < (compile parameters).entries[owner.val].producer.rows.length := by
    rw [producer]
    exact index.isLt
  refine Or.inl ⟨owner, ownerBound, ⟨index.val, indexBound⟩, ?_⟩
  rfl

def mismatchContext (rename : Nat → Fin v) : Clause (Fin v) :=
  [assignmentGuard (mapLiteral rename (sourceRoleMap parameters
      (.internal (.flag .healthy parameters.firstBus)))) true,
   assignmentGuard (mapLiteral rename (sourceRoleMap parameters
      (.internal (.flag .faulty parameters.firstBus)))) false]

def wireCursor : Cursor parameters :=
  (remainingCursor parameters).emitNative (.primary .wire)
    (.and [(remainingCursor parameters).slots (.internal .driver)])

def healthyProductCursor : Cursor parameters :=
  (wireCursor (parameters := parameters)).emitNative (.internal (.firstProduct .healthy))
    (.and [(wireCursor (parameters := parameters)).slots
      (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)),
      (wireCursor (parameters := parameters)).slots (.internal .driver),
      (wireCursor (parameters := parameters)).slots (.internal .remaining)])

def healthyFlagCursor : Cursor parameters :=
  (healthyProductCursor (parameters := parameters)).emitNative
    (.internal (.flag .healthy parameters.firstBus))
    (.not ((healthyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .healthy))))

def faultyProductCursor : Cursor parameters :=
  (healthyFlagCursor (parameters := parameters)).emitNative (.internal (.firstProduct .faulty))
    (.and [(healthyFlagCursor (parameters := parameters)).slots (.primary .wire),
      (healthyFlagCursor (parameters := parameters)).slots (.internal .driver),
      (healthyFlagCursor (parameters := parameters)).slots (.internal .remaining)])

theorem healthyFlag_before_interface : EntriesBefore
    (healthyFlagCursor (parameters := parameters)) (interface parameters) := by
  change EntriesBefore (healthyFlagCursor (parameters := parameters))
    ((faultyProductCursor (parameters := parameters)).emitNative
      (.internal (.flag .faulty parameters.firstBus))
      (.not ((faultyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .faulty)))))
  exact (emitNative_before _ _ _).trans (emitNative_before _ _ _)

theorem healthyProduct_before_compile : EntriesBefore
    (healthyProductCursor (parameters := parameters)) (compile parameters) :=
  (emitNative_before _ _ _).trans (healthyFlag_before_interface.trans interface_before_compile)

def healthyProductRows (rename : Nat → Fin v) :=
  emitRowsExact rename (wireCursor (parameters := parameters))
    (.internal (.firstProduct .healthy))
    (.and [(wireCursor (parameters := parameters)).slots
      (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)),
      (wireCursor (parameters := parameters)).slots (.internal .driver),
      (wireCursor (parameters := parameters)).slots (.internal .remaining)])
    healthyProduct_before_compile

def healthyFlagRows (rename : Nat → Fin v) :=
  emitRowsExact rename (healthyProductCursor (parameters := parameters))
    (.internal (.flag .healthy parameters.firstBus))
    (.not ((healthyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .healthy))))
    (healthyFlag_before_interface.trans interface_before_compile)

/-- This local original-row resolution derives U ∨ P₁. It has no splits and
uses no observations, input valuation, or semantic entailment oracle. -/
def healthyFlagFromTargetAbsent (rename : Nat → Fin v) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((wireCursor (parameters := parameters)).slots
          (.internal (.absent .healthy parameters.firstBus parameters.bridge.target))),
       mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)] 1 := by
  let state := initialState (relabel rename (formula parameters))
  let product := mapLiteral rename ((wireCursor (parameters := parameters)).lastID + 1, true)
  let absent := mapLiteral rename ((wireCursor (parameters := parameters)).slots
    (.internal (.absent .healthy parameters.firstBus parameters.bridge.target)))
  let flag := mapLiteral rename ((healthyProductCursor (parameters := parameters)).lastID + 1, true)
  let left : AvailableSubclause state [negate product, absent] :=
    ofRow ((healthyProductRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 4; decide⟩)
  let right : AvailableSubclause state [product, flag] :=
    retarget (ofRow ((healthyFlagRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 2; decide⟩)) (by
        intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        simp [healthyProductCursor, Cursor.emitNative, Cursor.emit, Cursor.assign,
          Bounded.Producer.rows, Gate.clauses, Rows.mapClause, mapLiteral, product, flag] at member ⊢ <;> aesop)
  let joined := longMerge state product [absent] [flag] left right
  exact ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    longMerge_result _ _ _ _ _ _, longMerge_count _ _ _ _ _ _⟩


theorem faultyProduct_before_compile : EntriesBefore
    (faultyProductCursor (parameters := parameters)) (compile parameters) :=
  (emitNative_before _ _ _).trans interface_before_compile

def faultyProductInputs : List (Literal Nat) :=
  [(healthyFlagCursor (parameters := parameters)).slots (.primary .wire),
   (healthyFlagCursor (parameters := parameters)).slots (.internal .driver),
   (healthyFlagCursor (parameters := parameters)).slots (.internal .remaining)]

def faultyProductRows (rename : Nat → Fin v) :=
  emitRowsExact rename (healthyFlagCursor (parameters := parameters))
    (.internal (.firstProduct .faulty)) (.and (faultyProductInputs (parameters := parameters)))
    faultyProduct_before_compile

def faultyFlagRows (rename : Nat → Fin v) :=
  emitRowsExact rename (faultyProductCursor (parameters := parameters))
    (.internal (.flag .faulty parameters.firstBus))
    (.not ((faultyProductCursor (parameters := parameters)).slots (.internal (.firstProduct .faulty))))
    interface_before_compile

/-- Each of W,D,R is forced by the faulty-zero cofactor using two original
interface rows. The output is a stronger clause, with at most one resolution. -/
def faultyZeroInput (rename : Nat → Fin v) (index : Fin 3) :
    SubclauseProjection (initialState (relabel rename (formula parameters)))
      [mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true),
       mapLiteral rename ((faultyProductInputs (parameters := parameters))[index.val]'(by
         simpa [faultyProductInputs] using index.isLt))] 1 := by
  let state := initialState (relabel rename (formula parameters))
  let product := mapLiteral rename ((healthyFlagCursor (parameters := parameters)).lastID + 1, true)
  let flag := mapLiteral rename ((faultyProductCursor (parameters := parameters)).lastID + 1, true)
  let input := mapLiteral rename ((faultyProductInputs (parameters := parameters))[index.val]'(by
    simpa [faultyProductInputs] using index.isLt))
  let left : AvailableSubclause state [negate product, input] := by
    have row := ofRow ((faultyProductRows (parameters := parameters) rename).row
      ⟨index.val, by change index.val < 4; omega⟩)
    have bound : index.val < (faultyProductInputs (parameters := parameters)).length := by
      simpa [faultyProductInputs] using index.isLt
    simpa [Bounded.Producer.rows, Gate.clauses, List.getElem_append, bound,
      Rows.mapClause, mapLiteral, product, input, state, negate, Std.Sat.Literal.negate] using row
  let right : AvailableSubclause state [product, flag] :=
    retarget (ofRow ((faultyFlagRows (parameters := parameters) rename).row
      ⟨0, by change 0 < 2; decide⟩)) (by
        intro literal member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        simp [faultyProductCursor, Cursor.emitNative, Cursor.emit, Cursor.assign,
          Bounded.Producer.rows, Gate.clauses, Rows.mapClause, mapLiteral, product, flag] at member ⊢ <;> aesop)
  let joined := longMerge state product [input] [flag] left right
  refine ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    retarget (longMerge_result _ _ _ _ _ _) ?_, longMerge_count _ _ _ _ _ _⟩
  intro literal member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  aesop


end Controller.NativeProof.SourceMismatchBranch
