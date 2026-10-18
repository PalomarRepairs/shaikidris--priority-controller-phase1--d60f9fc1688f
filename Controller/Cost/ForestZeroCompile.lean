module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestGreatestZero
public import Mathlib.Data.Vector.Basic

@[expose] public section

/-! Local-coordinate construction for root-local forward rows. A shared dense
source-coordinate table is initialized once. Each original literal occurrence
performs a real indexed table read; a first touch writes its local ID and appends
the original coordinate. Repeated occurrences keep their order and polarity.
The bounds below count these executable array operations and list constructors.
Their fetched-word implementation, source-row traversal and final channel output
are separate refinements, rather than consequences of a serialized list size.
-/
namespace Controller.Cost.ForestZeroCompile
open Controller.CNF

structure Dictionary (ambient : ℕ) where
  slots : Vector ℕ ambient
  coordinates : Array (Fin ambient)

/-- Zero means unseen; positive words encode local index plus one. -/
def empty (ambient : ℕ) : Dictionary ambient := ⟨Vector.replicate ambient 0, #[]⟩

structure Counts where
  reads : ℕ := 0
  writes : ℕ := 0
  appends : ℕ := 0
  literalCons : ℕ := 0
  rowCons : ℕ := 0
  deriving DecidableEq

def Counts.add (left right : Counts) : Counts :=
  ⟨left.reads + right.reads, left.writes + right.writes, left.appends + right.appends,
    left.literalCons + right.literalCons, left.rowCons + right.rowCons⟩

/-- This is an executable lookup/update at the supplied original finite ID;
there is no support sort, association-list scan or ambient-coordinate loop. -/
def touch (state : Dictionary ambient) (coordinate : Fin ambient) : Dictionary ambient × ℕ × Counts :=
  let encoded := state.slots[coordinate.val]
  if encoded = 0 then
    (⟨state.slots.set coordinate.val (state.coordinates.size + 1),
      state.coordinates.push coordinate⟩, state.coordinates.size, ⟨1, 1, 1, 0, 0⟩)
  else (state, encoded - 1, ⟨1, 0, 0, 0, 0⟩)

/-- Each occurrence emits one pair, including repeated literal IDs. -/
def compileClause (state : Dictionary ambient) : Clause (Fin ambient) →
    Dictionary ambient × Clause ℕ × Counts
  | [] => (state, [], {})
  | literal :: rest =>
      let touched := touch state literal.1
      let returned := compileClause touched.1 rest
      (returned.1, (touched.2.1, literal.2) :: returned.2.1,
        (touched.2.2.add returned.2.2).add ⟨0, 0, 0, 1, 0⟩)

/-- Rows and original occurrences are emitted in their supplied order. -/
def compileRows (state : Dictionary ambient) : List (Clause (Fin ambient)) →
    Dictionary ambient × List (Clause ℕ) × Counts
  | [] => (state, [], {})
  | row :: rest =>
      let clause := compileClause state row
      let returned := compileRows clause.1 rest
      (returned.1, clause.2.1 :: returned.2.1,
        (clause.2.2.add returned.2.2).add ⟨0, 0, 0, 0, 1⟩)

/-- Actual shared-coordinate reset traverses only the retained touched array.
Initialization of the ambient table is absent from this per-root operation. -/
def reset (state : Dictionary ambient) : Dictionary ambient :=
  ⟨state.coordinates.foldl (fun slots coordinate => slots.set coordinate.val 0) state.slots, #[]⟩

inductive TouchExecution : Dictionary ambient → Fin ambient → Dictionary ambient → ℕ → Counts → Prop
  | existing (state : Dictionary ambient) (coordinate : Fin ambient)
      (seen : state.slots[coordinate.val] ≠ 0) :
      TouchExecution state coordinate state (state.slots[coordinate.val] - 1) ⟨1, 0, 0, 0, 0⟩
  | fresh (state : Dictionary ambient) (coordinate : Fin ambient)
      (unseen : state.slots[coordinate.val] = 0) :
      TouchExecution state coordinate
        ⟨state.slots.set coordinate.val (state.coordinates.size + 1), state.coordinates.push coordinate⟩
        state.coordinates.size ⟨1, 1, 1, 0, 0⟩

theorem touch_execution (state : Dictionary ambient) (coordinate : Fin ambient) :
    TouchExecution state coordinate (touch state coordinate).1
      (touch state coordinate).2.1 (touch state coordinate).2.2 := by
  by_cases seen : state.slots[coordinate.val] = 0
  · simpa only [touch, ite_eq_left seen] using TouchExecution.fresh state coordinate seen
  · simpa only [touch, ite_eq_right seen] using TouchExecution.existing state coordinate seen

theorem touch_counts (state : Dictionary ambient) (coordinate : Fin ambient) :
    (touch state coordinate).2.2.reads = 1 ∧
      (touch state coordinate).2.2.writes ≤ 1 ∧ (touch state coordinate).2.2.appends ≤ 1 ∧
      (touch state coordinate).2.2.literalCons = 0 ∧ (touch state coordinate).2.2.rowCons = 0 := by
  by_cases unseen : state.slots[coordinate.val] = 0 <;> simp [touch, unseen]

theorem touch_size (state : Dictionary ambient) (coordinate : Fin ambient) :
    state.coordinates.size ≤ (touch state coordinate).1.coordinates.size ∧
      (touch state coordinate).1.coordinates.size ≤ state.coordinates.size + 1 := by
  by_cases unseen : state.slots[coordinate.val] = 0 <;> simp [touch, unseen]

/-- Original polarity/order survives local-index allocation. -/
theorem clause_polarities (state : Dictionary ambient) (row : Clause (Fin ambient)) :
    ((compileClause state row).2.1.map Prod.snd) = row.map Prod.snd := by
  induction row generalizing state with
  | nil => rfl
  | cons literal rest ih =>
      simp only [compileClause, List.map_cons, ih]

/-- Exact executed primitive counts, independently of dictionary contents. -/
theorem clause_counts (state : Dictionary ambient) (row : Clause (Fin ambient)) :
    (compileClause state row).2.2.reads = row.length ∧
      (compileClause state row).2.2.writes ≤ row.length ∧
      (compileClause state row).2.2.appends ≤ row.length ∧
      (compileClause state row).2.2.literalCons = row.length ∧
      (compileClause state row).2.2.rowCons = 0 := by
  induction row generalizing state with
  | nil => simp [compileClause]
  | cons literal rest ih =>
      have first := touch_counts state literal.1
      have tail := ih (touch state literal.1).1
      simp only [compileClause, Counts.add, List.length_cons]
      omega

theorem clause_local_size (state : Dictionary ambient) (row : Clause (Fin ambient)) :
    state.coordinates.size ≤ (compileClause state row).1.coordinates.size ∧
      (compileClause state row).1.coordinates.size ≤ state.coordinates.size + row.length := by
  induction row generalizing state with
  | nil => simp [compileClause]
  | cons literal rest ih =>
      have first := touch_size state literal.1
      have tail := ih (touch state literal.1).1
      simp only [compileClause, List.length_cons]
      omega

def literalCount (rows : List (Clause (Fin ambient))) : ℕ := (rows.map List.length).sum

/-- One table access and one emitted literal constructor per original occurrence;
first-touch writes/appends are bounded by that same occurrence count. -/
theorem rows_counts (state : Dictionary ambient) (rows : List (Clause (Fin ambient))) :
    (compileRows state rows).2.2.reads = literalCount rows ∧
      (compileRows state rows).2.2.writes ≤ literalCount rows ∧
      (compileRows state rows).2.2.appends ≤ literalCount rows ∧
      (compileRows state rows).2.2.literalCons = literalCount rows ∧
      (compileRows state rows).2.2.rowCons = rows.length := by
  induction rows generalizing state with
  | nil => simp [compileRows, literalCount]
  | cons row rest ih =>
      have first := clause_counts state row
      have tail := ih (compileClause state row).1
      simp only [literalCount] at tail
      simp only [compileRows, Counts.add, literalCount, List.map_cons, List.sum_cons,
        List.length_cons]
      omega

theorem rows_local_size (state : Dictionary ambient) (rows : List (Clause (Fin ambient))) :
    state.coordinates.size ≤ (compileRows state rows).1.coordinates.size ∧
      (compileRows state rows).1.coordinates.size ≤ state.coordinates.size + literalCount rows := by
  induction rows generalizing state with
  | nil => simp [compileRows, literalCount]
  | cons row rest ih =>
      have first := clause_local_size state row
      have tail := ih (compileClause state row).1
      simp only [literalCount] at tail
      simp only [compileRows, literalCount, List.map_cons, List.sum_cons]
      omega

theorem rows_shape (state : Dictionary ambient) (rows : List (Clause (Fin ambient))) :
    (compileRows state rows).2.1.map List.length = rows.map List.length := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      have same := congrArg List.length (clause_polarities state row)
      simpa only [compileRows, List.map_cons, List.length_map, ih] using
        congrArg (fun size => size :: rest.map List.length) same


/-- The shared table and local reverse array are exact inverses on positive
entries. This excludes stale IDs from earlier root queries. -/
def Coherent (state : Dictionary ambient) : Prop :=
  ∀ coordinate : Fin ambient, ∀ index : ℕ,
    state.slots[coordinate.val] = index + 1 ↔ state.coordinates[index]? = some coordinate

theorem empty_coherent (ambient : ℕ) : Coherent (empty ambient) := by
  intro coordinate index
  simp [empty]

/-- Both directions of the local-ID correspondence survive an actual first
touch, or the existing-ID path. No support-enumeration certificate is supplied. -/
theorem touch_coherent (state : Dictionary ambient) (valid : Coherent state)
    (coordinate : Fin ambient) : Coherent (touch state coordinate).1 := by
  by_cases unseen : state.slots[coordinate.val] = 0
  · simp only [touch, ite_eq_left unseen]
    intro other index
    by_cases same : coordinate = other
    · subst other
      by_cases last : index = state.coordinates.size
      · subst index; simp only [Vector.getElem_set_self, Array.getElem?_push_size]
      · have impossible : state.coordinates[index]? ≠ some coordinate := by
          intro present
          have encoded := (valid coordinate index).mpr present
          omega
        simp only [Vector.getElem_set_self, Array.getElem?_push, ite_eq_right last]
        constructor
        · intro equality; omega
        · intro present; exact False.elim (impossible present)
    · by_cases last : index = state.coordinates.size
      · subst index
        have impossible : state.slots[other.val] ≠ state.coordinates.size + 1 := by
          intro equality
          have present := (valid other state.coordinates.size).mp equality
          have missing := Array.getElem?_eq_none (xs := state.coordinates) (Nat.le_refl _)
          rw [missing] at present
          contradiction
        have valuesDifferent : coordinate.val ≠ other.val := fun equality => same (Fin.ext equality)
        simp only [Vector.getElem_set_ne coordinate.isLt other.isLt valuesDifferent,
          Array.getElem?_push_size]
        constructor
        · intro equality; exact False.elim (impossible equality)
        · intro equality; exact False.elim (same (Option.some.inj equality))
      · have valuesDifferent : coordinate.val ≠ other.val := fun equality => same (Fin.ext equality)
        simpa only [Vector.getElem_set_ne coordinate.isLt other.isLt valuesDifferent,
          Array.getElem?_push, ite_eq_right last] using valid other index
  · simpa only [touch, ite_eq_right unseen] using valid

/-- The returned ID decodes to the original coordinate in the actual reverse
array, including the fresh append case. -/
theorem touch_coordinate (state : Dictionary ambient) (valid : Coherent state)
    (coordinate : Fin ambient) :
    (touch state coordinate).1.coordinates[(touch state coordinate).2.1]? = some coordinate := by
  by_cases unseen : state.slots[coordinate.val] = 0
  · simp only [touch, ite_eq_left unseen, Array.getElem?_push_size]
  · have encoded : state.slots[coordinate.val] = (state.slots[coordinate.val] - 1) + 1 := by omega
    simpa only [touch, ite_eq_right unseen] using (valid coordinate _).mp encoded

def ExtendsCoordinates (before after : Dictionary ambient) : Prop :=
  ∀ (index : ℕ) (coordinate : Fin ambient), before.coordinates[index]? = some coordinate →
    after.coordinates[index]? = some coordinate

theorem touch_extends (state : Dictionary ambient) (coordinate : Fin ambient) :
    ExtendsCoordinates state (touch state coordinate).1 := by
  intro index other present
  by_cases unseen : state.slots[coordinate.val] = 0
  · obtain ⟨bounded, _⟩ := Array.getElem?_eq_some_iff.mp present
    have different : index ≠ state.coordinates.size := Nat.ne_of_lt bounded
    simp only [touch, ite_eq_left unseen, Array.getElem?_push, ite_eq_right different, present]
  · simpa only [touch, ite_eq_right unseen] using present

theorem clause_dictionary (state : Dictionary ambient) (valid : Coherent state)
    (row : Clause (Fin ambient)) :
    Coherent (compileClause state row).1 ∧ ExtendsCoordinates state (compileClause state row).1 := by
  induction row generalizing state with
  | nil => exact ⟨valid, fun _ _ same => same⟩
  | cons literal rest ih =>
      have first := touch_coherent state valid literal.1
      obtain ⟨tailValid, tailFrame⟩ := ih (touch state literal.1).1 first
      exact ⟨tailValid, fun index coordinate present =>
        tailFrame index coordinate (touch_extends state literal.1 index coordinate present)⟩

/-- Every returned occurrence has its own source-coordinate and polarity
agreement in the final dictionary. Duplicates remain separate list positions. -/
theorem clause_correspondence (state : Dictionary ambient) (valid : Coherent state)
    (row : Clause (Fin ambient)) :
    List.Forall₂ (fun output original =>
      (compileClause state row).1.coordinates[output.1]? = some original.1 ∧ output.2 = original.2)
      (compileClause state row).2.1 row := by
  induction row generalizing state with
  | nil => exact .nil
  | cons literal rest ih =>
      have firstValid := touch_coherent state valid literal.1
      have firstSame := touch_coordinate state valid literal.1
      have tail := ih (touch state literal.1).1 firstValid
      have frame := (clause_dictionary (touch state literal.1).1 firstValid rest).2
      exact .cons ⟨frame _ _ firstSame, rfl⟩ tail

theorem rows_dictionary (state : Dictionary ambient) (valid : Coherent state)
    (rows : List (Clause (Fin ambient))) :
    Coherent (compileRows state rows).1 ∧ ExtendsCoordinates state (compileRows state rows).1 := by
  induction rows generalizing state with
  | nil => exact ⟨valid, fun _ _ same => same⟩
  | cons row rest ih =>
      obtain ⟨firstValid, firstFrame⟩ := clause_dictionary state valid row
      obtain ⟨tailValid, tailFrame⟩ := ih (compileClause state row).1 firstValid
      exact ⟨tailValid, fun index coordinate present => tailFrame _ _ (firstFrame _ _ present)⟩

theorem rows_correspondence (state : Dictionary ambient) (valid : Coherent state)
    (rows : List (Clause (Fin ambient))) :
    List.Forall₂ (fun output original =>
      List.Forall₂ (fun produced source =>
        (compileRows state rows).1.coordinates[produced.1]? = some source.1 ∧ produced.2 = source.2)
        output original) (compileRows state rows).2.1 rows := by
  induction rows generalizing state with
  | nil => exact .nil
  | cons row rest ih =>
      have firstValid := (clause_dictionary state valid row).1
      have firstSame := clause_correspondence state valid row
      have frame := (rows_dictionary (compileClause state row).1 firstValid rest).2
      have lifted : List.Forall₂ (fun produced source =>
          (compileRows state (row :: rest)).1.coordinates[produced.1]? = some source.1 ∧
            produced.2 = source.2) (compileClause state row).2.1 row :=
        List.Forall₂.imp (fun _ _ pair => ⟨frame _ _ pair.1, pair.2⟩) firstSame
      exact .cons lifted (ih (compileClause state row).1 firstValid)


def localAssignment (state : Dictionary ambient) (original : Fin ambient → Bool) (index : ℕ) : Bool :=
  match state.coordinates[index]? with | some coordinate => original coordinate | none => false

def sourceAssignment (state : Dictionary ambient) (localValues : ℕ → Bool) (coordinate : Fin ambient) : Bool :=
  if state.slots[coordinate.val] = 0 then false else localValues (state.slots[coordinate.val] - 1)

private theorem clauses_equivalent {α β : Type} (left : α → Bool) (right : β → Bool)
    {output : Clause α} {original : Clause β}
    (related : List.Forall₂ (fun produced source =>
      LiteralHolds left produced ↔ LiteralHolds right source) output original) :
    ClauseHolds left output ↔ ClauseHolds right original := by
  induction related with
  | nil => simp [ClauseHolds]
  | cons first rest ih => simpa only [clauseHolds_cons] using or_congr first ih

private theorem formulas_equivalent {α β : Type} (left : α → Bool) (right : β → Bool)
    {output : List (Clause α)} {original : List (Clause β)}
    (related : List.Forall₂ (fun produced source =>
      ClauseHolds left produced ↔ ClauseHolds right source) output original) :
    Satisfies left (ofClauses output) ↔ Satisfies right (ofClauses original) := by
  simp only [satisfies_ofClauses]
  induction related with
  | nil => simp
  | cons first rest ih => simpa only [List.forall_mem_cons] using and_congr first ih

/-- Every original model produces a model of the actually emitted local rows. -/
theorem rows_forward_model (state : Dictionary ambient) (valid : Coherent state)
    (rows : List (Clause (Fin ambient))) (assignment : Fin ambient → Bool) :
    Satisfies (localAssignment (compileRows state rows).1 assignment)
      (ofClauses (compileRows state rows).2.1) ↔ Satisfies assignment (ofClauses rows) := by
  apply formulas_equivalent
  apply List.Forall₂.imp _ (rows_correspondence state valid rows)
  intro produced source related
  apply clauses_equivalent
  apply List.Forall₂.imp _ related
  intro output original same
  simp only [LiteralHolds, localAssignment, same.1, same.2]

/-- The reverse map is derived from the checked local allocation table, rather
than supplied as a semantic equivalence assertion. -/
theorem rows_reverse_model (state : Dictionary ambient) (valid : Coherent state)
    (rows : List (Clause (Fin ambient))) (assignment : ℕ → Bool) :
    Satisfies assignment (ofClauses (compileRows state rows).2.1) ↔
      Satisfies (sourceAssignment (compileRows state rows).1 assignment) (ofClauses rows) := by
  have coherent := (rows_dictionary state valid rows).1
  apply formulas_equivalent
  apply List.Forall₂.imp _ (rows_correspondence state valid rows)
  intro produced source related
  apply clauses_equivalent
  apply List.Forall₂.imp _ related
  intro output original same
  have encoded := (coherent original.1 output.1).mpr same.1
  simp only [LiteralHolds, sourceAssignment, encoded, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, same.2]

/-- Existence and nonexistence are transported in both directions through the
executed first-touch allocator. -/
theorem rows_satisfiable_iff (rows : List (Clause (Fin ambient))) :
    Satisfiable (ofClauses (compileRows (empty ambient) rows).2.1) ↔
      Satisfiable (ofClauses rows) := by
  constructor
  · rintro ⟨assignment, model⟩
    exact ⟨sourceAssignment (compileRows (empty ambient) rows).1 assignment,
      (rows_reverse_model _ (empty_coherent ambient) rows assignment).mp model⟩
  · rintro ⟨assignment, model⟩
    exact ⟨localAssignment (compileRows (empty ambient) rows).1 assignment,
      (rows_forward_model _ (empty_coherent ambient) rows assignment).mpr model⟩

def BoundedRows (limit : ℕ) (rows : List (Clause ℕ)) : Prop :=
  ∀ row ∈ rows, ∀ literal ∈ row, literal.1 < limit

private theorem clause_bounds (state : Dictionary ambient) {produced : Clause ℕ}
    {original : Clause (Fin ambient)}
    (related : List.Forall₂ (fun output source =>
      state.coordinates[output.1]? = some source.1 ∧ output.2 = source.2) produced original) :
    ∀ literal ∈ produced, literal.1 < state.coordinates.size := by
  induction related with
  | nil => simp
  | @cons first source rest originals same related ih =>
      intro literal present
      rcases List.mem_cons.mp present with equality | tail
      · subst literal
        exact (Array.getElem?_eq_some_iff.mp same.1).choose
      · exact ih literal tail

private theorem related_rows_bounds (state : Dictionary ambient)
    {produced : List (Clause ℕ)} {original : List (Clause (Fin ambient))}
    (related : List.Forall₂ (fun output source =>
      List.Forall₂ (fun out lit => state.coordinates[out.1]? = some lit.1 ∧ out.2 = lit.2)
        output source) produced original) : BoundedRows state.coordinates.size produced := by
  induction related with
  | nil => simp [BoundedRows]
  | @cons first source rest originals same related ih =>
      intro row present
      rcases List.mem_cons.mp present with equality | tail
      · subst row; exact clause_bounds _ same
      · exact ih row tail

/-- All emitted bounds derive from the final allocated coordinate array. -/
theorem rows_bounds (state : Dictionary ambient) (valid : Coherent state)
    (rows : List (Clause (Fin ambient))) :
    BoundedRows (compileRows state rows).1.coordinates.size (compileRows state rows).2.1 :=
  related_rows_bounds _ (rows_correspondence state valid rows)

/-- Bounded conversion preserves each original literal occurrence. -/
def finiteClause (row : Clause ℕ) (bound : ∀ literal ∈ row, literal.1 < limit) : Clause (Fin limit) :=
  row.attach.map fun literal => (⟨literal.val.1, bound literal.val literal.property⟩, literal.val.2)

def finiteRows (rows : List (Clause ℕ)) (bound : BoundedRows limit rows) : FiniteFormula limit :=
  ofClauses (rows.attach.map fun row => finiteClause row.val (bound row.val row.property))

private theorem finiteClause_model (row : Clause ℕ)
    (bound : ∀ literal ∈ row, literal.1 < limit) (assignment : ℕ → Bool) :
    ClauseHolds (restrictNat assignment) (finiteClause row bound) ↔ ClauseHolds assignment row := by
  constructor
  · rintro ⟨literal, member, holds⟩
    obtain ⟨original, present, equality⟩ := List.mem_map.mp member
    subst literal
    exact ⟨original.val, original.property, by simpa only [LiteralHolds, restrictNat] using holds⟩
  · rintro ⟨literal, present, holds⟩
    let original : {value // value ∈ row} := ⟨literal, present⟩
    refine ⟨(⟨literal.1, bound literal present⟩, literal.2), ?_, holds⟩
    exact List.mem_map.mpr ⟨original, List.mem_attach _ _, rfl⟩

/-- Finite-ID conversion changes only the variable type; row and literal
occurrence multiplicities are retained. -/
theorem finiteRows_model (rows : List (Clause ℕ)) (bound : BoundedRows limit rows)
    (assignment : ℕ → Bool) :
    Satisfies (restrictNat assignment) (finiteRows rows bound) ↔
      Satisfies assignment (ofClauses rows) := by
  simp only [finiteRows, satisfies_ofClauses]
  constructor
  · intro model row member
    apply (finiteClause_model row (bound row member) assignment).mp
    exact model _ (List.mem_map.mpr ⟨⟨row, member⟩, List.mem_attach _ _, rfl⟩)
  · intro model row member
    obtain ⟨original, present, equality⟩ := List.mem_map.mp member
    subst row
    exact (finiteClause_model original.val (bound _ original.property) assignment).mpr
      (model _ original.property)

/-- A finite local model extends to every natural ID; only IDs carrying an
allocation-derived bound occur in the emitted rows. -/
theorem finiteRows_satisfiable (rows : List (Clause ℕ)) (bound : BoundedRows limit rows) :
    Satisfiable (finiteRows rows bound) ↔ Satisfiable (ofClauses rows) := by
  constructor
  · rintro ⟨assignment, model⟩
    refine ⟨extendNat assignment, ?_⟩
    apply (finiteRows_model rows bound (extendNat assignment)).mp
    simpa only [restrictNat_extendNat] using model
  · rintro ⟨assignment, model⟩
    exact ⟨restrictNat assignment, (finiteRows_model rows bound assignment).mpr model⟩

/-- The production compiler's finite output uses exactly its appended local
coordinates. No ambient-variable scan or sorting pass is inserted here. -/
def compileFinite (rows : List (Clause (Fin ambient))) :
    Σ limit : ℕ, FiniteFormula limit :=
  let result := compileRows (empty ambient) rows
  ⟨result.1.coordinates.size, finiteRows result.2.1 (rows_bounds _ (empty_coherent ambient) rows)⟩

/-- The executed first-touch compiler and its bounded Fin conversion preserve
existence of models in both directions. No equivalence oracle is an input. -/
theorem compileFinite_satisfiable (rows : List (Clause (Fin ambient))) :
    Satisfiable (compileFinite rows).2 ↔ Satisfiable (ofClauses rows) := by
  exact (finiteRows_satisfiable _ (rows_bounds _ (empty_coherent ambient) rows)).trans
    (rows_satisfiable_iff rows)

end Controller.Cost.ForestZeroCompile
