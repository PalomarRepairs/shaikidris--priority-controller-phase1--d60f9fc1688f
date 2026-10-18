module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceMismatchHandles

@[expose] public section

/-! Original occurrence provenance for balanced source conjunction witnesses.
The predicates retain row identifiers through checked prefixes. -/
namespace Controller.NativeProof.SourceFoldProvenance
open Controller.CNF Controller.Resolution Controller.Resolution.Cases
open Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceMismatchHandles Controller.NativeProof.SourceMismatchBranch
open Controller.NativeProof.SourceFoldOwners
variable {v : Nat} {state initial : State v}

/-- A getter commutes with transport along equality of its index. -/
theorem getter_transport {ι : Sort _} {family : ι → Sort _}
    (getter : ∀ index, family index → Nat) {before after : ι} (equal : before = after)
    (value : family before) : getter after (equal ▸ value) = getter before value := by
  subst after
  rfl

/-- The corresponding predicate transport changes no witness data. -/
theorem predicate_transport {ι : Sort _} {family : ι → Sort _}
    (predicate : ∀ index, family index → Prop) {before after : ι} (equal : before = after)
    (value : family before) : predicate after (equal ▸ value) ↔ predicate before value := by
  subst after
  rfl

theorem getter_transport_apply {ι : Sort _} {argument : ι → Sort _}
    {family : ι → Sort _} (getter : ∀ index, family index → Nat)
    {before after : ι} (equal : before = after)
    (function : argument before → family before) (input : argument after) :
    getter after ((equal ▸ function) input) = getter before (function (equal.symm ▸ input)) := by
  subst after
  rfl

theorem getter_transport_apply_two {ι : Sort _} {argument₁ argument₂ : ι → Sort _}
    {family : ι → Sort _} (getter : ∀ index, family index → Nat)
    {before after : ι} (equal : before = after)
    (function : argument₁ before → argument₂ before → family before)
    (one : argument₁ after) (two : argument₂ after) :
    getter after ((equal ▸ function) one two) =
      getter before (function (equal.symm ▸ one) (equal.symm ▸ two)) := by
  subst after
  rfl

/-- All three binary equations come from permitted original occurrences. -/
def BinaryOriginals (allowed : Nat → Prop) {left right output : Literal (Fin v)}
    (rows : BinaryAndRows state left right output) : Prop :=
  allowed rows.leftRow.id ∧ allowed rows.rightRow.id ∧ allowed rows.longRow.id

def TreeOriginals (allowed : Nat → Prop) {output : Literal (Fin v)}
    {inputs : List (Literal (Fin v))} : AndTree state output inputs → Prop
  | .leaf _ => True
  | .node left right _ rows =>
      TreeOriginals allowed left ∧ TreeOriginals allowed right ∧ BinaryOriginals allowed rows

theorem binaryOriginals_afterTrace (allowed : Nat → Prop)
    (rows : BinaryAndRows state left right output) (original : BinaryOriginals allowed rows)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    BinaryOriginals allowed (rows.afterTrace next steps checked) := original

theorem treeOriginals_afterTrace (allowed : Nat → Prop) (tree : AndTree state output inputs)
    (original : TreeOriginals allowed tree) (next : State v) (steps : List (Step v))
    (checked : runSteps state steps = some next) :
    TreeOriginals allowed (tree.afterTrace next steps checked) := by
  induction tree with
  | leaf => trivial
  | node left right output rows one two =>
      exact ⟨one original.1, two original.2.1,
        binaryOriginals_afterTrace allowed rows original.2.2 next steps checked⟩

/-- A carried stronger result remains attributable after appending a trace. -/
theorem resultOrigin_append_right (originalCount : Nat) (allowed : Nat → Prop)
    (first second : List (Step v)) (id : Nat)
    (origin : ResultOrigin originalCount allowed first id) :
    ResultOrigin originalCount allowed (first ++ second) id := by
  rcases origin with original | ⟨earlier, member, equal, fresh⟩
  · exact Or.inl original
  · exact Or.inr ⟨earlier, List.mem_append_left second member, equal, fresh⟩

theorem resultOrigin_append_left (originalCount : Nat) (allowed : Nat → Prop)
    (first second : List (Step v)) (id : Nat)
    (origin : ResultOrigin originalCount allowed second id) :
    ResultOrigin originalCount allowed (first ++ second) id := by
  rcases origin with original | ⟨earlier, member, equal, fresh⟩
  · exact Or.inl original
  · exact Or.inr ⟨earlier, List.mem_append_right first member, equal, fresh⟩

/-- The actual merge either reuses one input ID or emits its fresh resolution
row. A missing pivot preserves the stronger premise's existing provenance. -/
theorem merge_result_origin (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (current : State v)
    (leftId rightId : Nat) (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (one : allowed leftId) (two : ResultOrigin originalCount allowed priorSteps rightId)
    (bound : originalCount ≤ current.lastId) :
    ResultOrigin originalCount allowed
      (priorSteps ++ (merge current leftId rightId pivot left right).steps)
      (merge current leftId rightId pivot left right).rowId := by
  unfold merge
  split
  · exact Or.inl one
  · split
    · exact resultOrigin_append_right originalCount allowed priorSteps [] rightId two
    · apply Or.inr
      refine ⟨RUP.resolutionStep current leftId rightId pivot left right, ?_, rfl, ?_⟩
      · simp
      · change originalCount < current.lastId + 1
        omega

/-- The owner is computed from the actual cursor prefix and allocator index.
Clause transport changes only the presence proof, retaining the original ID. -/
def foldRowsExact {parameters : Parameters} (rename : Nat → Fin v)
    (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (Literal Nat))
    (retained : EntriesBefore (cursor.foldNative slot junction inputs) (compile parameters)) :
    RowSupply (initialState (relabel rename (formula parameters))) rename
      (SourceSerialFold.allocate junction cursor.lastID inputs).producers := by
  intro index
  let owner := SourceFoldOwners.foldOwner cursor (compile parameters) slot junction inputs retained index
  have producer : (compile parameters).entries[owner.val].producer =
      (SourceSerialFold.allocate junction cursor.lastID inputs).producers[index.val] :=
    foldOwner_producer cursor (compile parameters) slot junction inputs retained index
  refine ⟨?_⟩
  intro rowIndex
  have rowBound : rowIndex.val < (compile parameters).entries[owner.val].producer.rows.length := by
    rw [producer]
    exact rowIndex.isLt
  let original := ownedRow rename owner ⟨rowIndex.val, rowBound⟩
  refine ⟨original.id, ?_, original.bound⟩
  simpa only [producer] using original.present

/-- Every supplied row keeps its permitted occurrence identity. -/
def SupplyOriginals (allowed : Nat → Prop) {rename : Nat → Fin v}
    {producers : List (Bounded.Producer Nat)} (supply : RowSupply state rename producers) : Prop :=
  ∀ owner index, allowed ((supply owner).row index).id

/-- Original support is established by the real controller stage prefix. -/
theorem foldRowsExact_allowed {parameters : Parameters} (rename : Nat → Fin v)
    (cursor : Cursor parameters) (slot : Controller.Native.Variable parameters)
    (junction : Bounded.Junction) (inputs : List (Literal Nat))
    (retained : EntriesBefore (cursor.foldNative slot junction inputs) (controller parameters)) :
    SupplyOriginals (AllowedOriginal (parameters := parameters) rename)
      (foldRowsExact rename cursor slot junction inputs
        (retained.trans controller_before_compile)) := by
  intro index rowIndex
  let retainedCompile := retained.trans controller_before_compile
  let owner := SourceFoldOwners.foldOwner cursor (compile parameters) slot junction inputs retainedCompile index
  have ownerBound : owner.val < (controller parameters).entries.length := by
    rcases retained with ⟨suffix, equality⟩
    simp only [equality, Cursor.foldNative, Cursor.assign, List.length_append,
      List.length_map, List.length_zipIdx, owner, SourceFoldOwners.foldOwner]
    have indexBound := index.isLt
    omega
  have producer : (compile parameters).entries[owner.val].producer =
      (SourceSerialFold.allocate junction cursor.lastID inputs).producers[index.val] :=
    foldOwner_producer cursor (compile parameters) slot junction inputs retainedCompile index
  have rowBound : rowIndex.val < (compile parameters).entries[owner.val].producer.rows.length := by
    rw [producer]
    exact rowIndex.isLt
  exact Or.inl ⟨owner, ownerBound, ⟨rowIndex.val, rowBound⟩, rfl⟩

def ForestOriginals (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)} : RawForest state rename handles leaves → Prop
  | .nil => True
  | .cons _ _ tree rest => TreeOriginals allowed tree ∧ ForestOriginals allowed rest

@[simp] theorem treeOriginals_cast_inputs (allowed : Nat → Prop)
    {output : Literal (Fin v)} {before after : List (Literal (Fin v))}
    (equal : before = after) (tree : AndTree state output before) :
    TreeOriginals allowed (Eq.mp (congrArg (AndTree state output) equal) tree) ↔ TreeOriginals allowed tree := by
  subst after
  rfl

@[simp] theorem treeOriginals_cast_output (allowed : Nat → Prop)
    {before after : Literal (Fin v)} {inputs : List (Literal (Fin v))}
    (equal : before = after) (tree : AndTree state before inputs) :
    TreeOriginals allowed (Eq.mp (congrArg (fun output => AndTree state output inputs) equal) tree) ↔
      TreeOriginals allowed tree := by
  subst after
  rfl

@[simp] theorem forestOriginals_cast_leaves (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles before after : List (Literal Nat)} (equal : before = after)
    (forest : RawForest state rename handles before) :
    ForestOriginals allowed (Eq.mp (congrArg (RawForest state rename handles) equal) forest) ↔
      ForestOriginals allowed forest := by
  subst after
  rfl

@[simp] theorem forestOriginals_cast_handles (allowed : Nat → Prop) {rename : Nat → Fin v}
    {before after leaves : List (Literal Nat)} (equal : before = after)
    (forest : RawForest state rename before leaves) :
    ForestOriginals allowed (Eq.mp (congrArg (fun handles => RawForest state rename handles leaves) equal) forest) ↔
      ForestOriginals allowed forest := by
  subst after
  rfl

@[simp] theorem treeOriginals_mpr_inputs (allowed : Nat → Prop)
    {output : Literal (Fin v)} {before after : List (Literal (Fin v))}
    (equal : before = after) (tree : AndTree state output after) :
    TreeOriginals allowed (Eq.mpr (congrArg (AndTree state output) equal) tree) ↔ TreeOriginals allowed tree := by
  subst after
  rfl

@[simp] theorem treeOriginals_mpr_output (allowed : Nat → Prop)
    {before after : Literal (Fin v)} {inputs : List (Literal (Fin v))}
    (equal : before = after) (tree : AndTree state after inputs) :
    TreeOriginals allowed (Eq.mpr (congrArg (fun output => AndTree state output inputs) equal) tree) ↔
      TreeOriginals allowed tree := by
  subst after
  rfl

@[simp] theorem forestOriginals_mpr_leaves (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles before after : List (Literal Nat)} (equal : before = after)
    (forest : RawForest state rename handles after) :
    ForestOriginals allowed (Eq.mpr (congrArg (RawForest state rename handles) equal) forest) ↔
      ForestOriginals allowed forest := by
  subst after
  rfl

@[simp] theorem forestOriginals_mpr_handles (allowed : Nat → Prop) {rename : Nat → Fin v}
    {before after leaves : List (Literal Nat)} (equal : before = after)
    (forest : RawForest state rename after leaves) :
    ForestOriginals allowed (Eq.mpr (congrArg (fun handles => RawForest state rename handles leaves) equal) forest) ↔
      ForestOriginals allowed forest := by
  subst after
  rfl

/-- Transport between definitionally equal indexed witness types retains the
original identifiers, regardless of the proof chosen for the type equality. -/
@[simp] theorem treeOriginals_mp_self (allowed : Nat → Prop)
    {output : Literal (Fin v)} {inputs : List (Literal (Fin v))}
    (equal : AndTree state output inputs = AndTree state output inputs)
    (tree : AndTree state output inputs) :
    TreeOriginals allowed (Eq.mp equal tree) ↔ TreeOriginals allowed tree := by
  rfl

@[simp] theorem treeOriginals_mpr_self (allowed : Nat → Prop)
    {output : Literal (Fin v)} {inputs : List (Literal (Fin v))}
    (equal : AndTree state output inputs = AndTree state output inputs)
    (tree : AndTree state output inputs) :
    TreeOriginals allowed (Eq.mpr equal tree) ↔ TreeOriginals allowed tree := by
  rfl

@[simp] theorem forestOriginals_mp_self (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)}
    (equal : RawForest state rename handles leaves = RawForest state rename handles leaves)
    (forest : RawForest state rename handles leaves) :
    ForestOriginals allowed (Eq.mp equal forest) ↔ ForestOriginals allowed forest := by
  rfl

@[simp] theorem forestOriginals_mpr_self (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)}
    (equal : RawForest state rename handles leaves = RawForest state rename handles leaves)
    (forest : RawForest state rename handles leaves) :
    ForestOriginals allowed (Eq.mpr equal forest) ↔ ForestOriginals allowed forest := by
  rfl

/-- Whole witness transport is independent of the equality proof. Both
indices are substituted before the retained occurrence predicate is reduced. -/
theorem treeOriginals_mp_indices (allowed : Nat → Prop)
    {beforeOutput afterOutput : Literal (Fin v)}
    {beforeInputs afterInputs : List (Literal (Fin v))}
    (outputEqual : beforeOutput = afterOutput) (inputsEqual : beforeInputs = afterInputs)
    (typeEqual : AndTree state beforeOutput beforeInputs = AndTree state afterOutput afterInputs)
    (tree : AndTree state beforeOutput beforeInputs) :
    TreeOriginals allowed (Eq.mp typeEqual tree) ↔ TreeOriginals allowed tree := by
  subst afterOutput
  subst afterInputs
  rfl

theorem treeOriginals_mpr_indices (allowed : Nat → Prop)
    {beforeOutput afterOutput : Literal (Fin v)}
    {beforeInputs afterInputs : List (Literal (Fin v))}
    (outputEqual : beforeOutput = afterOutput) (inputsEqual : beforeInputs = afterInputs)
    (typeEqual : AndTree state beforeOutput beforeInputs = AndTree state afterOutput afterInputs)
    (tree : AndTree state afterOutput afterInputs) :
    TreeOriginals allowed (Eq.mpr typeEqual tree) ↔ TreeOriginals allowed tree := by
  subst afterOutput
  subst afterInputs
  rfl

theorem forestOriginals_mp_indices (allowed : Nat → Prop) {rename : Nat → Fin v}
    {beforeHandles afterHandles beforeLeaves afterLeaves : List (Literal Nat)}
    (handlesEqual : beforeHandles = afterHandles) (leavesEqual : beforeLeaves = afterLeaves)
    (typeEqual : RawForest state rename beforeHandles beforeLeaves =
      RawForest state rename afterHandles afterLeaves)
    (forest : RawForest state rename beforeHandles beforeLeaves) :
    ForestOriginals allowed (Eq.mp typeEqual forest) ↔ ForestOriginals allowed forest := by
  subst afterHandles
  subst afterLeaves
  rfl

theorem forestOriginals_mpr_indices (allowed : Nat → Prop) {rename : Nat → Fin v}
    {beforeHandles afterHandles beforeLeaves afterLeaves : List (Literal Nat)}
    (handlesEqual : beforeHandles = afterHandles) (leavesEqual : beforeLeaves = afterLeaves)
    (typeEqual : RawForest state rename beforeHandles beforeLeaves =
      RawForest state rename afterHandles afterLeaves)
    (forest : RawForest state rename afterHandles afterLeaves) :
    ForestOriginals allowed (Eq.mpr typeEqual forest) ↔ ForestOriginals allowed forest := by
  subst afterHandles
  subst afterLeaves
  rfl

theorem initialForest_originals (allowed : Nat → Prop) (rename : Nat → Fin v)
    (inputs : List (Literal Nat)) : ForestOriginals allowed (initialForest (state := state) rename inputs) := by
  induction inputs with
  | nil => trivial
  | cons input rest ih => exact ⟨True.intro, ih⟩

theorem binaryRows_originals (allowed : Nat → Prop) (rename : Nat → Fin v)
    (left right output : Literal Nat)
    (rows : OriginalRows state rename (⟨output, .and [left, right]⟩ : Bounded.Producer Nat))
    (original : ∀ index, allowed (rows.row index).id) :
    BinaryOriginals allowed (binaryRows left right output rows) :=
  ⟨original _, original _, original _⟩

/-- Each local descent uses an original child link and the carried stronger
prefix. Both actual merges preserve causal support, including skipped merges. -/
theorem descendCell_supported (initial current : State v) (priorSteps : List (Step v))
    (checked : runSteps initial priorSteps = some current)
    (root left right output : Literal (Fin v)) (rows : BinaryAndRows initial left right output)
    (prefixRow : AvailableSubclause current [negate root, output])
    (originalCount : Nat) (allowed : Nat → Prop)
    (original : BinaryOriginals allowed rows)
    (supported : SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (origin : ResultOrigin originalCount allowed priorSteps prefixRow.row.id) :
    SourceBusSchedule.TraceOriginalSupport originalCount allowed
      (priorSteps ++ (descendCell initial current priorSteps checked root left right output rows prefixRow).steps) := by
  let leftLink := FoldProjection.afterTrace (ofRow rows.leftRow) current priorSteps checked
  let first := implicationMerge current [] root output left leftLink prefixRow
  have firstRun := implicationMerge_run current [] root output left leftLink prefixRow
  let nextPrefix := FoldProjection.afterTrace prefixRow first.state first.steps firstRun
  have nextChecked : runSteps initial (priorSteps ++ first.steps) = some first.state := by
    simp only [runSteps_append, checked, Option.bind_some]
    exact firstRun
  let rightLink := FoldProjection.afterTrace (ofRow rows.rightRow) first.state
    (priorSteps ++ first.steps) nextChecked
  let second := implicationMerge first.state [] root output right rightLink nextPrefix
  have one : SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ first.steps) :=
    appendMerge_supported originalCount allowed priorSteps current
      leftLink.row.id prefixRow.row.id output leftLink.clause prefixRow.clause
      supported originalBound original.1 origin prefixRow.row.bound
  have two : SourceBusSchedule.TraceOriginalSupport originalCount allowed
      ((priorSteps ++ first.steps) ++ second.steps) :=
    appendMerge_supported originalCount allowed (priorSteps ++ first.steps) first.state
      rightLink.row.id nextPrefix.row.id output rightLink.clause nextPrefix.clause
      one originalBound original.2.1
      (resultOrigin_append_right originalCount allowed priorSteps first.steps prefixRow.row.id origin)
      nextPrefix.row.bound
  simpa only [descendCell, List.append_assoc, leftLink, first, nextPrefix, rightLink,
    second] using two

/-- Every local descent result retains its concrete original or emitted ID. -/
theorem descendCell_origins (initial current : State v) (priorSteps : List (Step v))
    (checked : runSteps initial priorSteps = some current)
    (root left right output : Literal (Fin v)) (rows : BinaryAndRows initial left right output)
    (prefixRow : AvailableSubclause current [negate root, output])
    (originalCount : Nat) (allowed : Nat → Prop)
    (original : BinaryOriginals allowed rows)
    (origin : ResultOrigin originalCount allowed priorSteps prefixRow.row.id)
    (bound : originalCount ≤ current.lastId) :
    ∀ input member, ResultOrigin originalCount allowed
      (priorSteps ++ (descendCell initial current priorSteps checked root left right output rows prefixRow).steps)
      ((descendCell initial current priorSteps checked root left right output rows prefixRow).results input member).row.id := by
  let leftLink := FoldProjection.afterTrace (ofRow rows.leftRow) current priorSteps checked
  let first := implicationMerge current [] root output left leftLink prefixRow
  have firstRun := implicationMerge_run current [] root output left leftLink prefixRow
  let nextPrefix := FoldProjection.afterTrace prefixRow first.state first.steps firstRun
  have nextChecked : runSteps initial (priorSteps ++ first.steps) = some first.state := by
    simp only [runSteps_append, checked, Option.bind_some]
    exact firstRun
  let rightLink := FoldProjection.afterTrace (ofRow rows.rightRow) first.state
    (priorSteps ++ first.steps) nextChecked
  let second := implicationMerge first.state [] root output right rightLink nextPrefix
  have firstOrigin : ResultOrigin originalCount allowed (priorSteps ++ first.steps) first.rowId :=
    merge_result_origin originalCount allowed priorSteps current leftLink.row.id
      prefixRow.row.id output leftLink.clause prefixRow.clause original.1 origin bound
  have secondOrigin : ResultOrigin originalCount allowed
      ((priorSteps ++ first.steps) ++ second.steps) second.rowId :=
    merge_result_origin originalCount allowed (priorSteps ++ first.steps) first.state
      rightLink.row.id nextPrefix.row.id output rightLink.clause nextPrefix.clause original.2.1
      (resultOrigin_append_right originalCount allowed priorSteps first.steps prefixRow.row.id origin)
      (bound.trans (runSteps_lastId_le firstRun))
  intro input member
  by_cases same : input = left
  · subst input
    have carried := resultOrigin_append_right originalCount allowed
      (priorSteps ++ first.steps) second.steps first.rowId firstOrigin
    dsimp only [descendCell]
    rw [dite_eq_left rfl]
    simpa only [descendCell, dite_eq_left rfl, ite_eq_left rfl, FoldProjection.afterTrace, implicationMerge_result, getter_transport, getter_transport_apply, getter_transport_apply_two, dite_apply, ite_apply, apply_dite, apply_ite, eq_self_iff_true, dite_true, ite_true,
      List.append_assoc, leftLink, first, nextPrefix, rightLink, second] using carried
  · have rightSame : input = right := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, same, false_or] using member
    subst input
    dsimp only [descendCell]
    rw [dite_eq_right same]
    simpa only [descendCell, dite_eq_right same, ite_eq_right same, implicationMerge_result, getter_transport, getter_transport_apply, getter_transport_apply_two, dite_apply, ite_apply, apply_dite, apply_ite, eq_self_iff_true, dite_true, ite_true,
      List.append_assoc, leftLink, first, nextPrefix, rightLink, second] using secondOrigin

/-- The invariant follows the actual runtime traversal, with one induction
hypothesis per child. It certifies both the causal trace and every stronger
returned implication; it does not insert weakened target clauses. -/
theorem projectTreeInputsBelow_supported (tree : AndTree initial output inputs)
    (current : State v) (priorSteps : List (Step v))
    (checked : runSteps initial priorSteps = some current)
    (root : Literal (Fin v)) (prefixRow : AvailableSubclause current [negate root, output])
    (originalCount : Nat) (allowed : Nat → Prop)
    (treeOriginal : TreeOriginals allowed tree)
    (supported : SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (origin : ResultOrigin originalCount allowed priorSteps prefixRow.row.id)
    (bound : originalCount ≤ current.lastId) :
    let actual := projectTreeInputsBelow tree current priorSteps checked root prefixRow
    SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ actual.steps) ∧
      ∀ input member, ResultOrigin originalCount allowed (priorSteps ++ actual.steps)
        (actual.results input member).row.id := by
  cases tree with
  | leaf input =>
    refine ⟨?_, ?_⟩
    · simpa only [projectTreeInputsBelow, appendTreeInputProjection, List.append_nil] using supported
    · intro leaf member
      have same := List.mem_singleton.mp member
      subst leaf
      simpa only [projectTreeInputsBelow, appendTreeInputProjection, List.append_nil] using origin
  | @node left right leftInputs rightInputs leftTree rightTree output rows =>
    let localResult := descendCell initial current priorSteps checked root left right output rows prefixRow
    have localChecked : runSteps initial (priorSteps ++ localResult.steps) = some localResult.state := by
      simp only [runSteps_append, checked, Option.bind_some]
      exact localResult.checked
    have localSupport := descendCell_supported initial current priorSteps checked root left right output
      rows prefixRow originalCount allowed treeOriginal.2.2 supported originalBound origin
    have localOrigins := descendCell_origins initial current priorSteps checked root left right output
      rows prefixRow originalCount allowed treeOriginal.2.2 origin bound
    let leftPrefix := localResult.results left (by simp)
    let first := projectTreeInputsBelow leftTree localResult.state (priorSteps ++ localResult.steps)
      localChecked root leftPrefix
    have firstInvariant := projectTreeInputsBelow_supported leftTree localResult.state
      (priorSteps ++ localResult.steps) localChecked root leftPrefix originalCount allowed
      treeOriginal.1 localSupport originalBound (localOrigins left (by simp))
      (bound.trans (runSteps_lastId_le localResult.checked))
    have firstChecked : runSteps initial ((priorSteps ++ localResult.steps) ++ first.steps) = some first.state := by
      simp only [runSteps_append, localChecked, Option.bind_some]
      exact first.checked
    let rightPrefix := FoldProjection.afterTrace (localResult.results right (by simp))
      first.state first.steps first.checked
    let second := projectTreeInputsBelow rightTree first.state
      ((priorSteps ++ localResult.steps) ++ first.steps) firstChecked root rightPrefix
    have rightOrigin := resultOrigin_append_right originalCount allowed
      (priorSteps ++ localResult.steps) first.steps
      (localResult.results right (by simp)).row.id (localOrigins right (by simp))
    have secondInvariant := projectTreeInputsBelow_supported rightTree first.state
      ((priorSteps ++ localResult.steps) ++ first.steps) firstChecked root rightPrefix
      originalCount allowed treeOriginal.2.1 firstInvariant.1 originalBound rightOrigin
      ((bound.trans (runSteps_lastId_le localResult.checked)).trans (runSteps_lastId_le first.checked))
    refine ⟨?_, ?_⟩
    · simpa only [projectTreeInputsBelow, appendTreeInputProjection, List.append_assoc, localResult, leftPrefix,
        first, rightPrefix, second] using secondInvariant.1
    · intro input member
      by_cases leftMem : input ∈ leftInputs
      · have result := resultOrigin_append_right originalCount allowed
          ((priorSteps ++ localResult.steps) ++ first.steps) second.steps
          (first.results input leftMem).row.id (firstInvariant.2 input leftMem)
        dsimp only [projectTreeInputsBelow, appendTreeInputProjection]
        rw [dite_eq_left leftMem]
        simpa only [projectTreeInputsBelow, appendTreeInputProjection, ite_eq_left leftMem, dite_eq_left leftMem, FoldProjection.afterTrace, getter_transport, getter_transport_apply, getter_transport_apply_two, dite_apply, ite_apply, apply_dite, apply_ite, eq_self_iff_true, dite_true, ite_true,
          List.append_assoc, localResult, leftPrefix, first, rightPrefix, second] using result
      · have rightMem := (List.mem_append.mp member).resolve_left leftMem
        dsimp only [projectTreeInputsBelow, appendTreeInputProjection]
        rw [dite_eq_right leftMem]
        simpa only [projectTreeInputsBelow, appendTreeInputProjection, ite_eq_right leftMem, dite_eq_right leftMem, getter_transport, getter_transport_apply, getter_transport_apply_two, dite_apply, ite_apply, apply_dite, apply_ite, eq_self_iff_true, dite_true, ite_true, List.append_assoc, localResult,
          leftPrefix, first, rightPrefix, second] using secondInvariant.2 input rightMem
termination_by inputs.length
decreasing_by
  all_goals
    have leftPositive := leftTree.nodes_leaves
    have rightPositive := rightTree.nodes_leaves
    simp_all only [List.length_append]
    omega

theorem supplyOriginals_transport (allowed : Nat → Prop) (rename : Nat → Fin v)
    {before after : List (Bounded.Producer Nat)} (equal : before = after)
    (supply : RowSupply state rename before) (original : SupplyOriginals allowed supply) :
    SupplyOriginals allowed (Eq.mp (congrArg (RowSupply state rename) equal) supply) := by
  subst after
  exact original

def ProducerOriginals (allowed : Nat → Prop) {rename : Nat → Fin v}
    {producer : Bounded.Producer Nat} (rows : OriginalRows state rename producer) : Prop :=
  ∀ index, allowed (rows.row index).id

/-- Changing the producer index transports row bounds and contents, but the
original occurrence identifier is independent of those indices. -/
theorem producerOriginals_transport (allowed : Nat → Prop) (rename : Nat → Fin v)
    {before after : Bounded.Producer Nat} (equal : before = after)
    (rows : OriginalRows state rename before) (original : ProducerOriginals allowed rows) :
    ProducerOriginals allowed (Eq.mp (congrArg (OriginalRows state rename) equal) rows) := by
  subst after
  exact original

theorem prefixSupply_originals (allowed : Nat → Prop) (rename : Nat → Fin v)
    (before after : List (Bounded.Producer Nat)) (supply : RowSupply state rename (before ++ after))
    (original : SupplyOriginals allowed supply) :
    SupplyOriginals allowed (prefixSupply before after supply) := by
  intro owner
  let index : Fin (before ++ after).length := ⟨owner.val, by simp only [List.length_append]; omega⟩
  have producerEquality : (before ++ after)[index.val] = before[owner.val] :=
    List.getElem_append_left owner.isLt
  have result := producerOriginals_transport allowed rename producerEquality (supply index) (original index)
  simpa only [prefixSupply, index, ProducerOriginals] using result

theorem suffixSupply_originals (allowed : Nat → Prop) (rename : Nat → Fin v)
    (before after : List (Bounded.Producer Nat)) (supply : RowSupply state rename (before ++ after))
    (original : SupplyOriginals allowed supply) :
    SupplyOriginals allowed (suffixSupply before after supply) := by
  intro owner
  let index : Fin (before ++ after).length := ⟨before.length + owner.val, by
    simp only [List.length_append]; omega⟩
  have producerEquality : (before ++ after)[index.val] = after[owner.val] := by
    simp only [index, List.getElem_append_right (by omega : before.length ≤ before.length + owner.val),
      Nat.add_sub_cancel_left]
  have result := producerOriginals_transport allowed rename producerEquality (supply index) (original index)
  simpa only [suffixSupply, index, ProducerOriginals] using result

/-- Adjacent-pair construction introduces only the three supplied original
rows. A carried singleton creates no equation or alias occurrence. -/
theorem pairLayerForest_originals (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)} (forest : RawForest state rename handles leaves)
    (lastID : Nat) (supply : RowSupply state rename
      (SourceSerialFold.pairLayer .conjunction lastID handles).producers)
    (forestOriginal : ForestOriginals allowed forest) (supplyOriginal : SupplyOriginals allowed supply) :
    ForestOriginals allowed (pairLayerForest forest lastID supply) := by
  cases forest with
  | nil => trivial
  | cons left leftLeaves leftTree rest =>
    cases rest with
    | nil =>
      dsimp only [pairLayerForest]
      simpa only [pairLayerForest, SourceSerialFold.pairLayer, ForestOriginals, List.append_nil, predicate_transport, id_eq, treeOriginals_mp_indices, treeOriginals_mpr_indices, forestOriginals_mp_indices, forestOriginals_mpr_indices, treeOriginals_mp_self, treeOriginals_mpr_self, forestOriginals_mp_self, forestOriginals_mpr_self, treeOriginals_mpr_inputs, treeOriginals_mpr_output, forestOriginals_mpr_leaves, forestOriginals_mpr_handles, forestOriginals_cast_leaves, forestOriginals_cast_handles] using forestOriginal
    | @cons right rightLeaves rightTree tailHandles tailLeaves tail =>
      let producer : Bounded.Producer Nat := ⟨(lastID + 1, true), .and [left, right]⟩
      let restProducers := (SourceSerialFold.pairLayer .conjunction (lastID + 1) tailHandles).producers
      change RowSupply state rename (producer :: restProducers) at supply
      have nodeOriginal := binaryRows_originals allowed rename left right (lastID + 1, true)
        (supply ⟨0, by simp [List.length_cons]⟩) ((by intro rowIndex; exact supplyOriginal ⟨0, by simp [SourceSerialFold.pairLayer]⟩ rowIndex))
      have tailOriginal : SupplyOriginals allowed (tailSupply producer restProducers supply) := by
        intro owner index
        exact supplyOriginal _ _
      have nextOriginal := pairLayerForest_originals allowed tail (lastID + 1)
        (tailSupply producer restProducers supply) forestOriginal.2.2 tailOriginal
      dsimp only [pairLayerForest, id]
      simpa only [pairLayerForest, SourceSerialFold.pairLayer, id, ForestOriginals, TreeOriginals, List.map_append,
        List.append_assoc, predicate_transport, id_eq, treeOriginals_mp_indices, treeOriginals_mpr_indices, forestOriginals_mp_indices, forestOriginals_mpr_indices, treeOriginals_mp_self, treeOriginals_mpr_self, forestOriginals_mp_self, forestOriginals_mpr_self, treeOriginals_mpr_inputs, treeOriginals_mpr_output, forestOriginals_mpr_leaves, forestOriginals_mpr_handles, forestOriginals_cast_leaves, forestOriginals_cast_handles, treeOriginals_cast_inputs] using
        And.intro (And.intro forestOriginal.1 (And.intro forestOriginal.2.1 nodeOriginal)) nextOriginal
termination_by handles.length

decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- The allocator's real producer decomposition propagates original support
through every balanced layer, using its exact prefix and suffix supplies. -/
theorem allocateForest_originals (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)} (forest : RawForest state rename handles leaves)
    (lastID : Nat) (nonempty : handles ≠ [])
    (supply : RowSupply state rename (SourceSerialFold.allocate .conjunction lastID handles).producers)
    (forestOriginal : ForestOriginals allowed forest) (supplyOriginal : SupplyOriginals allowed supply) :
    TreeOriginals allowed (allocateForest forest lastID nonempty supply) := by
  cases forest with
  | nil => exact False.elim (nonempty rfl)
  | cons left leftLeaves leftTree rest =>
    cases rest with
    | nil =>
      simpa only [allocateForest, SourceSerialFold.allocate_unary, List.append_nil, predicate_transport, id_eq, treeOriginals_mp_indices, treeOriginals_mpr_indices, forestOriginals_mp_indices, forestOriginals_mpr_indices, treeOriginals_mp_self, treeOriginals_mpr_self, forestOriginals_mp_self, forestOriginals_mpr_self, treeOriginals_mpr_inputs, treeOriginals_mpr_output, forestOriginals_mpr_leaves, forestOriginals_mpr_handles, treeOriginals_cast_inputs, treeOriginals_cast_output] using forestOriginal.1
    | @cons right rightLeaves rightTree tailHandles tailLeaves tail =>
      let layer := SourceSerialFold.pairLayer .conjunction lastID (left :: right :: tailHandles)
      let remaining := SourceSerialFold.allocate .conjunction layer.nextID layer.handles
      have expansion : SourceSerialFold.allocate .conjunction lastID (left :: right :: tailHandles) =
          { output := remaining.output, producers := layer.producers ++ remaining.producers,
            nextID := remaining.nextID } := by rw [SourceSerialFold.allocate]
      have producerEquality := congrArg SourceSerialFold.Result.producers expansion
      let normalizedSupply : RowSupply state rename (layer.producers ++ remaining.producers) :=
        Eq.mp (congrArg (RowSupply state rename) producerEquality) supply
      have normalizedOriginal : SupplyOriginals allowed normalizedSupply :=
        supplyOriginals_transport allowed rename producerEquality supply supplyOriginal
      let paired := pairLayerForest
        (RawForest.cons left leftLeaves leftTree (RawForest.cons right rightLeaves rightTree tail))
        lastID (prefixSupply layer.producers remaining.producers normalizedSupply)
      have pairedOriginal : ForestOriginals allowed paired :=
        pairLayerForest_originals allowed _ lastID _ forestOriginal
          (prefixSupply_originals allowed rename layer.producers remaining.producers normalizedSupply normalizedOriginal)
      have layerNonempty : layer.handles ≠ [] := by
        have size := SourceSerialFold.pairLayer_length .conjunction lastID (left :: right :: tailHandles)
        intro empty
        have zero : layer.handles.length = 0 := by rw [empty]; rfl
        simp only [List.length_cons] at size
        change layer.handles.length = _ at size
        omega
      have result := allocateForest_originals allowed paired layer.nextID layerNonempty
        (suffixSupply layer.producers remaining.producers normalizedSupply) pairedOriginal
        (suffixSupply_originals allowed rename layer.producers remaining.producers normalizedSupply normalizedOriginal)
      simpa only [allocateForest, expansion, layer, remaining, normalizedSupply, paired, predicate_transport, id_eq, treeOriginals_mp_indices, treeOriginals_mpr_indices, forestOriginals_mp_indices, forestOriginals_mpr_indices, treeOriginals_mp_self, treeOriginals_mpr_self, forestOriginals_mp_self, forestOriginals_mpr_self, treeOriginals_mpr_inputs, treeOriginals_mpr_output, forestOriginals_mpr_leaves, forestOriginals_mpr_handles, treeOriginals_cast_inputs, treeOriginals_cast_output] using result
termination_by handles.length

decreasing_by
  have size := SourceSerialFold.pairLayer_length .conjunction lastID (left :: right :: tailHandles)
  simp_all only [List.length_cons]
  omega

def CertificateOrigin (originalCount : Nat) (allowed : Nat → Prop) (steps : List (Step v))
    {root input : Literal (Fin v)} : DirectionalCertificate state root input → Prop
  | .identity _ => True
  | .derived row => ResultOrigin originalCount allowed steps row.row.id

/-- The root traversal starts at its actual original binary rows; unary
identity certificates require no available row. -/
theorem projectTreeInputs_supported (tree : AndTree state output inputs)
    (originalCount : Nat) (allowed : Nat → Prop) (original : TreeOriginals allowed tree)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (bound : originalCount ≤ state.lastId) :
    let actual := projectTreeInputs tree
    SourceBusSchedule.TraceOriginalSupport originalCount allowed actual.steps ∧
      ∀ input member, CertificateOrigin originalCount allowed actual.steps (actual.results input member) := by
  cases tree with
  | leaf input =>
    refine ⟨?_, ?_⟩
    · intro step member
      simp only [projectTreeInputs, List.not_mem_nil] at member
    · intro leaf member
      have same := List.mem_singleton.mp member
      subst leaf
      trivial
  | @node left right leftInputs rightInputs leftTree rightTree output rows =>
    let first := projectTreeInputsBelow leftTree state [] rfl output (ofRow rows.leftRow)
    have emptySupport : SourceBusSchedule.TraceOriginalSupport originalCount allowed ([] : List (Step v)) := by
      intro step member
      simp at member
    have firstInvariant := projectTreeInputsBelow_supported leftTree state [] rfl output
      (ofRow rows.leftRow) originalCount allowed original.1 emptySupport originalBound
      (Or.inl original.2.2.1) bound
    let rightPrefix := FoldProjection.afterTrace (ofRow rows.rightRow) first.state first.steps first.checked
    let second := projectTreeInputsBelow rightTree first.state first.steps first.checked output rightPrefix
    have secondInvariant := projectTreeInputsBelow_supported rightTree first.state first.steps first.checked
      output rightPrefix originalCount allowed original.2.1
      (by simpa only [List.nil_append] using firstInvariant.1) originalBound
      (Or.inl original.2.2.2.1) (bound.trans (runSteps_lastId_le first.checked))
    refine ⟨?_, ?_⟩
    · simpa only [projectTreeInputs, first, rightPrefix, second] using secondInvariant.1
    · intro input member
      by_cases leftMem : input ∈ leftInputs
      · have origin := resultOrigin_append_right originalCount allowed first.steps second.steps
          (first.results input leftMem).row.id
          (by simpa only [List.nil_append] using firstInvariant.2 input leftMem)
        simpa only [projectTreeInputs, ite_eq_left leftMem, dite_eq_left leftMem, CertificateOrigin, FoldProjection.afterTrace, getter_transport, getter_transport_apply, getter_transport_apply_two, dite_apply, ite_apply, apply_dite, apply_ite, eq_self_iff_true, dite_true, ite_true,
          first, rightPrefix, second] using origin
      · have rightMem := (List.mem_append.mp member).resolve_left leftMem
        simpa only [projectTreeInputs, ite_eq_right leftMem, dite_eq_right leftMem, CertificateOrigin, getter_transport, getter_transport_apply, getter_transport_apply_two, dite_apply, ite_apply, apply_dite, apply_ite, eq_self_iff_true, dite_true, ite_true, first, rightPrefix, second]
          using secondInvariant.2 input rightMem

end Controller.NativeProof.SourceFoldProvenance
