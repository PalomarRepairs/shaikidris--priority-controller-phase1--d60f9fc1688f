module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceFoldProvenance

@[expose] public section

/-! Causal original-occurrence support for aggregate projections. Every parent
is either an allowed original row or an earlier result of the actual trace. -/
namespace Controller.NativeProof.SourceFoldAggregateProvenance
open Controller.CNF Controller.Resolution Controller.Resolution.Cases
open Controller.Native
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceFoldProvenance Controller.NativeProof.SourceMismatchHandles
variable {v : Nat} {state initial : State v}

theorem merge_origins (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (current : State v)
    (leftId rightId : Nat) (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (one : ResultOrigin originalCount allowed priorSteps leftId)
    (two : ResultOrigin originalCount allowed priorSteps rightId)
    (bound : originalCount ≤ current.lastId) :
    ResultOrigin originalCount allowed
      (priorSteps ++ (merge current leftId rightId pivot left right).steps)
      (merge current leftId rightId pivot left right).rowId := by
  unfold merge
  split
  · exact resultOrigin_append_right originalCount allowed priorSteps [] leftId one
  · split
    · exact resultOrigin_append_right originalCount allowed priorSteps [] rightId two
    · exact Or.inr ⟨RUP.resolutionStep current leftId rightId pivot left right,
        by simp, rfl, by change originalCount < current.lastId + 1; omega⟩

theorem appendMerge_origins_supported (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (current : State v)
    (leftId rightId : Nat) (pivot : Literal (Fin v)) (left right : Clause (Fin v))
    (supported : SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (one : ResultOrigin originalCount allowed priorSteps leftId)
    (two : ResultOrigin originalCount allowed priorSteps rightId)
    (leftBound : leftId ≤ current.lastId) (rightBound : rightId ≤ current.lastId) :
    SourceBusSchedule.TraceOriginalSupport originalCount allowed
      (priorSteps ++ (merge current leftId rightId pivot left right).steps) := by
  unfold merge
  split
  · simpa only [List.append_nil] using supported
  · split
    · simpa only [List.append_nil] using supported
    · intro step member parent parentMember
      rcases List.mem_append.mp member with old | fresh
      · have previous := supported step old parent parentMember
        refine ⟨previous.1, ?_⟩
        intro derived
        rcases previous.2 derived with ⟨earlier, contained, same, order⟩
        exact ⟨earlier, List.mem_append_left _ contained, same, order⟩
      · have same := List.mem_singleton.mp fresh
        subst step
        change parent ∈ [leftId, rightId] at parentMember
        have parentOrigin : ResultOrigin originalCount allowed priorSteps parent := by
          rcases List.mem_cons.mp parentMember with same | rest
          · exact same.symm ▸ one
          · have same : parent = rightId := List.mem_singleton.mp rest
            exact same.symm ▸ two
        have parentBound : parent ≤ current.lastId := by
          rcases List.mem_cons.mp parentMember with same | rest
          · exact same.symm ▸ leftBound
          · have same : parent = rightId := List.mem_singleton.mp rest
            exact same.symm ▸ rightBound
        rcases parentOrigin with original | ⟨earlier, contained, same, derived⟩
        · refine ⟨fun _ => original, ?_⟩
          intro larger
          have bound := originalBound parent original
          omega
        · refine ⟨?_, ?_⟩
          · intro old
            omega
          · intro _
            refine ⟨earlier, List.mem_append_left _ contained, same, ?_⟩
            change earlier.id < current.lastId + 1
            rw [same]
            omega

def AggregateOrigin (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) {output : Literal (Fin v)}
    {inputs : List (Literal (Fin v))} : AggregateCertificate state output inputs → Prop
  | .identity => True
  | .derived row => ResultOrigin originalCount allowed priorSteps row.row.id

theorem aggregateOrigin_afterTrace (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps extra : List (Step v)) {output : Literal (Fin v)}
    {inputs : List (Literal (Fin v))} (certificate : AggregateCertificate state output inputs)
    (next : State v) (checked : runSteps state extra = some next)
    (origin : AggregateOrigin originalCount allowed priorSteps certificate) :
    AggregateOrigin originalCount allowed (priorSteps ++ extra)
      (certificate.afterTrace next extra checked) := by
  cases certificate with
  | identity => trivial
  | derived row =>
    exact resultOrigin_append_right originalCount allowed priorSteps extra row.row.id origin

/-- Both the aggregate and its parent may come from earlier checked inferences.
Identity leaves retain the existing parent without emitting a new row. -/
theorem expandChild_supported (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (current : State v)
    (child : Literal (Fin v)) (inputs : List (Literal (Fin v)))
    (rest : Clause (Fin v)) (parent : AvailableSubclause current (negate child :: rest))
    (certificate : AggregateCertificate current child inputs)
    (supported : SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (currentBound : originalCount ≤ current.lastId)
    (parentOrigin : ResultOrigin originalCount allowed priorSteps parent.row.id)
    (childOrigin : AggregateOrigin originalCount allowed priorSteps certificate) :
    SourceBusSchedule.TraceOriginalSupport originalCount allowed
      (priorSteps ++ (expandChild current child inputs rest parent certificate).steps) ∧
    ResultOrigin originalCount allowed
      (priorSteps ++ (expandChild current child inputs rest parent certificate).steps)
      (expandChild current child inputs rest parent certificate).result.row.id := by
  cases certificate with
  | identity =>
    exact ⟨by simpa only [expandChild, List.append_nil] using supported,
      by simpa only [expandChild, retarget, List.append_nil] using parentOrigin⟩
  | derived row =>
    refine ⟨?_, ?_⟩
    · exact appendMerge_origins_supported originalCount allowed priorSteps current
        parent.row.id row.row.id child parent.clause row.clause supported originalBound
        parentOrigin childOrigin parent.row.bound row.row.bound
    · exact merge_origins originalCount allowed priorSteps current parent.row.id row.row.id
        child parent.clause row.clause parentOrigin childOrigin currentBound

/-- The two actual child eliminations preserve causal support, including when
normalization returns an earlier stronger subclause in either elimination. -/
theorem expandChildren_supported (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (current : State v)
    (left right output : Literal (Fin v))
    (leftInputs rightInputs : List (Literal (Fin v)))
    (parent : AvailableSubclause current (negate left :: [output, negate right]))
    (leftCertificate : AggregateCertificate current left leftInputs)
    (rightCertificate : AggregateCertificate current right rightInputs)
    (supported : SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (currentBound : originalCount ≤ current.lastId)
    (parentOrigin : ResultOrigin originalCount allowed priorSteps parent.row.id)
    (leftOrigin : AggregateOrigin originalCount allowed priorSteps leftCertificate)
    (rightOrigin : AggregateOrigin originalCount allowed priorSteps rightCertificate) :
    let first := expandChild current left leftInputs [output, negate right] parent leftCertificate
    let rightParent : AvailableSubclause first.state
        (negate right :: (output :: leftInputs.map negate)) :=
      retarget first.result (by
        intro literal member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        aesop)
    let certificate := rightCertificate.afterTrace first.state first.steps first.checked
    let second := expandChild first.state right rightInputs
      (output :: leftInputs.map negate) rightParent certificate
    SourceBusSchedule.TraceOriginalSupport originalCount allowed
      (priorSteps ++ (first.steps ++ second.steps)) ∧
    ResultOrigin originalCount allowed (priorSteps ++ (first.steps ++ second.steps))
      second.result.row.id := by
  dsimp only
  let first := expandChild current left leftInputs [output, negate right] parent leftCertificate
  let rightParent : AvailableSubclause first.state
      (negate right :: (output :: leftInputs.map negate)) :=
    retarget first.result (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  let certificate := rightCertificate.afterTrace first.state first.steps first.checked
  have firstSupport := expandChild_supported originalCount allowed priorSteps current left
    leftInputs [output, negate right] parent leftCertificate supported originalBound
    currentBound parentOrigin leftOrigin
  have secondSupport := expandChild_supported originalCount allowed (priorSteps ++ first.steps)
    first.state right rightInputs (output :: leftInputs.map negate) rightParent certificate
    firstSupport.1 originalBound (currentBound.trans (runSteps_lastId_le first.checked))
    firstSupport.2 (aggregateOrigin_afterTrace originalCount allowed priorSteps first.steps
      rightCertificate first.state first.checked rightOrigin)
  simpa only [List.append_assoc, first, rightParent, certificate] using secondSupport

theorem projectTreeLongStep_supported (originalCount : Nat) (allowed : Nat → Prop)
    (priorSteps : List (Step v)) (current : State v)
    (left right output : Literal (Fin v))
    (leftInputs rightInputs : List (Literal (Fin v))) (leftNodes rightNodes : Nat)
    (rows : BinaryAndRows current left right output)
    (first : AggregateProjection current left leftInputs (2 * leftNodes))
    (second : AggregateProjection first.state right rightInputs (2 * rightNodes))
    (original : BinaryOriginals allowed rows)
    (supported : SourceBusSchedule.TraceOriginalSupport originalCount allowed
      ((priorSteps ++ first.steps) ++ second.steps))
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (currentBound : originalCount ≤ second.state.lastId)
    (firstOrigin : AggregateOrigin originalCount allowed (priorSteps ++ first.steps) first.result)
    (secondOrigin : AggregateOrigin originalCount allowed
      ((priorSteps ++ first.steps) ++ second.steps) second.result) :
    let actual := projectTreeLongStep left right output leftInputs rightInputs
      leftNodes rightNodes rows first second
    SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ actual.steps) ∧
    AggregateOrigin originalCount allowed (priorSteps ++ actual.steps) actual.result := by
  have childrenChecked : runSteps current (first.steps ++ second.steps) = some second.state := by
    rw [runSteps_append, first.checked]
    exact second.checked
  let originalRow := FoldProjection.afterTrace (ofRow rows.longRow) second.state
    (first.steps ++ second.steps) childrenChecked
  let leftParent : AvailableSubclause second.state (negate left :: [output, negate right]) :=
    retarget originalRow (by
      intro literal member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop)
  let leftCertificate := first.result.afterTrace second.state second.steps second.checked
  have leftOrigin := aggregateOrigin_afterTrace originalCount allowed
    (priorSteps ++ first.steps) second.steps first.result second.state second.checked firstOrigin
  have result := expandChildren_supported originalCount allowed
    ((priorSteps ++ first.steps) ++ second.steps) second.state left right output
    leftInputs rightInputs leftParent leftCertificate second.result supported originalBound
    currentBound (Or.inl original.2.2) leftOrigin secondOrigin
  simpa only [projectTreeLongStep, AggregateOrigin, originalRow, leftParent,
    leftCertificate, retarget, List.append_assoc] using result

theorem aggregateProjection_transport {output : Literal (Fin v)}
    {inputs : List (Literal (Fin v))} {before after : Nat} (equal : before = after)
    (projection : AggregateProjection state output inputs before)
    (originalCount : Nat) (allowed : Nat → Prop) (priorSteps : List (Step v)) :
    let moved := Eq.mp (congrArg (AggregateProjection state output inputs) equal) projection
    (SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ moved.steps) ∧
      AggregateOrigin originalCount allowed (priorSteps ++ moved.steps) moved.result) ↔
    (SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ projection.steps) ∧
      AggregateOrigin originalCount allowed (priorSteps ++ projection.steps) projection.result) := by
  subst after
  rfl

theorem aggregateProjection_transport_any {output : Literal (Fin v)}
    {inputs : List (Literal (Fin v))} {before after : Nat} (equal : before = after)
    (typeEqual : AggregateProjection state output inputs before =
      AggregateProjection state output inputs after)
    (projection : AggregateProjection state output inputs before)
    (originalCount : Nat) (allowed : Nat → Prop) (priorSteps : List (Step v)) :
    let moved := Eq.mp typeEqual projection
    (SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ moved.steps) ∧
      AggregateOrigin originalCount allowed (priorSteps ++ moved.steps) moved.result) ↔
    (SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ projection.steps) ∧
      AggregateOrigin originalCount allowed (priorSteps ++ projection.steps) projection.result) := by
  subst after
  rfl

/-- The actual balanced traversal retains only original occurrences and
causally earlier checked results, for every leaf and every internal node. -/
theorem projectTreeLong_supported {output : Literal (Fin v)}
    {inputs : List (Literal (Fin v))} (current : State v)
    (tree : AndTree current output inputs)
    (originalCount : Nat) (allowed : Nat → Prop) (priorSteps : List (Step v))
    (original : TreeOriginals allowed tree)
    (supported : SourceBusSchedule.TraceOriginalSupport originalCount allowed priorSteps)
    (originalBound : ∀ id, allowed id → id ≤ originalCount)
    (bound : originalCount ≤ current.lastId) :
    let actual := projectTreeLong tree
    SourceBusSchedule.TraceOriginalSupport originalCount allowed (priorSteps ++ actual.steps) ∧
      AggregateOrigin originalCount allowed (priorSteps ++ actual.steps) actual.result := by
  cases tree with
  | leaf input =>
    dsimp only
    rw [projectTreeLong]
    exact ⟨by simpa only [List.append_nil] using supported, trivial⟩
  | @node left right leftInputs rightInputs leftTree rightTree output rows =>
    let first := projectTreeLong leftTree
    have firstInvariant := projectTreeLong_supported current leftTree originalCount allowed priorSteps
      original.1 supported originalBound bound
    let rightCurrent := rightTree.afterTrace first.state first.steps first.checked
    let second := projectTreeLong rightCurrent
    have secondInvariant := projectTreeLong_supported first.state rightCurrent originalCount allowed
      (priorSteps ++ first.steps)
      (treeOriginals_afterTrace allowed rightTree original.2.1 first.state first.steps first.checked)
      firstInvariant.1 originalBound (bound.trans (runSteps_lastId_le first.checked))
    let secondTyped : AggregateProjection first.state right rightInputs (2 * rightTree.nodes) := by
      simpa only [rightCurrent, AndTree.afterTrace_nodes] using second
    have typedInvariant :
        SourceBusSchedule.TraceOriginalSupport originalCount allowed
          ((priorSteps ++ first.steps) ++ secondTyped.steps) ∧
        AggregateOrigin originalCount allowed
          ((priorSteps ++ first.steps) ++ secondTyped.steps) secondTyped.result := by
      dsimp only [secondTyped]
      apply (aggregateProjection_transport_any
        (congrArg (fun n => 2 * n) (AndTree.afterTrace_nodes rightTree first.state first.steps first.checked))
        _ second originalCount allowed (priorSteps ++ first.steps)).mpr
      exact secondInvariant
    have result := projectTreeLongStep_supported originalCount allowed priorSteps current left right
      output leftInputs rightInputs leftTree.nodes rightTree.nodes rows first secondTyped
      original.2.2 typedInvariant.1 originalBound
      ((bound.trans (runSteps_lastId_le first.checked)).trans (runSteps_lastId_le secondTyped.checked))
      firstInvariant.2 typedInvariant.2
    have whole : projectTreeLong (AndTree.node leftTree rightTree output rows) =
        projectTreeLongStep left right output leftInputs rightInputs leftTree.nodes rightTree.nodes
          rows first secondTyped := by
      rw [projectTreeLong]
    dsimp only
    rw [whole]
    exact result
termination_by inputs.length
 decreasing_by
  all_goals have := leftTree.nodes_leaves
  all_goals have := rightTree.nodes_leaves
  all_goals simp_all only [List.length_append]
  all_goals omega

/-- Polarity reflection preserves every stored OR occurrence identifier. -/
def OrForestOriginals (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)} : RawOrForest state rename handles leaves → Prop
  | .nil => True
  | .cons _ _ tree rest => TreeOriginals allowed tree ∧ OrForestOriginals allowed rest

@[simp] theorem orForestOriginals_cast_leaves (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles before after : List (Literal Nat)} (equal : before = after)
    (forest : RawOrForest state rename handles before) :
    OrForestOriginals allowed (Eq.mp (congrArg (RawOrForest state rename handles) equal) forest) ↔
      OrForestOriginals allowed forest := by
  subst after
  rfl


@[simp] theorem orForestOriginals_cast_handles (allowed : Nat → Prop) {rename : Nat → Fin v}
    {before after leaves : List (Literal Nat)} (equal : before = after)
    (forest : RawOrForest state rename before leaves) :
    OrForestOriginals allowed (Eq.mp (congrArg (fun handles => RawOrForest state rename handles leaves) equal) forest) ↔
      OrForestOriginals allowed forest := by
  subst after
  rfl


@[simp] theorem orForestOriginals_mpr_leaves (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles before after : List (Literal Nat)} (equal : before = after)
    (forest : RawOrForest state rename handles after) :
    OrForestOriginals allowed (Eq.mpr (congrArg (RawOrForest state rename handles) equal) forest) ↔
      OrForestOriginals allowed forest := by
  subst after
  rfl


@[simp] theorem orForestOriginals_mpr_handles (allowed : Nat → Prop) {rename : Nat → Fin v}
    {before after leaves : List (Literal Nat)} (equal : before = after)
    (forest : RawOrForest state rename after leaves) :
    OrForestOriginals allowed (Eq.mpr (congrArg (fun handles => RawOrForest state rename handles leaves) equal) forest) ↔
      OrForestOriginals allowed forest := by
  subst after
  rfl


@[simp] theorem orForestOriginals_mp_self (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)}
    (equal : RawOrForest state rename handles leaves = RawOrForest state rename handles leaves)
    (forest : RawOrForest state rename handles leaves) :
    OrForestOriginals allowed (Eq.mp equal forest) ↔ OrForestOriginals allowed forest := by
  rfl


@[simp] theorem orForestOriginals_mpr_self (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)}
    (equal : RawOrForest state rename handles leaves = RawOrForest state rename handles leaves)
    (forest : RawOrForest state rename handles leaves) :
    OrForestOriginals allowed (Eq.mpr equal forest) ↔ OrForestOriginals allowed forest := by
  rfl


theorem orForestOriginals_mp_indices (allowed : Nat → Prop) {rename : Nat → Fin v}
    {beforeHandles afterHandles beforeLeaves afterLeaves : List (Literal Nat)}
    (handlesEqual : beforeHandles = afterHandles) (leavesEqual : beforeLeaves = afterLeaves)
    (typeEqual : RawOrForest state rename beforeHandles beforeLeaves =
      RawOrForest state rename afterHandles afterLeaves)
    (forest : RawOrForest state rename beforeHandles beforeLeaves) :
    OrForestOriginals allowed (Eq.mp typeEqual forest) ↔ OrForestOriginals allowed forest := by
  subst afterHandles
  subst afterLeaves
  rfl


theorem orForestOriginals_mpr_indices (allowed : Nat → Prop) {rename : Nat → Fin v}
    {beforeHandles afterHandles beforeLeaves afterLeaves : List (Literal Nat)}
    (handlesEqual : beforeHandles = afterHandles) (leavesEqual : beforeLeaves = afterLeaves)
    (typeEqual : RawOrForest state rename beforeHandles beforeLeaves =
      RawOrForest state rename afterHandles afterLeaves)
    (forest : RawOrForest state rename afterHandles afterLeaves) :
    OrForestOriginals allowed (Eq.mpr typeEqual forest) ↔ OrForestOriginals allowed forest := by
  subst afterHandles
  subst afterLeaves
  rfl


theorem initialOrForest_originals (allowed : Nat → Prop) (rename : Nat → Fin v)
    (inputs : List (Literal Nat)) :
    OrForestOriginals allowed (initialOrForest (state := state) rename inputs) := by
  induction inputs with
  | nil => trivial
  | cons input rest ih => exact ⟨True.intro, ih⟩

theorem available_cast_id {before after : Clause (Fin v)}
    (same : before = after) (typeEqual : Rows.Available state before = Rows.Available state after)
    (row : Rows.Available state before) : (Eq.mp typeEqual row).id = row.id := by
  subst after
  rfl

theorem available_mpr_id {before after : Clause (Fin v)}
    (same : before = after) (typeEqual : Rows.Available state before = Rows.Available state after)
    (row : Rows.Available state after) : (Eq.mpr typeEqual row).id = row.id := by
  subst after
  rfl

theorem binaryOrRows_originals (allowed : Nat → Prop) (rename : Nat → Fin v)
    (left right output : Literal Nat)
    (rows : OriginalRows state rename (⟨output, .or [left, right]⟩ : Bounded.Producer Nat))
    (original : ∀ index, allowed (rows.row index).id) :
    BinaryOriginals allowed (binaryOrRows left right output rows) := by
  let one : Rows.Available state [mapLiteral rename output, negate (mapLiteral rename left)] :=
    rows.row ⟨0, by change 0 < 3; decide⟩
  let two : Rows.Available state [mapLiteral rename output, negate (mapLiteral rename right)] :=
    rows.row ⟨1, by change 1 < 3; decide⟩
  let three : Rows.Available state
      [negate (mapLiteral rename output), mapLiteral rename left, mapLiteral rename right] :=
    rows.row ⟨2, by change 2 < 3; decide⟩
  let normalized : BinaryOrRows state (mapLiteral rename left) (mapLiteral rename right)
      (mapLiteral rename output) := ⟨one, two, three⟩
  have whole : binaryOrRows left right output rows = normalized.dual := rfl
  have oneOrigin : allowed one.id := original _
  have twoOrigin : allowed two.id := original _
  have threeOrigin : allowed three.id := original _
  rw [whole]
  change allowed normalized.dual.leftRow.id ∧
    allowed normalized.dual.rightRow.id ∧ allowed normalized.dual.longRow.id
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [normalized, BinaryOrRows.dual]
    rw [available_mpr_id (by simp only [negate_negate])]
    exact oneOrigin
  · dsimp only [normalized, BinaryOrRows.dual]
    rw [available_mpr_id (by simp only [negate_negate])]
    exact twoOrigin
  · dsimp only [normalized, BinaryOrRows.dual]
    rw [available_mpr_id (by simp only [negate_negate])]
    exact threeOrigin

theorem pairLayerOrForest_originals (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)} (forest : RawOrForest state rename handles leaves)
    (lastID : Nat) (supply : RowSupply state rename
      (SourceSerialFold.pairLayer .disjunction lastID handles).producers)
    (forestOriginal : OrForestOriginals allowed forest) (supplyOriginal : SupplyOriginals allowed supply) :
    OrForestOriginals allowed (pairLayerOrForest forest lastID supply) := by
  cases forest with
  | nil => trivial
  | cons left leftLeaves leftTree rest =>
    cases rest with
    | nil =>
      dsimp only [pairLayerOrForest]
      simpa only [pairLayerOrForest, SourceSerialFold.pairLayer, OrForestOriginals, List.append_nil, predicate_transport, id_eq, treeOriginals_mp_indices, treeOriginals_mpr_indices, orForestOriginals_mp_indices, orForestOriginals_mpr_indices, treeOriginals_mp_self, treeOriginals_mpr_self, orForestOriginals_mp_self, orForestOriginals_mpr_self, treeOriginals_mpr_inputs, treeOriginals_mpr_output, orForestOriginals_mpr_leaves, orForestOriginals_mpr_handles, orForestOriginals_cast_leaves, orForestOriginals_cast_handles] using forestOriginal
    | @cons right rightLeaves rightTree tailHandles tailLeaves tail =>
      let producer : Bounded.Producer Nat := ⟨(lastID + 1, true), .or [left, right]⟩
      let restProducers := (SourceSerialFold.pairLayer .disjunction (lastID + 1) tailHandles).producers
      change RowSupply state rename (producer :: restProducers) at supply
      have nodeOriginal := binaryOrRows_originals allowed rename left right (lastID + 1, true)
        (supply ⟨0, by simp [List.length_cons]⟩) ((by intro rowIndex; exact supplyOriginal ⟨0, by simp [SourceSerialFold.pairLayer]⟩ rowIndex))
      have tailOriginal : SupplyOriginals allowed (tailSupply producer restProducers supply) := by
        intro owner index
        exact supplyOriginal _ _
      have nextOriginal := pairLayerOrForest_originals allowed tail (lastID + 1)
        (tailSupply producer restProducers supply) forestOriginal.2.2 tailOriginal
      dsimp only [pairLayerOrForest, id]
      simpa only [pairLayerOrForest, SourceSerialFold.pairLayer, id, OrForestOriginals, TreeOriginals, List.map_append,
        List.append_assoc, predicate_transport, id_eq, treeOriginals_mp_indices, treeOriginals_mpr_indices, orForestOriginals_mp_indices, orForestOriginals_mpr_indices, treeOriginals_mp_self, treeOriginals_mpr_self, orForestOriginals_mp_self, orForestOriginals_mpr_self, treeOriginals_mpr_inputs, treeOriginals_mpr_output, orForestOriginals_mpr_leaves, orForestOriginals_mpr_handles, orForestOriginals_cast_leaves, orForestOriginals_cast_handles, treeOriginals_cast_inputs] using
        And.intro (And.intro forestOriginal.1 (And.intro forestOriginal.2.1 nodeOriginal)) nextOriginal
termination_by handles.length

decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- The allocator's real producer decomposition propagates original support
through every balanced layer, using its exact prefix and suffix supplies. -/
theorem allocateOrForest_originals (allowed : Nat → Prop) {rename : Nat → Fin v}
    {handles leaves : List (Literal Nat)} (forest : RawOrForest state rename handles leaves)
    (lastID : Nat) (nonempty : handles ≠ [])
    (supply : RowSupply state rename (SourceSerialFold.allocate .disjunction lastID handles).producers)
    (forestOriginal : OrForestOriginals allowed forest) (supplyOriginal : SupplyOriginals allowed supply) :
    TreeOriginals allowed (allocateOrForest forest lastID nonempty supply) := by
  cases forest with
  | nil => exact False.elim (nonempty rfl)
  | cons left leftLeaves leftTree rest =>
    cases rest with
    | nil =>
      simpa only [allocateOrForest, SourceSerialFold.allocate_unary, List.append_nil, predicate_transport, id_eq, treeOriginals_mp_indices, treeOriginals_mpr_indices, orForestOriginals_mp_indices, orForestOriginals_mpr_indices, treeOriginals_mp_self, treeOriginals_mpr_self, orForestOriginals_mp_self, orForestOriginals_mpr_self, treeOriginals_mpr_inputs, treeOriginals_mpr_output, orForestOriginals_mpr_leaves, orForestOriginals_mpr_handles, treeOriginals_cast_inputs, treeOriginals_cast_output] using forestOriginal.1
    | @cons right rightLeaves rightTree tailHandles tailLeaves tail =>
      let layer := SourceSerialFold.pairLayer .disjunction lastID (left :: right :: tailHandles)
      let remaining := SourceSerialFold.allocate .disjunction layer.nextID layer.handles
      have expansion : SourceSerialFold.allocate .disjunction lastID (left :: right :: tailHandles) =
          { output := remaining.output, producers := layer.producers ++ remaining.producers,
            nextID := remaining.nextID } := by rw [SourceSerialFold.allocate]
      have producerEquality := congrArg SourceSerialFold.Result.producers expansion
      let normalizedSupply : RowSupply state rename (layer.producers ++ remaining.producers) :=
        Eq.mp (congrArg (RowSupply state rename) producerEquality) supply
      have normalizedOriginal : SupplyOriginals allowed normalizedSupply :=
        supplyOriginals_transport allowed rename producerEquality supply supplyOriginal
      let paired := pairLayerOrForest
        (RawOrForest.cons left leftLeaves leftTree (RawOrForest.cons right rightLeaves rightTree tail))
        lastID (prefixSupply layer.producers remaining.producers normalizedSupply)
      have pairedOriginal : OrForestOriginals allowed paired :=
        pairLayerOrForest_originals allowed _ lastID _ forestOriginal
          (prefixSupply_originals allowed rename layer.producers remaining.producers normalizedSupply normalizedOriginal)
      have layerNonempty : layer.handles ≠ [] := by
        have size := SourceSerialFold.pairLayer_length .disjunction lastID (left :: right :: tailHandles)
        intro empty
        have zero : layer.handles.length = 0 := by rw [empty]; rfl
        simp only [List.length_cons] at size
        change layer.handles.length = _ at size
        omega
      have result := allocateOrForest_originals allowed paired layer.nextID layerNonempty
        (suffixSupply layer.producers remaining.producers normalizedSupply) pairedOriginal
        (suffixSupply_originals allowed rename layer.producers remaining.producers normalizedSupply normalizedOriginal)
      simpa only [allocateOrForest, expansion, layer, remaining, normalizedSupply, paired, predicate_transport, id_eq, treeOriginals_mp_indices, treeOriginals_mpr_indices, orForestOriginals_mp_indices, orForestOriginals_mpr_indices, treeOriginals_mp_self, treeOriginals_mpr_self, orForestOriginals_mp_self, orForestOriginals_mpr_self, treeOriginals_mpr_inputs, treeOriginals_mpr_output, orForestOriginals_mpr_leaves, orForestOriginals_mpr_handles, treeOriginals_cast_inputs, treeOriginals_cast_output] using result
termination_by handles.length

decreasing_by
  have size := SourceSerialFold.pairLayer_length .disjunction lastID (left :: right :: tailHandles)
  simp_all only [List.length_cons]
  omega


end Controller.NativeProof.SourceFoldAggregateProvenance
