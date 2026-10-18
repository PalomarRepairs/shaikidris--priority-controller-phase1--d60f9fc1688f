module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SupportRows

@[expose] public section

/-! Stored native summaries retain finite supports and ordinary-resolution
rows. Topological lookup reuses each child summary at every shared incidence. -/
namespace Controller.NativeProof.SourceSupportSummaries
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceStageXor
open Controller.NativeProof.SourceDecoderTraversal Controller.NativeProof.SourceDecoderSchedule
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderEvaluation
open Controller.NativeProof.SourceHealthyOne Controller.NativeProof.SupportRows
variable {parameters : Parameters} {v : Nat}

def qualifier (rename : Nat → Fin v) := qualifierLiteral (parameters := parameters) rename .faulty
def output (rename : Nat → Fin v) := outputLiteral (parameters := parameters) rename .faulty
def support (node : Fin parameters.decoder.nodeCount) :=
  DecoderSupport.support parameters.decoder parameters.buses parameters.bridge.target node

structure Entry (rename : Nat → Fin v) (state : State v) (node : Fin parameters.decoder.nodeCount) where
  stored : Finset (Fin parameters.channels)
  exactSupport : stored = support (parameters := parameters) node
  summary : Summary state (cofactor (parameters := parameters) rename) (output rename node) (heads stored (qualifier rename))

def Entry.afterTrace (entry : Entry (parameters := parameters) rename state node)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    Entry (parameters := parameters) rename next node :=
  ⟨entry.stored, entry.exactSupport, entry.summary.afterTrace next steps checked⟩

structure Table (rename : Nat → Fin v) (count : Nat) where
  prepared : Preparation (parameters := parameters) rename
  entries : ∀ node : Fin parameters.decoder.nodeCount, node.val < count → Entry rename prepared.proofPrefix.state node

def Table.afterTrace (table : Table (parameters := parameters) rename count)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.prepared.proofPrefix.state steps = some next) :
    Table (parameters := parameters) rename count where
  prepared := table.prepared.afterTrace next steps checked
  entries node before := (table.entries node before).afterTrace next steps checked

def childEntry {rename : Nat → Fin v} {node : Fin parameters.decoder.nodeCount} (table : Table (parameters := parameters) rename node.val) (child : Fin node.val) :=
  table.entries (parameters.decoder.childIndex node child) child.isLt

structure NodeStep (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (start : Table (parameters := parameters) rename node.val) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.prepared.proofPrefix.state steps = some state
  entry : Entry rename state node

def zero (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename node.val) (shape : parameters.decoder.node node = .zero) :
    NodeStep rename node table := by
  have unit := decoderZeroUnit rename .faulty node shape table.prepared.proofPrefix
  have same : output rename node = mapLiteral rename (decoderLiveAndOutput .faulty node) := by
    simp only [output, outputLiteral, decoderZero_output .faulty node _ shape]
    rfl
  refine ⟨table.prepared.proofPrefix.state, [], rfl, ∅, ?_, .derived ?_⟩
  · simp [support, DecoderSupport.support, shape]
  · simpa only [heads_empty, same] using retarget unit (fun _ member => List.mem_append_right _ member)

def input (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename node.val) (channel : Fin parameters.channels)
    (shape : parameters.decoder.node node = .input channel) : NodeStep rename node table := by
  have same : output rename node = qualifier rename channel := by
    simp only [output, outputLiteral, decoderInput_output .faulty node channel _ shape, qualifier,
      qualifierAt_eq rename .faulty node channel]
  exact ⟨table.prepared.proofPrefix.state, [], rfl, {channel}, by simp [support, DecoderSupport.support, shape],
    .identity (by simp [same])⟩

def disjunction (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename node.val) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) : NodeStep rename node table := by
  match children with
  | [] =>
    have unit := decoderEmptyDisjunctionUnit rename .faulty node shape table.prepared.proofPrefix
    have same : output rename node = mapLiteral rename (decoderLiveAndOutput .faulty node) := by
      rw [output, outputLiteral, decoderDisjunction_output .faulty node [] shape]
      simp only [decoderDisjunctionOutput, SourceSerialFold.allocate, List.map_nil, decoderLiveAndOutput]
    exact ⟨table.prepared.proofPrefix.state, [], rfl, ∅, by
      change ∅ = DecoderSupport.support parameters.decoder parameters.buses parameters.bridge.target node
      rw [DecoderSupport.support, shape]
      simp,
      .derived (by simpa only [heads_empty, same] using retarget unit (fun _ member => List.mem_append_right _ member))⟩
  | [child] =>
    let previous := childEntry table child
    have same : output rename node = output rename (parameters.decoder.childIndex node child) := by
      rw [output, outputLiteral, decoderDisjunction_output .faulty node [child] shape]
      simpa only [decoderDisjunctionOutput, List.map_cons, List.map_nil, SourceSerialFold.allocate,
        childLiteral] using child_eq_output rename .faulty node child
    refine ⟨table.prepared.proofPrefix.state, [], rfl, previous.stored, ?_, ?_⟩
    · calc
        previous.stored = support (parameters := parameters) (parameters.decoder.childIndex node child) := previous.exactSupport
        _ = support (parameters := parameters) node := by
          unfold support
          conv_rhs => rw [DecoderSupport.support, shape]
          simp
    · exact Eq.mpr (congrArg (fun literal => Summary table.prepared.proofPrefix.state
        (cofactor (parameters := parameters) rename) literal (heads previous.stored (qualifier rename))) same) previous.summary
  | first :: second :: rest =>
    let children := first :: second :: rest
    let stored := children.toFinset.biUnion (fun child => (childEntry table child).stored)
    have correct : stored = support (parameters := parameters) node := by
      change stored = DecoderSupport.support parameters.decoder parameters.buses parameters.bridge.target node
      rw [DecoderSupport.support, shape]
      exact Finset.biUnion_congr rfl (fun child _ => (childEntry table child).exactSupport)
    let start := table.prepared.proofPrefix
    let tree := (decoderDisjunctionTree rename .faulty node children shape (by simp [children])).afterTrace
      start.state start.steps start.checked
    let projected := TreeUnits.nonunaryLong tree (by simp [children])
    let target := cofactor (parameters := parameters) rename ++ negate (output rename node) :: heads stored (qualifier rename)
    let labels := fun child => output rename (parameters.decoder.childIndex node child)
    let supportHeads := fun child => heads (childEntry table child).stored (qualifier rename)
    have parent : AvailableSubclause projected.state (children.map labels ++ target) := by
      apply retarget projected.result
      intro literal member
      have rootEq : dualLiteral rename (SourceSerialFold.allocate .disjunction (decoderPositionBefore .faulty node).lastID
          (children.map (fun child => (decoderPositionBefore .faulty node).slots
            (.internal (.decoder .faulty (parameters.decoder.childIndex node child)))))).output = negate (output rename node) := by
        rw [output, outputLiteral, decoderDisjunction_output .faulty node children shape]
        rfl
      have inputEq : ((children.map (fun child => (decoderPositionBefore .faulty node).slots
          (.internal (.decoder .faulty (parameters.decoder.childIndex node child))))).map (dualLiteral rename)).map negate = children.map labels := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro child member
        simpa only [Function.comp_apply, dualLiteral, negate_negate, labels, output, childLiteral] using child_eq_output rename .faulty node child
      simp only [rootEq, inputEq, List.mem_cons] at member
      exact member.elim (fun same => List.mem_append_right _ (List.mem_append_right _ (List.mem_cons.mpr (Or.inl same))))
        (List.mem_append_left _)
    have included : ∀ child ∈ children, ClauseSubset (supportHeads child) target := by
      intro child listed literal member
      obtain ⟨channel, present, equal⟩ := (heads_member _ _ _).mp member
      apply List.mem_append_right
      apply List.mem_cons_of_mem
      apply (heads_member stored (qualifier rename) literal).mpr
      exact ⟨channel, Finset.mem_biUnion.mpr ⟨child, List.mem_toFinset.mpr listed, present⟩, equal⟩
    let eliminated := eliminate projected.state (cofactor (parameters := parameters) rename) target children labels supportHeads
      (fun child _ => (childEntry table child).summary.afterTrace projected.state projected.steps projected.checked)
      (fun _ member => List.mem_append_left _ member) included parent
    exact ⟨eliminated.state, projected.steps ++ eliminated.steps, by
      rw [runSteps_append, projected.checked]
      exact eliminated.checked, stored, correct, .derived eliminated.result⟩

def guard (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename node.val) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels) :
    NodeStep rename node table := by
  let previous := childEntry table child
  by_cases empty : labels = []
  · subst labels
    have same : output rename node = output rename (parameters.decoder.childIndex node child) := by
      simpa [output, outputLiteral, guardNode_output .faulty node child [] shape, guardCursorAt, childLiteral] using
        child_eq_output rename .faulty node child
    refine ⟨table.prepared.proofPrefix.state, [], rfl, previous.stored, ?_, ?_⟩
    · calc
        previous.stored = support (parameters := parameters) (parameters.decoder.childIndex node child) := previous.exactSupport
        _ = support (parameters := parameters) node := by
          unfold support
          conv_rhs => rw [DecoderSupport.support, shape]
          simp
    · exact Eq.mpr (congrArg (fun literal => Summary table.prepared.proofPrefix.state
        (cofactor (parameters := parameters) rename) literal (heads previous.stored (qualifier rename))) same) previous.summary
  · let start := table.prepared.proofPrefix
    let tree := (nativeGuardTree rename .faulty node child labels shape).afterTrace start.state start.steps start.checked
    have two : 2 ≤ (guardInputs rename .faulty node child labels labels.length).length := by
      simp only [guardInputs, List.take_length, List.length_append, List.length_cons, List.length_nil, List.length_map]
      have positive := List.length_pos_iff.mpr empty
      omega
    let projected := nonunaryTreeInputs tree two
    let live := childLiteral rename .faulty node child
    have inputs : guardInputs rename .faulty node child labels labels.length =
        [live] ++ labels.map (fun channel => negate (qualifier rename channel)) := by
      simp only [guardInputs, List.take_length, live, childLiteral]
      congr 1
      apply List.map_congr_left
      intro channel member
      exact congrArg negate (qualifierAt_eq rename .faulty node channel)
    have rootEq : mapLiteral rename (guardCursorAt .faulty node child labels labels.length).1 = output rename node :=
      (congrArg (mapLiteral rename) (guardNode_output .faulty node child labels shape)).symm
    have childRow : AvailableSubclause projected.state [negate (output rename node), output rename (parameters.decoder.childIndex node child)] := by
      have member : live ∈ guardInputs rename .faulty node child labels labels.length := by rw [inputs]; simp
      simpa only [rootEq, live, child_eq_output, output] using projected.results live member
    have blocked : ∀ channel ∈ labels, AvailableSubclause projected.state
        [negate (output rename node), negate (qualifier rename channel)] := by
      intro channel present
      have member : negate (qualifier rename channel) ∈ guardInputs rename .faulty node child labels labels.length := by
        rw [inputs]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨channel, present, rfl⟩)
      simpa only [rootEq] using projected.results _ member
    by_cases killed : parameters.buses = 1 ∧ parameters.bridge.target ∈ labels
    · let unit := FoldProjection.afterTrace (table.prepared.targetUnit killed.1) projected.state projected.steps projected.checked
      let killedRow := kill projected.state (cofactor (parameters := parameters) rename) (output rename node)
        (qualifier rename parameters.bridge.target) (blocked _ killed.2) unit
      refine ⟨killedRow.state, projected.steps ++ killedRow.steps, ?_, ∅, ?_, .derived ?_⟩
      · rw [runSteps_append, projected.checked]
        exact killedRow.checked
      · unfold support
        rw [DecoderSupport.support, shape]
        simp only [ite_eq_left killed]
      · simpa only [heads_empty] using killedRow.result
    · let target := cofactor (parameters := parameters) rename ++ negate (output rename node) :: heads previous.stored (qualifier rename)
      let parent : AvailableSubclause projected.state (output rename (parameters.decoder.childIndex node child) :: target) :=
        retarget childRow (by
          intro literal member
          simp only [target, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member ⊢
          aesop)
      let expanded := expand projected.state (cofactor (parameters := parameters) rename) target
        (output rename (parameters.decoder.childIndex node child)) (heads previous.stored (qualifier rename))
        (previous.summary.afterTrace projected.state projected.steps projected.checked) parent
        (fun _ member => List.mem_append_left _ member)
        (fun _ member => List.mem_append_right _ (List.mem_cons_of_mem _ member))
      let erased := eraseLabels expanded.state (cofactor (parameters := parameters) rename) (output rename node)
        previous.stored (qualifier rename) labels expanded.result
        (fun channel present => FoldProjection.afterTrace (blocked channel present) expanded.state expanded.steps expanded.checked)
      refine ⟨erased.next, (projected.steps ++ expanded.steps) ++ erased.steps, ?_,
        previous.stored \ labels.toFinset, ?_, .derived erased.result⟩
      · have firstRun : runSteps table.prepared.proofPrefix.state projected.steps = some projected.state := projected.checked
        simp only [runSteps_append, firstRun, Option.bind_some, expanded.checked, erased.checked]
      · unfold support
        rw [DecoderSupport.support, shape]
        simp only [ite_eq_right killed]
        exact congrArg (fun set => set \ labels.toFinset) previous.exactSupport

def step (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (node : Fin parameters.decoder.nodeCount) (table : Table (parameters := parameters) rename node.val) :
    NodeStep rename node table :=
  match shape : parameters.decoder.node node with
  | .zero => zero rename node table shape
  | .input channel => input rename node table channel shape
  | .disj children => disjunction rename node table children shape
  | .guard child labels => guard rename node table child labels shape
  | .liveAnd left right =>
    False.elim (by simpa [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] using guarded node)

def append (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename node.val) (added : NodeStep rename node table) :
    Table (parameters := parameters) rename (node.val + 1) := by
  let next := table.afterTrace added.state added.steps added.checked
  refine ⟨next.prepared, ?_⟩
  intro query before
  by_cases same : query = node
  · subst query
    exact added.entry
  · have earlier : query.val < node.val := by
      have different : query.val ≠ node.val := fun equal => same (Fin.ext equal)
      omega
    exact next.entries query earlier

def build (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (prepared : Preparation (parameters := parameters) rename) :
    (count : Nat) → count ≤ parameters.decoder.nodeCount → Table (parameters := parameters) rename count
  | 0, _ => ⟨prepared, fun node before => False.elim (Nat.not_lt_zero _ before)⟩
  | count + 1, bound =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let table := build rename guarded prepared count (by omega)
    append rename node table (step rename guarded node table)

def allSummaries (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (prepared : Preparation (parameters := parameters) rename) :=
  build rename guarded prepared parameters.decoder.nodeCount (Nat.le_refl _)

def equality (rename : Nat → Fin v) (table : Table (parameters := parameters) rename parameters.decoder.nodeCount)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected)
    (index : Fin parameters.decoder.roots.length) (accepted : index ∈ selected)
    (healthy : parameters.observations index (Controller.assignmentOfSet {parameters.bridge.target}) = false) :
    SourceBusAdvance.PairedProjection table.prepared.proofPrefix.state (cofactor (parameters := parameters) rename)
      (nativeRootLiteral rename .healthy index) (nativeRootLiteral rename .faulty index) 0 := by
  let root := parameters.decoder.roots.get index
  let entry := table.entries root root.isLt
  have semanticEmpty := DecoderSupport.root_support_empty parameters guarded selected absent index accepted healthy
  have storedEmpty : entry.stored = ∅ := entry.exactSupport.trans semanticEmpty
  have summary : Summary table.prepared.proofPrefix.state (cofactor (parameters := parameters) rename) (output rename root) [] := by
    simpa only [storedEmpty, heads_empty] using entry.summary
  have faulty : AvailableSubclause table.prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [negate (nativeRootLiteral rename .faulty index)]) := by
    simpa only [SourceHealthyOneQuery.rootHandle, output] using summary.emptyRow
  have healthyRow : AvailableSubclause table.prepared.proofPrefix.state
      (cofactor (parameters := parameters) rename ++ [negate (nativeRootLiteral rename .healthy index)]) := by
    have bit : parameters.decoder.eval (Controller.assignmentOfSet {parameters.bridge.target}) root = false := healthy
    simpa only [bit, valueLiteral, Bool.false_eq_true, ite_false, SourceHealthyOneQuery.rootHandle] using table.prepared.healthy root
  refine ⟨table.prepared.proofPrefix.state, [], rfl,
    ⟨.derived (retarget healthyRow ?_), .derived (retarget faulty ?_)⟩, by simp⟩
  · intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop
  · intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop

def closedEquality (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) (selected : Finset (Fin parameters.decoder.roots.length))
    (absent : Decoder.NoDiscrepancy parameters selected)
    (index : Fin parameters.decoder.roots.length) (accepted : index ∈ selected)
    (healthy : parameters.observations index (Controller.assignmentOfSet {parameters.bridge.target}) = false) :=
  equality rename (allSummaries rename guarded (prepare rename drive guarded)) guarded selected absent index accepted healthy

def uniformEquality (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (selected : Finset (Fin parameters.decoder.roots.length)) (absent : Decoder.NoDiscrepancy parameters selected)
    (index : Fin parameters.decoder.roots.length) (accepted : index ∈ selected)
    (healthy : parameters.observations index (Controller.assignmentOfSet {parameters.bridge.target}) = false) :
    SourceHealthyOneQuery.EqualityPrefix (parameters := parameters) rename index := by
  by_cases drive : parameters.drive = true
  · let table := allSummaries rename guarded (prepare rename drive guarded)
    let actual := equality rename table guarded selected absent index accepted healthy
    exact ⟨table.prepared.proofPrefix.extend actual.state actual.steps actual.checked, actual.pair⟩
  · have zero : parameters.drive = false := Bool.eq_false_of_not_eq_true drive
    let actual := driveZeroOutputRoot rename zero index
    exact ⟨driveZeroOutputPrefix rename zero,
      ⟨SourceHealthyOneQuery.addContext _ actual.forward, SourceHealthyOneQuery.addContext _ actual.backward⟩⟩

theorem disjunctionSize (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename node.val) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) :
    (disjunction rename node table children shape).steps.length ≤ 4 * sourceDecoderNodeProducerCost parameters node := by
  cases children with
  | nil => simp [disjunction]
  | cons first rest =>
    cases rest with
    | nil => simp [disjunction]
    | cons second rest =>
      dsimp only [disjunction]
      rw [List.length_append]
      apply (Nat.add_le_add (TreeUnits.nonunaryLong _ _).count
        (eliminate _ _ _ _ _ _ _ _ _ _).count).trans
      simp only [AndTree.afterTrace_nodes, List.length_cons]
      have paid := disjunctionTreeCost rename .faulty node (first :: second :: rest) shape (by simp)
      have size := (decoderDisjunctionTree rename .faulty node (first :: second :: rest) shape (by simp)).nodes_leaves
      simp only [List.length_map, List.length_cons] at size
      change (decoderDisjunctionTree rename .faulty node (first :: second :: rest) shape (by simp)).nodes + 1 =
        rest.length + 2 at size
      omega

theorem guardSize (rename : Nat → Fin v) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename node.val) (child : Fin node.val)
    (labels : List (Fin parameters.channels)) (shape : parameters.decoder.node node = .guard child labels) :
    (guard rename node table child labels shape).steps.length ≤ 4 * sourceDecoderNodeProducerCost parameters node := by
  unfold guard
  dsimp only
  split
  · rename_i empty
    subst labels
    simp
  · rename_i nonempty
    split
    · dsimp only
      rw [List.length_append]
      apply (Nat.add_le_add (nonunaryTreeInputs _ _).count (kill _ _ _ _ _ _).count).trans
      simp only [AndTree.afterTrace_nodes]
      have paid := guardTreeCost rename .faulty node child labels shape
      have positive := List.length_pos_iff.mpr nonempty
      have cost : sourceDecoderNodeProducerCost parameters node = labels.length := by
        simp only [sourceDecoderNodeProducerCost, shape, Nat.one_mul]
      omega
    · dsimp only
      simp only [List.length_append]
      apply (Nat.add_le_add
        (Nat.add_le_add (nonunaryTreeInputs _ _).count (expand _ _ _ _ _ _ _ _ _).count)
        (eraseLabels _ _ _ _ _ _ _ _).count).trans
      simp only [AndTree.afterTrace_nodes]
      have paid := guardTreeCost rename .faulty node child labels shape
      have positive := List.length_pos_iff.mpr nonempty
      have cost : sourceDecoderNodeProducerCost parameters node = labels.length := by
        simp only [sourceDecoderNodeProducerCost, shape, Nat.one_mul]
      omega

theorem stepSize (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (node : Fin parameters.decoder.nodeCount) (table : Table (parameters := parameters) rename node.val) :
    (step rename guarded node table).steps.length ≤ 4 * sourceDecoderNodeProducerCost parameters node := by
  unfold step
  split
  · simp [zero]
  · simp [input]
  · exact disjunctionSize _ _ _ _ _
  · exact guardSize _ _ _ _ _ _
  · next left right shape =>
    exact False.elim (by simpa [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] using guarded node)

theorem buildSize (rename : Nat → Fin v) (guarded : parameters.decoder.Guarded)
    (prepared : Preparation (parameters := parameters) rename)
    (count : Nat) (bound : count ≤ parameters.decoder.nodeCount) :
    (build rename guarded prepared count bound).prepared.proofPrefix.steps.length ≤
      prepared.proofPrefix.steps.length + 4 * evaluationPrefixCost parameters count := by
  induction count with
  | zero => simp [build, evaluationPrefixCost]
  | succ count ih =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let previous := build rename guarded prepared count (by omega)
    have old := ih (by omega)
    change previous.prepared.proofPrefix.steps.length ≤ prepared.proofPrefix.steps.length +
      4 * evaluationPrefixCost parameters count at old
    have current := stepSize rename guarded node previous
    change (previous.prepared.proofPrefix.steps ++ (step rename guarded node previous).steps).length ≤ _
    rw [List.length_append]
    have next := evaluationPrefixCost_succ parameters node
    change evaluationPrefixCost parameters (count + 1) =
      evaluationPrefixCost parameters count + sourceDecoderNodeProducerCost parameters node at next
    omega

end Controller.NativeProof.SourceSupportSummaries
