module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceHealthyQualifiers

@[expose] public section

/-! Unit evaluation follows the stored source DAG in increasing node order.
Every child unit is read from the shared table; aliases reuse the existing row. -/
namespace Controller.NativeProof.SourceDecoderEvaluation
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceStageXor Controller.NativeProof.SourceFoldOccurrences
open Controller.NativeProof.SourceDecoderTraversal Controller.NativeProof.SourceDecoderSchedule
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceQualifierSchedule
variable {parameters : Parameters} {v : Nat}

def pick {α : Type} (items : List α) (predicate : α → Prop) [DecidablePred predicate]
    (witness : ∃ item ∈ items, predicate item) : {item // item ∈ items ∧ predicate item} :=
  match items with
  | [] => False.elim (by simpa using witness)
  | item :: rest => by
    by_cases held : predicate item
    · exact ⟨item, List.mem_cons_self, held⟩
    · let tail := pick rest predicate (by
        obtain ⟨selected, present, satisfies⟩ := witness
        refine ⟨selected, ?_, satisfies⟩
        exact (List.mem_cons.mp present).resolve_left (fun same => held (same ▸ satisfies)))
      exact ⟨tail.val, List.mem_cons_of_mem _ tail.property.1, tail.property.2⟩

def nodeBit (assignment : Controller.Assignment parameters.channels)
    (node : Fin parameters.decoder.nodeCount) := parameters.decoder.eval assignment node

def qualifierLiteral (rename : Nat → Fin v) (side : Side) (channel : Fin parameters.channels) :=
  mapLiteral rename ((decoderStart (parameters := parameters) side).slots (.internal (.qualifier side channel)))

structure Table (rename : Nat → Fin v) (side : Side)
    (context : Clause (Fin v)) (assignment : Controller.Assignment parameters.channels) (count : Nat) where
  proofPrefix : SourcePrefix (parameters := parameters) rename
  qualifiers : ∀ channel, AvailableSubclause proofPrefix.state
    (context ++ [valueLiteral (qualifierLiteral rename side channel) (assignment channel)])
  nodes : ∀ node : Fin parameters.decoder.nodeCount, node.val < count →
    AvailableSubclause proofPrefix.state
      (context ++ [valueLiteral (decoderStoredLiteral rename side count node) (nodeBit assignment node)])

def Table.afterTrace (table : Table (parameters := parameters) rename side context assignment count)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.proofPrefix.state steps = some next) :
    Table (parameters := parameters) rename side context assignment count where
  proofPrefix := table.proofPrefix.extend next steps checked
  qualifiers channel := FoldProjection.afterTrace (table.qualifiers channel) next steps checked
  nodes node before := FoldProjection.afterTrace (table.nodes node before) next steps checked

def outputLiteral (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount) :=
  mapLiteral rename ((decoderNode parameters side node (decoderPositionBefore side node)).slots
    (.internal (.decoder side node)))

def childLiteral (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (child : Fin node.val) := mapLiteral rename ((decoderPositionBefore side node).slots
      (.internal (.decoder side (parameters.decoder.childIndex node child))))

def childUnit (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val) (child : Fin node.val) :
    AvailableSubclause table.proofPrefix.state
      (context ++ [valueLiteral (childLiteral rename side node child)
        (nodeBit assignment (parameters.decoder.childIndex node child))]) := by
  simpa only [childLiteral, decoderStoredLiteral, decoderCursorAt_before] using
    table.nodes (parameters.decoder.childIndex node child) (parameters.decoder.childIndex_lt node child)

structure NodeStep (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (assignment : Controller.Assignment parameters.channels) (node : Fin parameters.decoder.nodeCount)
    (start : Table (parameters := parameters) rename side context assignment node.val) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.proofPrefix.state steps = some state
  result : AvailableSubclause state (context ++ [valueLiteral (outputLiteral rename side node) (nodeBit assignment node)])

def zero (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val)
    (shape : parameters.decoder.node node = .zero) : NodeStep rename side context assignment node table := by
  have unit := decoderZeroUnit rename side node shape table.proofPrefix
  have bit : nodeBit assignment node = false := parameters.decoder.eval_zero assignment node shape
  have output : outputLiteral rename side node = mapLiteral rename (decoderLiveAndOutput side node) := by
    simp only [outputLiteral, decoderZero_output side node _ shape]
    rfl
  refine ⟨table.proofPrefix.state, [], rfl, ?_⟩
  simp only [bit, valueLiteral, Bool.false_eq_true, ite_false, output]
  exact retarget unit (fun _ member => List.mem_append_right _ member)

def input (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val)
    (channel : Fin parameters.channels) (shape : parameters.decoder.node node = .input channel) :
    NodeStep rename side context assignment node table := by
  have bit : nodeBit assignment node = assignment channel := parameters.decoder.eval_input assignment node channel shape
  have output : outputLiteral rename side node = qualifierLiteral rename side channel := by
    simp only [outputLiteral, decoderInput_output side node channel _ shape,
      ← decoderCursorAt_before, decoderCursorAt_qualifier, qualifierLiteral]
  exact ⟨table.proofPrefix.state, [], rfl, by simpa only [bit, output] using table.qualifiers channel⟩

def disjunction (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children) :
    NodeStep rename side context assignment node table := by
  by_cases empty : children = []
  · subst children
    have bit : nodeBit assignment node = false := by
      simp only [nodeBit, parameters.decoder.eval_disj assignment node [] shape, List.any_nil]
    have unit := decoderEmptyDisjunctionUnit rename side node shape table.proofPrefix
    have output : outputLiteral rename side node = mapLiteral rename (decoderLiveAndOutput side node) := by
      simp [outputLiteral, decoderNode, shape, Cursor.foldNative, Cursor.assign,
        decoderLiveAndOutput, SourceSerialFold.allocate]
    exact ⟨table.proofPrefix.state, [], rfl, by
      simp only [bit, output, valueLiteral, Bool.false_eq_true, ite_false]
      exact retarget unit (fun _ member => List.mem_append_right _ member)⟩
  · let tree := (decoderDisjunctionTree rename side node children shape empty).afterTrace
      table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
    have output : outputLiteral rename side node = mapLiteral rename (decoderDisjunctionOutput side node children) := by
      simp only [outputLiteral, decoderDisjunction_output side node children shape]
    have bits : nodeBit assignment node = children.any (fun child => nodeBit assignment (parameters.decoder.childIndex node child)) :=
      parameters.decoder.eval_disj assignment node children shape
    by_cases active : nodeBit assignment node = true
    · have someChild : ∃ child ∈ children, nodeBit assignment (parameters.decoder.childIndex node child) = true := by
        rw [bits] at active
        exact List.any_eq_true.mp active
      let selected := pick children (fun child => nodeBit assignment (parameters.decoder.childIndex node child) = true) someChild
      let leaf := negate (childLiteral rename side node selected.val)
      have member : leaf ∈ (children.map (fun child => (decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child))))).map (dualLiteral rename) :=
        List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨selected.val, selected.property.1, rfl⟩, rfl⟩
      have unit : AvailableSubclause table.proofPrefix.state (context ++ [negate leaf]) := by
        simpa only [selected.property.2, valueLiteral, ite_true, leaf, negate_negate] using childUnit rename side node table selected.val
      let denied := TreeUnits.deny tree context leaf member unit
      exact ⟨denied.state, denied.steps, denied.checked, by
        simpa only [active, valueLiteral, ite_true, output, dualLiteral, negate_negate, decoderDisjunctionOutput] using denied.result⟩
    · have inactive : nodeBit assignment node = false := Bool.eq_false_of_not_eq_true active
      have childrenFalse : ∀ child ∈ children, nodeBit assignment (parameters.decoder.childIndex node child) = false := by
        rw [bits] at inactive
        intro child present
        exact Bool.eq_false_of_not_eq_true (List.any_eq_false.mp inactive child present)
      have units : ∀ leaf ∈ (children.map (fun child => (decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child))))).map (dualLiteral rename),
          AvailableSubclause table.proofPrefix.state (context ++ [leaf]) := by
        intro leaf listed
        have member : leaf ∈ children.map (fun child => negate (childLiteral rename side node child)) := by
          simpa only [List.map_map, childLiteral, dualLiteral, Function.comp_def] using listed
        exact TreeUnits.mappedUnit children _ context (fun child present => by
          simpa only [childrenFalse child present, valueLiteral, Bool.false_eq_true, ite_false] using
            childUnit rename side node table child) leaf member
      let forced := TreeUnits.force tree context units
      exact ⟨forced.state, forced.steps, forced.checked, by
        simpa only [inactive, valueLiteral, Bool.false_eq_true, ite_false, output, dualLiteral, decoderDisjunctionOutput] using forced.result⟩

def qualifierAt (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val)
    (channel : Fin parameters.channels) :
    AvailableSubclause table.proofPrefix.state (context ++ [valueLiteral
      (mapLiteral rename ((decoderPositionBefore side node).slots (.internal (.qualifier side channel))))
      (assignment channel)]) := by
  simpa only [← decoderCursorAt_before, decoderCursorAt_qualifier, qualifierLiteral] using table.qualifiers channel

def guard (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val)
    (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    NodeStep rename side context assignment node table := by
  let tree := (nativeGuardTree rename side node child labels shape).afterTrace
    table.proofPrefix.state table.proofPrefix.steps table.proofPrefix.checked
  let live := childLiteral rename side node child
  let blocked := fun channel => negate (mapLiteral rename
    ((decoderPositionBefore side node).slots (.internal (.qualifier side channel))))
  have inputs : guardInputs rename side node child labels labels.length = [live] ++ labels.map blocked := by
    simp only [guardInputs, List.take_length, live, blocked, childLiteral]
  have output : outputLiteral rename side node = mapLiteral rename (guardCursorAt side node child labels labels.length).1 := by
    simp only [outputLiteral, guardNode_output side node child labels shape]
  have bits : nodeBit assignment node =
      (nodeBit assignment (parameters.decoder.childIndex node child) && !(labels.any assignment)) :=
    parameters.decoder.eval_guard assignment node child labels shape
  by_cases active : nodeBit assignment node = true
  · have conditions : nodeBit assignment (parameters.decoder.childIndex node child) = true ∧
        labels.any assignment = false := by
      rw [bits] at active
      simpa only [Bool.and_eq_true, Bool.not_eq_true'] using active
    have units : ∀ leaf ∈ guardInputs rename side node child labels labels.length,
        AvailableSubclause table.proofPrefix.state (context ++ [leaf]) := by
      intro leaf member
      rw [inputs] at member
      by_cases same : leaf = live
      · subst leaf
        simpa only [conditions.1, valueLiteral, ite_true] using childUnit rename side node table child
      · have guards : leaf ∈ labels.map blocked := (List.mem_cons.mp member).resolve_left same
        exact TreeUnits.mappedUnit labels blocked context (fun channel present => by
          have falseBit : assignment channel = false :=
            Bool.eq_false_of_not_eq_true (List.any_eq_false.mp conditions.2 channel present)
          simpa only [falseBit, valueLiteral, Bool.false_eq_true, ite_false, blocked] using qualifierAt rename side node table channel) leaf guards
    let forced := TreeUnits.force tree context units
    exact ⟨forced.state, forced.steps, forced.checked, by simpa only [active, valueLiteral, ite_true, output] using forced.result⟩
  · have inactive : nodeBit assignment node = false := Bool.eq_false_of_not_eq_true active
    by_cases childFalse : nodeBit assignment (parameters.decoder.childIndex node child) = false
    · have member : live ∈ guardInputs rename side node child labels labels.length := by rw [inputs]; simp
      have unit : AvailableSubclause table.proofPrefix.state (context ++ [negate live]) := by
        simpa only [childFalse, valueLiteral, Bool.false_eq_true, ite_false] using childUnit rename side node table child
      let denied := TreeUnits.deny tree context live member unit
      exact ⟨denied.state, denied.steps, denied.checked, by
        simpa only [inactive, valueLiteral, Bool.false_eq_true, ite_false, output] using denied.result⟩
    · have labelTrue : labels.any assignment = true := by
        have childTrue := Bool.eq_true_of_not_eq_false childFalse
        rw [bits, childTrue] at inactive
        simpa using inactive
      let selected := pick labels (fun channel => assignment channel = true) (List.any_eq_true.mp labelTrue)
      let leaf := blocked selected.val
      have member : leaf ∈ guardInputs rename side node child labels labels.length := by
        rw [inputs]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨selected.val, selected.property.1, rfl⟩)
      have unit : AvailableSubclause table.proofPrefix.state (context ++ [negate leaf]) := by
        simpa only [selected.property.2, valueLiteral, ite_true, leaf, blocked, negate_negate] using
          qualifierAt rename side node table selected.val
      let denied := TreeUnits.deny tree context leaf member unit
      exact ⟨denied.state, denied.steps, denied.checked, by
        simpa only [inactive, valueLiteral, Bool.false_eq_true, ite_false, output] using denied.result⟩

def step (rename : Nat → Fin v) (side : Side) (guarded : parameters.decoder.Guarded)
    (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val) :
    NodeStep rename side context assignment node table :=
  match shape : parameters.decoder.node node with
  | .zero => zero rename side node table shape
  | .input channel => input rename side node table channel shape
  | .disj children => disjunction rename side node table children shape
  | .guard child labels => guard rename side node table child labels shape
  | .liveAnd left right =>
    False.elim (by simpa [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] using guarded node)

def append (rename : Nat → Fin v) (side : Side) (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val)
    (added : NodeStep rename side context assignment node table) :
    Table (parameters := parameters) rename side context assignment (node.val + 1) := by
  let next := table.afterTrace added.state added.steps added.checked
  refine ⟨next.proofPrefix, next.qualifiers, ?_⟩
  intro query before
  by_cases same : query = node
  · subst query
    simpa only [decoderStoredLiteral_self, outputLiteral, next, Table.afterTrace, SourcePrefix.extend] using added.result
  · have earlier : query.val < node.val := by
      have different : query.val ≠ node.val := fun equal => same (Fin.ext equal)
      omega
    simpa only [decoderStoredLiteral_old rename side node query earlier] using next.nodes query earlier

def build (rename : Nat → Fin v) (side : Side) (guarded : parameters.decoder.Guarded)
    (seed : Table (parameters := parameters) rename side context assignment 0) :
    (count : Nat) → count ≤ parameters.decoder.nodeCount →
      Table (parameters := parameters) rename side context assignment count
  | 0, _ => seed
  | count + 1, bound =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let table := build rename side guarded seed count (by omega)
    append rename side node table (step rename side guarded node table)

def healthySeed (rename : Nat → Fin v) (drive : parameters.drive = true) :
    Table (parameters := parameters) rename .healthy (SourceHealthyMasks.context (parameters := parameters) rename)
      (Controller.assignmentOfSet {parameters.bridge.target}) 0 := by
  let bank := SourceHealthyQualifiers.allQualifiers rename drive
  refine ⟨bank.table.proofPrefix, ?_, fun node before => False.elim (Nat.not_lt_zero _ before)⟩
  intro channel
  have row := bank.rows channel (List.mem_finRange _)
  have bit : Controller.assignmentOfSet {parameters.bridge.target} channel = decide (channel = parameters.bridge.target) := by
    simp [Controller.assignmentOfSet]
  simpa only [bit, qualifierLiteral, ← qualifierOutput_decoderStart] using row

def healthy (rename : Nat → Fin v) (drive : parameters.drive = true) (guarded : parameters.decoder.Guarded) :
    Table (parameters := parameters) rename .healthy (SourceHealthyMasks.context (parameters := parameters) rename)
      (Controller.assignmentOfSet {parameters.bridge.target}) parameters.decoder.nodeCount :=
  build rename .healthy guarded (healthySeed rename drive) _ (Nat.le_refl _)

def rootUnit (rename : Nat → Fin v) (side : Side)
    (table : Table (parameters := parameters) rename side context assignment parameters.decoder.nodeCount)
    (output : Fin parameters.decoder.roots.length) :
    AvailableSubclause table.proofPrefix.state (context ++ [valueLiteral (nativeRootLiteral rename side output)
      (parameters.observations output assignment)]) := by
  let root := parameters.decoder.roots[output.val]
  have row := table.nodes root root.isLt
  have handle : nativeRootLiteral rename side output = decoderStoredLiteral rename side parameters.decoder.nodeCount root := by
    simp only [nativeRootLiteral, compiled_decoder_slot, decoderComplete_slot, decoderStoredLiteral, root]
  simpa only [handle, nodeBit, Parameters.observations, root, List.get_eq_getElem] using row

theorem stored_eq_output (rename : Nat → Fin v) (side : Side)
    (count : Nat) (bound : count ≤ parameters.decoder.nodeCount)
    (query : Fin parameters.decoder.nodeCount) (before : query.val < count) :
    decoderStoredLiteral rename side count query = outputLiteral rename side query := by
  induction count generalizing query with
  | zero => omega
  | succ count ih =>
    let current : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    by_cases same : query = current
    · have base : decoderStoredLiteral rename side (count + 1) current = outputLiteral rename side current :=
        decoderStoredLiteral_self rename side current
      exact (congrArg (decoderStoredLiteral rename side (count + 1)) same).trans
        (base.trans (congrArg (outputLiteral rename side) same.symm))
    · have earlier : query.val < count := by
        have different : query.val ≠ count := fun equal => same (Fin.ext equal)
        omega
      have frame := decoderStoredLiteral_old rename side current query earlier
      exact frame.trans (ih (by omega) query earlier)

theorem child_eq_output (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val) :
    childLiteral rename side node child = outputLiteral rename side (parameters.decoder.childIndex node child) := by
  exact stored_eq_output rename side node.val (Nat.le_of_lt node.isLt)
    (parameters.decoder.childIndex node child) child.isLt

theorem qualifierAt_eq (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (channel : Fin parameters.channels) :
    mapLiteral rename ((decoderPositionBefore side node).slots (.internal (.qualifier side channel))) =
      qualifierLiteral rename side channel := by
  simp only [← decoderCursorAt_before, decoderCursorAt_qualifier, qualifierLiteral]

theorem disjunctionTreeCost (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children) (nonempty : children ≠ []) :
    (decoderDisjunctionTree rename side node children shape nonempty).nodes =
      sourceDecoderNodeProducerCost parameters node := by
  have counted := (decoderDisjunctionTree rename side node children shape nonempty).nodes_leaves
  simp only [List.length_map] at counted
  change (decoderDisjunctionTree rename side node children shape nonempty).nodes + 1 = children.length at counted
  have positive := List.length_pos_iff.mpr nonempty
  simp only [sourceDecoderNodeProducerCost, shape, sourceFoldProducerCount, ite_eq_right (Nat.ne_of_gt positive)]
  omega

theorem guardTreeCost (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount) (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    (nativeGuardTree rename side node child labels shape).nodes = sourceDecoderNodeProducerCost parameters node := by
  have counted := (nativeGuardTree rename side node child labels shape).nodes_leaves
  simp only [guardInputs, List.take_length, List.length_append, List.length_cons, List.length_nil, List.length_map] at counted
  change (nativeGuardTree rename side node child labels shape).nodes + 1 = 1 + labels.length at counted
  simp only [sourceDecoderNodeProducerCost, shape]
  omega

theorem disjunctionSize (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children) :
    (disjunction rename side node table children shape).steps.length ≤
      4 * sourceDecoderNodeProducerCost parameters node := by
  unfold disjunction
  split
  · rename_i empty
    subst children
    simp
  · rename_i nonempty
    dsimp only
    split
    · dsimp only
      apply (TreeUnits.deny_count_nodes _ _ _ _ _).trans
      simp only [AndTree.afterTrace_nodes]
      have paid := disjunctionTreeCost rename side node children shape nonempty
      omega
    · dsimp only
      apply (TreeUnits.force_count_nodes _ _ _).trans
      simp only [AndTree.afterTrace_nodes]
      exact Nat.mul_le_mul_left 4 (Nat.le_of_eq (disjunctionTreeCost rename side node children shape nonempty))

theorem guardSize (rename : Nat → Fin v) (side : Side)
    (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val)
    (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    (guard rename side node table child labels shape).steps.length ≤
      4 * sourceDecoderNodeProducerCost parameters node := by
  unfold guard
  dsimp only
  split
  · dsimp only
    apply (TreeUnits.force_count_nodes _ _ _).trans
    simp only [AndTree.afterTrace_nodes]
    exact Nat.mul_le_mul_left 4 (Nat.le_of_eq (guardTreeCost rename side node child labels shape))
  · split
    all_goals
      dsimp only
      apply (TreeUnits.deny_count_nodes _ _ _ _ _).trans
      simp only [AndTree.afterTrace_nodes]
      have paid := guardTreeCost rename side node child labels shape
      omega

theorem stepSize (rename : Nat → Fin v) (side : Side) (guarded : parameters.decoder.Guarded)
    (node : Fin parameters.decoder.nodeCount)
    (table : Table (parameters := parameters) rename side context assignment node.val) :
    (step rename side guarded node table).steps.length ≤ 4 * sourceDecoderNodeProducerCost parameters node := by
  unfold step
  split
  · simp [zero]
  · simp [input]
  · exact disjunctionSize _ _ _ _ _ _
  · exact guardSize _ _ _ _ _ _ _
  · next left right shape =>
    exact False.elim (by simpa [Decoder.Gate.IsGuarded, shape, Decoder.Gate.isLiveAnd] using guarded node)

def evaluationPrefixCost (parameters : Parameters) (count : Nat) : Nat :=
  (((List.finRange parameters.decoder.nodeCount).take count).map
    (sourceDecoderNodeProducerCost parameters)).sum

theorem evaluationPrefixCost_succ (parameters : Parameters) (node : Fin parameters.decoder.nodeCount) :
    evaluationPrefixCost parameters (node.val + 1) =
      evaluationPrefixCost parameters node.val + sourceDecoderNodeProducerCost parameters node := by
  unfold evaluationPrefixCost
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using node.isLt),
    List.map_append, List.sum_append]
  simp only [List.getElem_finRange, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

theorem buildSize (rename : Nat → Fin v) (side : Side) (guarded : parameters.decoder.Guarded)
    (seed : Table (parameters := parameters) rename side context assignment 0)
    (count : Nat) (bound : count ≤ parameters.decoder.nodeCount) :
    (build rename side guarded seed count bound).proofPrefix.steps.length ≤
      seed.proofPrefix.steps.length + 4 * evaluationPrefixCost parameters count := by
  induction count with
  | zero => simp [build, evaluationPrefixCost]
  | succ count ih =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let previous := build rename side guarded seed count (by omega)
    have old := ih (by omega)
    change previous.proofPrefix.steps.length ≤ seed.proofPrefix.steps.length +
      4 * evaluationPrefixCost parameters count at old
    have current := stepSize rename side guarded node previous
    change (previous.proofPrefix.steps ++ (step rename side guarded node previous).steps).length ≤ _
    rw [List.length_append]
    have next := evaluationPrefixCost_succ parameters node
    change evaluationPrefixCost parameters (count + 1) =
      evaluationPrefixCost parameters count + sourceDecoderNodeProducerCost parameters node at next
    omega

theorem healthySize (rename : Nat → Fin v) (drive : parameters.drive = true)
    (guarded : parameters.decoder.Guarded) :
    (healthy rename drive guarded).proofPrefix.steps.length ≤
      (healthySeed rename drive).proofPrefix.steps.length + 4 * sourceDecoderProducerCost parameters := by
  have actual := buildSize rename .healthy guarded (healthySeed rename drive)
    parameters.decoder.nodeCount (Nat.le_refl _)
  unfold evaluationPrefixCost at actual
  rw [List.take_of_length_le (by simp)] at actual
  exact actual

end Controller.NativeProof.SourceDecoderEvaluation
