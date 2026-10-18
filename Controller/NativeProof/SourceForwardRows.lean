module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceDecoderEvaluation
public import Controller.NativeProof.Decoder
public import Controller.NativeProof.HornNativeReplay

@[expose] public section

/-! The forward zero-system rows are materialized from concrete source
decoder occurrences. Literal-identity implications retain an explicit alias
certificate and contribute no invented resolution parent. -/
namespace Controller.NativeProof.SourceForwardRows
open Controller.CNF Controller.Resolution Controller.Native Controller.Native.SourceController
open Controller.Decoder.ZeroSystem
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceFoldProjection
open Controller.NativeProof.SourceStageCongruence Controller.NativeProof.SourceStagePolarity
open Controller.NativeProof.SourceFoldOccurrences Controller.NativeProof.SourceStageXor
open Controller.NativeProof.SourceDecoderTraversal Controller.NativeProof.SourceDecoderSchedule
open Controller.NativeProof.SourceDecoderClauses Controller.NativeProof.SourceDecoderEvaluation
variable {parameters : Parameters} {v : Nat}

def handle (rename : Nat → Fin v) (side : Side) : parameters.decoder.ZeroVar → Literal (Fin v) :=
  Sum.elim (qualifierLiteral rename side) (outputLiteral rename side)

def literal (rename : Nat → Fin v) (side : Side) (entry : Literal parameters.decoder.ZeroVar) : Literal (Fin v) :=
  if entry.2 then handle rename side entry.1 else negate (handle rename side entry.1)

def clause (rename : Nat → Fin v) (side : Side) (row : Clause parameters.decoder.ZeroVar) : Clause (Fin v) :=
  row.map (literal rename side)

@[simp] theorem implication (rename : Nat → Fin v) (side : Side)
    (premise : parameters.decoder.ZeroVar) (alternatives : List parameters.decoder.ZeroVar) :
    clause rename side (implicationClause premise alternatives) =
      negate (handle rename side premise) :: alternatives.map (handle rename side) := by
  simp [clause, literal, implicationClause, positiveClause, List.map_map, Function.comp_def]

inductive Origin (rename : Nat → Fin v) (side : Side) (state : State v)
    (context : Clause (Fin v)) (row : Clause parameters.decoder.ZeroVar) : Type
  | native (available : AvailableSubclause state (context ++ clause rename side row))
  | identity (premise conclusion : parameters.decoder.ZeroVar)
      (shape : row = implicationClause premise [conclusion])
      (same : handle rename side premise = handle rename side conclusion)

def Origin.afterTrace (origin : Origin (parameters := parameters) rename side state context row)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    Origin (parameters := parameters) rename side next context row :=
  match origin with
  | .native available => .native (FoldProjection.afterTrace available next steps checked)
  | .identity premise conclusion shape same => .identity premise conclusion shape same

structure NodeRows (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename) where
  state : State v
  steps : List (Step v)
  checked : runSteps start.state steps = some state
  rows : ∀ row ∈ parameters.decoder.nodeClauses node,
    Origin (parameters := parameters) rename side state context row

def zero (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (shape : parameters.decoder.node node = .zero) : NodeRows rename side context node start := by
  refine ⟨start.state, [], rfl, ?_⟩
  intro row present
  have same : row = implicationClause (.inr node) [] := by simpa [Controller.Decoder.DAG.nodeClauses, shape] using present
  subst row
  apply Origin.native
  have unit := decoderZeroUnit rename side node shape start
  have output : outputLiteral rename side node = mapLiteral rename (decoderLiveAndOutput side node) := by
    simp only [outputLiteral, decoderZero_output side node _ shape]
    rfl
  simpa only [implication, List.map_nil, handle, Sum.elim_inr, output] using
    retarget unit (fun _ member => List.mem_append_right context member)

def input (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (channel : Fin parameters.channels) (shape : parameters.decoder.node node = .input channel) :
    NodeRows rename side context node start := by
  have same : handle rename side (.inl channel) = handle rename side (.inr node) := by
    simp only [handle, Sum.elim_inl, Sum.elim_inr, outputLiteral, decoderInput_output side node channel _ shape,
      qualifierAt_eq rename side node channel]
  refine ⟨start.state, [], rfl, ?_⟩
  intro row present
  by_cases first : row = implicationClause (.inl channel) [.inr node]
  · exact .identity (.inl channel) (.inr node) first same
  · have second : row = implicationClause (.inr node) [.inl channel] := by
      simpa only [Controller.Decoder.DAG.nodeClauses, shape, List.mem_cons, List.not_mem_nil, or_false] using
        (show row = implicationClause (.inr node) [.inl channel] from by
          simpa [Controller.Decoder.DAG.nodeClauses, shape, first] using present)
    exact .identity (.inr node) (.inl channel) second same.symm

def mapDirectionalCertificate {rename : Nat → Fin v} {side : Side} {state : State v}
    {context : Clause (Fin v)} {row : Clause parameters.decoder.ZeroVar}
    {root input : Literal (Fin v)} (certificate : DirectionalCertificate state root input)
    (identity : root = input → Origin (parameters := parameters) rename side state context row)
    (derived : AvailableSubclause state [negate root, input] → Origin (parameters := parameters) rename side state context row) :
    Origin (parameters := parameters) rename side state context row :=
  match (generalizing := false) certificate with
  | .identity same => identity same
  | .derived available => derived available

def disjunctionSelection (node : Fin parameters.decoder.nodeCount) (children : List (Fin node.val))
    (shape : parameters.decoder.node node = .disj children)
    (row : Clause parameters.decoder.ZeroVar) (present : row ∈ parameters.decoder.nodeClauses node) :
    {child // child ∈ children ∧ row = implicationClause (.inr (parameters.decoder.childIndex node child)) [.inr node]} :=
  pick children (fun child => row = implicationClause (.inr (parameters.decoder.childIndex node child)) [.inr node])
    (by simpa [Controller.Decoder.DAG.nodeClauses, shape, List.mem_map, eq_comm] using present)

def disjunction (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children) :
    NodeRows rename side context node start := by
  by_cases empty : children = []
  · subst children
    exact ⟨start.state, [], rfl, fun row present => False.elim (by simpa [Controller.Decoder.DAG.nodeClauses, shape] using present)⟩
  · let tree := (decoderDisjunctionTree rename side node children shape empty).afterTrace start.state start.steps start.checked
    let projected := projectTreeInputs tree
    refine ⟨projected.state, projected.steps, projected.checked, ?_⟩
    intro row present
    let selected := disjunctionSelection node children shape row present
    let leaf := negate (childLiteral rename side node selected.val)
    have listed : leaf ∈ (children.map (fun child => (decoderPositionBefore side node).slots
        (.internal (.decoder side (parameters.decoder.childIndex node child))))).map (dualLiteral rename) :=
      List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨selected.val, selected.property.1, rfl⟩, rfl⟩
    have output : mapLiteral rename (SourceSerialFold.allocate .disjunction (decoderPositionBefore side node).lastID
        (children.map (fun child => (decoderPositionBefore side node).slots
          (.internal (.decoder side (parameters.decoder.childIndex node child)))))).output = outputLiteral rename side node :=
      (congrArg (mapLiteral rename) (decoderDisjunction_output side node children shape)).symm
    apply mapDirectionalCertificate (projected.results leaf listed)
    · intro equal
      apply Origin.identity (.inr (parameters.decoder.childIndex node selected.val)) (.inr node) selected.property.2
      have same : negate (outputLiteral rename side node) = negate (childLiteral rename side node selected.val) := by
        simpa only [leaf, dualLiteral, output] using equal
      simpa only [handle, Sum.elim_inr, child_eq_output, negate_negate] using (congrArg negate same).symm
    · intro available
      apply Origin.native
      apply retarget available
      intro lit member
      have target : clause rename side row = [negate (childLiteral rename side node selected.val), outputLiteral rename side node] := by
        calc
          clause rename side row = clause rename side
              (implicationClause (.inr (parameters.decoder.childIndex node selected.val)) [.inr node]) :=
            congrArg (clause rename side) selected.property.2
          _ = _ := by simp only [implication, handle, Sum.elim_inr, List.map_cons, List.map_nil, child_eq_output]
      rw [target]
      simp only [leaf, dualLiteral, output, negate_negate, List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      aesop


def guard (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) : NodeRows rename side context node start := by
  by_cases empty : labels = []
  · subst labels
    have same : handle rename side (.inr (parameters.decoder.childIndex node child)) = handle rename side (.inr node) := by
      have output : outputLiteral rename side node = childLiteral rename side node child := by
        simp [outputLiteral, guardNode_output side node child [] shape, guardCursorAt, childLiteral]
      simpa only [handle, Sum.elim_inr, child_eq_output] using output.symm
    refine ⟨start.state, [], rfl, ?_⟩
    intro row present
    have clauseEq : row = implicationClause (.inr (parameters.decoder.childIndex node child)) [.inr node] := by
      simpa [Controller.Decoder.DAG.nodeClauses, shape] using present
    exact .identity (.inr (parameters.decoder.childIndex node child)) (.inr node) clauseEq same
  · let tree := (nativeGuardTree rename side node child labels shape).afterTrace start.state start.steps start.checked
    have two : 2 ≤ (guardInputs rename side node child labels labels.length).length := by
      simp only [guardInputs, List.take_length, List.length_append, List.length_cons, List.length_nil, List.length_map]
      have positive := List.length_pos_iff.mpr empty
      omega
    let projected := TreeUnits.nonunaryLong tree two
    refine ⟨projected.state, projected.steps, projected.checked, ?_⟩
    intro row present
    have clauseEq : row = implicationClause (.inr (parameters.decoder.childIndex node child))
        (labels.map Sum.inl ++ [.inr node]) := by
      simpa [Controller.Decoder.DAG.nodeClauses, shape] using present
    apply Origin.native
    have mapped : clause rename side row = negate (childLiteral rename side node child) ::
        (labels.map (qualifierLiteral rename side) ++ [outputLiteral rename side node]) := by
      calc
        clause rename side row = clause rename side (implicationClause (.inr (parameters.decoder.childIndex node child))
          (labels.map Sum.inl ++ [.inr node])) := congrArg (clause rename side) clauseEq
        _ = _ := by simp only [implication, handle, Sum.elim_inr, Sum.elim_inl, List.map_append,
          List.map_map, List.map_cons, List.map_nil, child_eq_output, Function.comp_def]
    apply retarget projected.result
    intro lit member
    rw [mapped]
    have output : mapLiteral rename (guardCursorAt side node child labels labels.length).1 = outputLiteral rename side node :=
      (congrArg (mapLiteral rename) (guardNode_output side node child labels shape)).symm
    have inputs : (guardInputs rename side node child labels labels.length).map negate =
        negate (childLiteral rename side node child) :: labels.map (qualifierLiteral rename side) := by
      simp only [guardInputs, List.take_length, List.map_append, List.map_cons, List.map_nil, List.map_map,
        List.cons_append, List.nil_append, childLiteral, negate_negate, qualifierAt_eq, Function.comp_def]
    simp only [output, inputs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member ⊢
    aesop

def nodeRows (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (node : Fin parameters.decoder.nodeCount)
    (start : SourcePrefix (parameters := parameters) rename) : NodeRows rename side context node start :=
  match shape : parameters.decoder.node node with
  | .zero => zero rename side context node start shape
  | .input channel => input rename side context node start channel shape
  | .disj children => disjunction rename side context node start children shape
  | .guard child labels => guard rename side context node start child labels shape
  | .liveAnd left right =>
    False.elim (by simpa [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] using guarded node)

structure Table (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v)) (count : Nat) where
  proofPrefix : SourcePrefix (parameters := parameters) rename
  rows : ∀ node : Fin parameters.decoder.nodeCount, node.val < count →
    ∀ row ∈ parameters.decoder.nodeClauses node, Origin (parameters := parameters) rename side proofPrefix.state context row

def append (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (table : Table (parameters := parameters) rename side context node.val)
    (added : NodeRows rename side context node table.proofPrefix) :
    Table (parameters := parameters) rename side context (node.val + 1) := by
  refine ⟨table.proofPrefix.extend added.state added.steps added.checked, ?_⟩
  intro query before row present
  by_cases same : query = node
  · subst query
    exact added.rows row present
  · have earlier : query.val < node.val := by
      have different : query.val ≠ node.val := fun equal => same (Fin.ext equal)
      omega
    exact (table.rows query earlier row present).afterTrace added.state added.steps added.checked

def build (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (seed : SourcePrefix (parameters := parameters) rename) :
    (count : Nat) → count ≤ parameters.decoder.nodeCount → Table (parameters := parameters) rename side context count
  | 0, _ => ⟨seed, fun node before => False.elim (Nat.not_lt_zero _ before)⟩
  | count + 1, bound =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let table := build rename side context guarded seed count (by omega)
    append rename side context node table (nodeRows rename side context guarded node table.proofPrefix)

def allRows (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (seed : SourcePrefix (parameters := parameters) rename) :=
  build rename side context guarded seed parameters.decoder.nodeCount (Nat.le_refl _)

def Table.afterTrace (table : Table (parameters := parameters) rename side context count)
    (next : State v) (steps : List (Step v)) (checked : runSteps table.proofPrefix.state steps = some next) :
    Table (parameters := parameters) rename side context count where
  proofPrefix := table.proofPrefix.extend next steps checked
  rows node before row present := (table.rows node before row present).afterTrace next steps checked

theorem build_extends (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (seed : SourcePrefix (parameters := parameters) rename)
    (count : Nat) (bound : count ≤ parameters.decoder.nodeCount) :
    ∃ suffix, (build rename side context guarded seed count bound).proofPrefix.steps = seed.steps ++ suffix := by
  induction count with
  | zero => exact ⟨[], by simp [build]⟩
  | succ count ih =>
    obtain ⟨suffix, equality⟩ := ih (by omega)
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let table := build rename side context guarded seed count (by omega)
    let added := nodeRows rename side context guarded node table.proofPrefix
    refine ⟨suffix ++ added.steps, ?_⟩
    change table.proofPrefix.steps ++ added.steps = _
    rw [equality, List.append_assoc]

theorem build_relative (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (seed : SourcePrefix (parameters := parameters) rename)
    (count : Nat) (bound : count ≤ parameters.decoder.nodeCount) :
    let table := build rename side context guarded seed count bound
    runSteps seed.state (table.proofPrefix.steps.drop seed.steps.length) = some table.proofPrefix.state := by
  obtain ⟨suffix, equality⟩ := build_extends rename side context guarded seed count bound
  have full := (build rename side context guarded seed count bound).proofPrefix.checked
  rw [equality, runSteps_append, seed.checked] at full
  simpa only [equality, List.drop_left, Option.bind_some] using full

def memDecidable {α : Type} [DecidableEq α] (item : α) : (items : List α) → Decidable (item ∈ items)
  | [] => .isFalse List.not_mem_nil
  | first :: rest =>
    if same : item = first then .isTrue (List.mem_cons.mpr (Or.inl same))
    else match memDecidable item rest with
      | .isTrue present => .isTrue (List.mem_cons_of_mem _ present)
      | .isFalse absent => .isFalse (fun member => absent ((List.mem_cons.mp member).resolve_left same))

def forwardRow (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (table : Table (parameters := parameters) rename side context parameters.decoder.nodeCount)
    (row : Clause parameters.decoder.ZeroVar) (present : row ∈ parameters.decoder.forwardClauses) :
    Origin (parameters := parameters) rename side table.proofPrefix.state context row := by
  have covered : ∃ node ∈ List.finRange parameters.decoder.nodeCount, row ∈ parameters.decoder.nodeClauses node := by
    simpa only [Controller.Decoder.DAG.forwardClauses, List.mem_flatMap] using present
  letI : DecidableEq (Clause parameters.decoder.ZeroVar) := inferInstance
  letI : DecidablePred (fun node : Fin parameters.decoder.nodeCount => row ∈ parameters.decoder.nodeClauses node) := fun node => by
    change Decidable (row ∈ parameters.decoder.nodeClauses node)
    exact memDecidable row (parameters.decoder.nodeClauses node)
  let selected := pick (List.finRange parameters.decoder.nodeCount) (fun node => row ∈ parameters.decoder.nodeClauses node) covered
  exact table.rows selected.val selected.val.isLt row selected.property.2

theorem disjunctionSize (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (children : List (Fin node.val)) (shape : parameters.decoder.node node = .disj children) :
    (disjunction rename side context node start children shape).steps.length ≤
      4 * sourceDecoderNodeProducerCost parameters node := by
  unfold disjunction
  split
  · rename_i empty
    subst children
    simp
  · rename_i nonempty
    dsimp only
    apply (projectTreeInputs _).count.trans
    simp only [AndTree.afterTrace_nodes]
    have paid := disjunctionTreeCost rename side node children shape nonempty
    omega

theorem guardSize (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (node : Fin parameters.decoder.nodeCount) (start : SourcePrefix (parameters := parameters) rename)
    (child : Fin node.val) (labels : List (Fin parameters.channels))
    (shape : parameters.decoder.node node = .guard child labels) :
    (guard rename side context node start child labels shape).steps.length ≤
      4 * sourceDecoderNodeProducerCost parameters node := by
  unfold guard
  split
  · rename_i empty
    subst labels
    simp
  · dsimp only
    apply (TreeUnits.nonunaryLong _ _).count.trans
    simp only [AndTree.afterTrace_nodes]
    have paid := guardTreeCost rename side node child labels shape
    omega

theorem nodeRowsSize (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (node : Fin parameters.decoder.nodeCount)
    (start : SourcePrefix (parameters := parameters) rename) :
    (nodeRows rename side context guarded node start).steps.length ≤
      4 * sourceDecoderNodeProducerCost parameters node := by
  unfold nodeRows
  split
  · simp [zero]
  · simp [input]
  · exact disjunctionSize _ _ _ _ _ _ _
  · exact guardSize _ _ _ _ _ _ _ _
  · next left right shape =>
    exact False.elim (by simpa [Controller.Decoder.Gate.IsGuarded, shape, Controller.Decoder.Gate.isLiveAnd] using guarded node)

theorem buildSize (rename : Nat → Fin v) (side : Side) (context : Clause (Fin v))
    (guarded : parameters.decoder.Guarded) (seed : SourcePrefix (parameters := parameters) rename)
    (count : Nat) (bound : count ≤ parameters.decoder.nodeCount) :
    (build rename side context guarded seed count bound).proofPrefix.steps.length ≤
      seed.steps.length + 4 * evaluationPrefixCost parameters count := by
  induction count with
  | zero => simp [build, evaluationPrefixCost]
  | succ count ih =>
    let node : Fin parameters.decoder.nodeCount := ⟨count, by omega⟩
    let previous := build rename side context guarded seed count (by omega)
    have old := ih (by omega)
    change previous.proofPrefix.steps.length ≤ seed.steps.length +
      4 * evaluationPrefixCost parameters count at old
    have current := nodeRowsSize rename side context guarded node previous.proofPrefix
    change (previous.proofPrefix.steps ++ (nodeRows rename side context guarded node previous.proofPrefix).steps).length ≤ _
    rw [List.length_append]
    have next := evaluationPrefixCost_succ parameters node
    change evaluationPrefixCost parameters (count + 1) =
      evaluationPrefixCost parameters count + sourceDecoderNodeProducerCost parameters node at next
    omega

end Controller.NativeProof.SourceForwardRows
