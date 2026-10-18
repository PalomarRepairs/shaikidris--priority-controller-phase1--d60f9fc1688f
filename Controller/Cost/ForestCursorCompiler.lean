module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorCapturedProgram
public import Controller.Cost.CompilerAppendTrace

@[expose] public section

/-!
# Direct source compiler for the physical forest cursor

The executable recursion reads stored decoder nodes and child positions. It
carries an allocation cursor and a reversed instruction accumulator. It creates
no route-prefix lists and never materializes the ghost cursor operation list.
The source-operation list occurs only in refinement statements. Local append
traces charge three concrete list traversals; descriptor-cell materialization,
chunk generation and finite allocation have separate costs.
-/
namespace Controller.Cost.ForestCursorCompiler

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorCapturedProgram

structure State (width : ℕ) where
  descriptors : ForestCursorDescriptors.Builder
  code : CompilerBuilder.Builder width

def emit (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : State width) (operation : CursorOp n) : State width :=
  let chunk := capturedCode graph records layout state.descriptors state.code.cursor b target operation
  ⟨ForestCursorDescriptors.step root state.descriptors operation, state.code.append chunk⟩

/-- Specification fold; the executable source compiler does not call it. -/
def runOps (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : State width) (operations : List (CursorOp n)) : State width :=
  operations.foldl (emit graph records layout root b target) state

theorem runOps_append (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : State width) (first second : List (CursorOp n)) :
    runOps graph records layout root b target state (first ++ second) =
      runOps graph records layout root b target
        (runOps graph records layout root b target state first) second := by
  simp only [runOps, List.foldl_append]

/-- Leaf routes are erased before descriptor and code updates. -/
theorem emit_leaf_erased (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : State width) (owner : ℕ) (head : Channel n) (route : LeafRoute) :
    emit graph records layout root b target state (.leaf owner [] head) =
      emit graph records layout root b target state (.leaf owner route head) := rfl

/-- Source recursion carries descriptor IDs, not paths. The only route argument
is an ignored empty literal at leaves. -/
def compileNode (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (node : Fin graph.nodeCount) (state : State width) : State width :=
  let entered := emit graph records layout root b target state (.node node.val)
  match graph.node node with
  | .zero => entered
  | .liveAnd _ _ => entered
  | .input head => emit graph records layout root b target entered (.leaf node.val [] head)
  | .disj refs =>
      refs.zipIdx.foldl (fun current item =>
        let child := graph.childIndex node item.1
        let down := emit graph records layout root b target current (.down node.val item.2 child.val)
        let visited := compileNode graph records layout root b target child down
        emit graph records layout root b target visited .up) entered
  | .guard child labels =>
      let indexed := labels.zipIdx
      let guarded := indexed.foldl (fun current item =>
        emit graph records layout root b target current (.enter node.val item.2 item.1)) entered
      let down := emit graph records layout root b target guarded (.down node.val 0 (graph.childIndex node child).val)
      let visited := compileNode graph records layout root b target (graph.childIndex node child) down
      let up := emit graph records layout root b target visited .up
      indexed.reverse.foldl (fun current item =>
        emit graph records layout root b target current (.leave node.val item.2 item.1)) up
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

/-- This identity is a proof bridge; the executable enumeration uses zipIdx,
whose traversal reads each source list cell once. -/
private theorem zipIdx_finRange (items : List α) :
    items.zipIdx = (List.finRange items.length).map (fun position => (items.get position, position.val)) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp

private theorem foldl_agrees (items : List α) (left right : β → α → β)
    (same : ∀ state item, left state item = right state item) (state : β) :
    items.foldl left state = items.foldl right state := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih => simp only [List.foldl_cons, same]; exact ih _

private theorem foldl_flatBlocks (items : List α) (body : α → List β)
    (step : γ → β → γ) (state : γ) :
    (items.flatMap body).foldl step state =
      items.foldl (fun current item => (body item).foldl step current) state := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]; exact ih _

/-- Whole-node refinement for arbitrary ghost prefix routes and accumulators. -/
theorem compileNode_eq (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n) :
    ∀ (node : Fin graph.nodeCount) (route : LeafRoute) (state : State width),
      compileNode graph records layout root b target node state =
        runOps graph records layout root b target state (cursorOps graph node route) := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ route state, compileNode graph records layout root b target node state =
        runOps graph records layout root b target state (cursorOps graph node route) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node equal route state
      rw [compileNode.eq_def, cursorOps.eq_def]
      cases kind : graph.node node with
      | zero => rfl
      | liveAnd left right => rfl
      | input head => exact emit_leaf_erased graph records layout root b target _ node.val head route
      | disj refs =>
          simp only [zipIdx_finRange, List.foldl_map, runOps, List.foldl_cons, List.foldl_nil, foldl_flatBlocks]
          apply foldl_agrees
          intro current position
          let child := graph.childIndex node (refs.get position)
          have earlier : child.val < rank := by
            have bound := graph.childIndex_lt node (refs.get position)
            dsimp [child]
            omega
          rw [ih child.val earlier child rfl (position.val :: route)]
          simp only [runOps, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rfl
      | guard child labels =>
          simp only [zipIdx_finRange, ← List.map_reverse, List.foldl_map]
          have earlier : (graph.childIndex node child).val < rank := by
            have bound := graph.childIndex_lt node child
            omega
          rw [ih (graph.childIndex node child).val earlier (graph.childIndex node child) rfl (0 :: route)]
          simp only [runOps, List.foldl_cons, List.foldl_append, List.foldl_map, List.foldl_nil]
  intro node route state
  exact claim node.val node rfl route state

theorem runOps_descriptors (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : State width) (operations : List (CursorOp n)) :
    (runOps graph records layout root b target state operations).descriptors =
      ForestCursorDescriptors.scan root state.descriptors operations := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      change (runOps graph records layout root b target
        (emit graph records layout root b target state operation) rest).descriptors = _
      rw [ih]
      rfl

theorem runOps_code (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : State width) (operations : List (CursorOp n)) :
    (runOps graph records layout root b target state operations).code.cursor =
      state.code.cursor + (emitCaptured graph records layout root b target state.descriptors state.code.cursor operations).length ∧
    (runOps graph records layout root b target state operations).code.reversed.reverse =
      state.code.reversed.reverse ++ emitCaptured graph records layout root b target state.descriptors state.code.cursor operations := by
  induction operations generalizing state with
  | nil => simp [runOps, emitCaptured]
  | cons operation rest ih =>
      obtain ⟨cursor, code⟩ := ih (emit graph records layout root b target state operation)
      constructor
      · simpa only [runOps, List.foldl_cons, emit, CompilerBuilder.Builder.append,
          emitCaptured, List.length_append, Nat.add_assoc] using cursor
      · simpa only [runOps, List.foldl_cons, emit, CompilerBuilder.Builder.append_reversed,
          CompilerBuilder.Builder.append, emitCaptured, List.reverse_append, List.reverse_reverse,
          List.append_assoc] using code

def compileRoot (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (b : ℕ) (target : Channel n)
    (position : Fin graph.roots.length) (state : State width) : State width :=
  compileNode graph records layout position.val b target (graph.roots.get position)
    { state with descriptors := ForestCursorDescriptors.beginRoot state.descriptors }

theorem compileRoot_descriptors (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (b : ℕ) (target : Channel n)
    (position : Fin graph.roots.length) (state : State width) :
    (compileRoot graph records layout b target position state).descriptors =
      ForestCursorDescriptors.scanRoot graph state.descriptors position := by
  unfold compileRoot
  rw [compileNode_eq graph records layout position.val b target _ []]
  exact runOps_descriptors graph records layout position.val b target _ _

/-- This trace charges length, reversal, copying and one cursor addition for
this emitted chunk. Chunk generation and descriptor updates are separate. -/
theorem emit_append_trace (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : State width) (operation : CursorOp n) :
    let chunk := capturedCode graph records layout state.descriptors state.code.cursor b target operation
    CompilerAppendTrace.BuilderTrace state.code chunk
      (emit graph records layout root b target state operation).code (3 * chunk.length + 1) := by
  exact CompilerAppendTrace.builder_exists _ _

/-- Every current instruction chunk has bounded size independently of prior
code and descriptor accumulation. -/
theorem capturedCode_length_le (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (state : ForestCursorDescriptors.Builder)
    (base b : ℕ) (target : Channel n) (operation : CursorOp n) :
    (capturedCode graph records layout state base b target operation).length ≤ 20 := by
  cases operation <;> simp [capturedCode, operationCode, recordReadCode,
    downCode, upCode, ForestCounter.changeCode, leafCode, leafTests_length] <;> split <;> omega

/-- A trace of the actual reversed-accumulator traversals along the compiler
updates. Descriptor update and chunk generation are deliberately not assigned
costs by this relation. -/
inductive AppendRunTrace (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n) :
    State width → List (CursorOp n) → State width → ℕ → Prop where
  | nil (state) : AppendRunTrace graph records layout root b target state [] state 0
  | cons (state : State width) (operation : CursorOp n) (rest : List (CursorOp n))
      (final : State width) (localVisits tailVisits : ℕ)
      (localTrace : CompilerAppendTrace.BuilderTrace state.code
        (capturedCode graph records layout state.descriptors state.code.cursor b target operation)
        (emit graph records layout root b target state operation).code localVisits)
      (tail : AppendRunTrace graph records layout root b target
        (emit graph records layout root b target state operation) rest final tailVisits) :
      AppendRunTrace graph records layout root b target state (operation :: rest) final
        (localVisits + tailVisits)

/-- Concrete accumulator traversals for the whole ghost refinement have a
linear visit bound. The executable direct source recursion has the same state
updates by compileNode_eq; this is not a whole compiler time bound. -/
theorem appendRun_exists (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (root b : ℕ) (target : Channel n)
    (state : State width) (operations : List (CursorOp n)) :
    ∃ visits, AppendRunTrace graph records layout root b target state operations
      (runOps graph records layout root b target state operations) visits ∧
      visits ≤ 61 * operations.length := by
  induction operations generalizing state with
  | nil => exact ⟨0, AppendRunTrace.nil state, by simp⟩
  | cons operation rest ih =>
      obtain ⟨visits, tail, bound⟩ := ih (emit graph records layout root b target state operation)
      let chunk := capturedCode graph records layout state.descriptors state.code.cursor b target operation
      refine ⟨3 * chunk.length + 1 + visits, ?_, ?_⟩
      · exact AppendRunTrace.cons state operation rest _ _ _
          (emit_append_trace graph records layout root b target state operation) tail
      · have localBound := capturedCode_length_le graph records layout state.descriptors state.code.cursor b target operation
        change chunk.length ≤ 20 at localBound
        simp only [List.length_cons]
        omega

end Controller.Cost.ForestCursorCompiler
