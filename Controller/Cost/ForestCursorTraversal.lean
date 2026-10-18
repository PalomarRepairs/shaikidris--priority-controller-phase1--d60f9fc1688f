module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorProgram

@[expose] public section

/-!
# Source-rooted physical forest traversal

Traversal operations retain stored node and child positions. Node-record reads,
positional navigation, counter updates and physical leaf selection have
separate instruction bodies. The generated operation list is a proof witness
for the source-specialized program; full route lists are not runtime heap data.
-/
namespace Controller.Cost.ForestCursorTraversal

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram

/-- These operations are generated only by the actual stored decoder recursion. -/
inductive CursorOp (n : ℕ) where
  | node (index : ℕ)
  | down (parent position child : ℕ)
  | up
  | enter (owner position : ℕ) (channel : Channel n)
  | leave (owner position : ℕ) (channel : Channel n)
  | leaf (owner : ℕ) (route : LeafRoute) (head : Channel n)
  deriving DecidableEq

/-- Stored node accesses and child occurrences are explicit in the generated
traversal, including repeated references to shared terminal nodes. -/
def cursorOps (graph : DAG n) (node : Fin graph.nodeCount) (routePrefix : LeafRoute) :
    List (CursorOp n) :=
  .node node.val :: match graph.node node with
  | .zero => []
  | .input head => [.leaf node.val routePrefix head]
  | .disj refs => (List.finRange refs.length).flatMap fun position =>
      let child := graph.childIndex node (refs.get position)
      [.down node.val position.val child.val] ++ cursorOps graph child (position.val :: routePrefix) ++ [.up]
  | .guard child labels =>
      (List.finRange labels.length).map (fun position => .enter node.val position.val (labels.get position)) ++
        [.down node.val 0 (graph.childIndex node child).val] ++
        cursorOps graph (graph.childIndex node child) (0 :: routePrefix) ++ [.up] ++
        (List.finRange labels.length).reverse.map (fun position => .leave node.val position.val (labels.get position))
  | .liveAnd _ _ => []
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

/-- The finite physical records certify source tags, child IDs and channel IDs.
Mutable counter/selector regions must be disjoint from all these cells. -/
structure GraphRecords (width : ℕ) (heap : Array (Word width)) (graph : DAG n) where
  recordBase : ℕ
  childBase : Fin graph.nodeCount → ℕ
  guardBase : Fin graph.nodeCount → ℕ
  tagValid : ∀ node : Fin graph.nodeCount, recordBase + 2 * node.val < heap.size
  tagWord : ∀ node, heap[recordBase + 2 * node.val]'(tagValid node) =
    word width (match graph.node node with
      | .zero => 0 | .input _ => 1 | .disj _ => 2 | .guard _ _ => 3 | .liveAnd _ _ => 4)
  headValid : ∀ node : Fin graph.nodeCount, recordBase + 2 * node.val + 1 < heap.size
  headWord : ∀ node head, graph.node node = .input head →
    heap[recordBase + 2 * node.val + 1]'(headValid node) = word width head.val
  childValid : ∀ node, ∀ position : Fin (graph.node node).children.length,
    childBase node + position.val < heap.size
  childWord : ∀ node, ∀ position : Fin (graph.node node).children.length,
    heap[childBase node + position.val]'(childValid node position) =
      word width ((graph.node node).children.get position).val
  guardValid : ∀ node, ∀ position : Fin (graph.node node).guardLabels.length,
    guardBase node + position.val < heap.size
  guardWord : ∀ node, ∀ position : Fin (graph.node node).guardLabels.length,
    heap[guardBase node + position.val]'(guardValid node position) =
      word width ((graph.node node).guardLabels.get position).val

def recordReadCode (width address : ℕ) : ForestCounter.Code width :=
  [.constant 0 (word width address), .load 1 0]

/-- Two actual fetched instructions read a represented source record. -/
theorem record_read_execution (program : Program width 4) (heap : Array (Word width))
    (base address : ℕ) (oldAddress loaded temporary value : Word width)
    (fits : base + 2 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (held : heap[address] = value)
    (block : BlockAt program base (recordReadCode width address)) :
    Execution program (counterState heap base oldAddress loaded temporary)
      (counterState heap (base + 2) (word width address) value temporary) 2 (5 + heap.size) := by
  have first : program[base]? = some (.constant 0 (word width address)) := by
    simpa [recordReadCode] using block 0 (by simp [recordReadCode])
  have second : program[base + 1]? = some (.load 1 0) := by
    simpa [recordReadCode] using block 1 (by simp [recordReadCode])
  have a := address_transition program heap base address oldAddress loaded temporary (by omega) first
  have b := read_transition program heap (base + 1) address loaded temporary value
    (by omega) addressFits valid held second
  have trace := Execution.cons a (Execution.cons b (Execution.refl
    (counterState heap (base + 2) (word width address) value temporary)))
  simpa only [counterState_liveWords, Nat.add_assoc, Nat.zero_add, max_self] using trace

/-- The concrete test routePrefix uses one shared failure continuation. -/
def zeroTestsCode (width base failure : ℕ) : List ℕ → ForestCounter.Code width
  | [] => []
  | address :: rest => zeroTest width base address failure ++
      zeroTestsCode width (base + 4) failure rest

@[simp] theorem zeroTestsCode_length (width base failure : ℕ) (addresses : List ℕ) :
    (zeroTestsCode width base failure addresses).length = 4 * addresses.length := by
  induction addresses generalizing base with
  | nil => simp [zeroTestsCode]
  | cons address rest ih => simp [zeroTestsCode, ih]; omega

/-- Coverage of the emitted routePrefix supplies the actual selector test contract. -/
theorem zeroTestsCode_coverage (program : Program width 4) (base failure : ℕ)
    (addresses : List ℕ)
    (block : BlockAt program base (zeroTestsCode width base failure addresses)) :
    TestsAt program base failure addresses := by
  induction addresses generalizing base with
  | nil => trivial
  | cons address rest ih =>
      exact ⟨BlockAt.prefix program base _ _ block,
        ih (base + 4) (by simpa using BlockAt.suffix program base _ _ block)⟩

def leafCode (width base : ℕ) (layout : SelectorLayout n) (b : ℕ)
    (target head : Channel n) (pointer : ℕ) : ForestCounter.Code width :=
  let addresses := leafTests layout b target head
  let finish := base + 4 * addresses.length + 6
  zeroTestsCode width base finish addresses ++
    commitCode width layout.best layout.found pointer

@[simp] theorem leafCode_length (width base : ℕ) (layout : SelectorLayout n) (b : ℕ)
    (target head : Channel n) (pointer : ℕ) :
    (leafCode width base layout b target head pointer).length =
      4 * (leafTests layout b target head).length + 6 := by
  simp [leafCode]

/-- A single emitted leaf block supplies both contracts needed by the physical
callback. No additional instruction generation occurs while the callback runs. -/
theorem leafCode_coverage (program : Program width 4) (base : ℕ)
    (layout : SelectorLayout n) (b : ℕ) (target head : Channel n) (pointer : ℕ)
    (block : BlockAt program base (leafCode width base layout b target head pointer)) :
    TestsAt program base (base + 4 * (leafTests layout b target head).length + 6)
      (leafTests layout b target head) ∧
    BlockAt program (base + 4 * (leafTests layout b target head).length)
      (commitCode width layout.best layout.found pointer) := by
  exact ⟨zeroTestsCode_coverage program base _ _
    (BlockAt.prefix program base _ _ block),
    by simpa using BlockAt.suffix program base _ _ block⟩

/-- The descriptor index is a compile-time occurrence map. Its source-linear
construction must be proved before using the complete resource contract. The
runtime code stores a pointer and never constructs a route list. -/
structure OccurrenceIndex (graph : DAG n) where
  pointer : LeafRoute → ℕ
  empty : pointer [] = 0

/-- Node-index conversion is total for code emission; source-generated owner
indices are valid and the fallback is never used by a valid traversal. -/
def childRecordAddress (graph : DAG n) (records : GraphRecords width heap graph)
    (owner position : ℕ) : ℕ :=
  if valid : owner < graph.nodeCount then records.childBase ⟨owner, valid⟩ + position else 0

def guardRecordAddress (graph : DAG n) (records : GraphRecords width heap graph)
    (owner position : ℕ) : ℕ :=
  if valid : owner < graph.nodeCount then records.guardBase ⟨owner, valid⟩ + position else 0

/-- A source-specialized operation reads its represented graph cell before
performing the corresponding counter, navigation or selector action. Control
continuations are fixed code addresses; no indirect-jump primitive is assumed. -/
def operationCode (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (base b : ℕ) (target : Channel n) : CursorOp n → ForestCounter.Code width
  | .node owner => recordReadCode width (records.recordBase + 2 * owner)
  | .down owner position _ =>
      recordReadCode width (childRecordAddress graph records owner position) ++ downCode width position
  | .up => upCode
  | .enter owner position channel =>
      recordReadCode width (guardRecordAddress graph records owner position) ++
        changeCode width (layout.counterOffset + channel.val) 1
  | .leave owner position channel =>
      recordReadCode width (guardRecordAddress graph records owner position) ++
        changeCode width (layout.counterOffset + channel.val) (2 ^ width - 1)
  | .leaf owner route head =>
      recordReadCode width (records.recordBase + 2 * owner + 1) ++
        leafCode width (base + 2) layout b target head (index.pointer route)

/-- This emitter joins the actual instruction blocks at their successive code
addresses. The operation list is a source-derived proof witness. -/
def emitOperations (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (base : ℕ) :
    List (CursorOp n) → ForestCounter.Code width
  | [] => []
  | operation :: rest =>
      let block := operationCode graph records layout index base b target operation
      block ++ emitOperations graph records layout index b target (base + block.length) rest

/-- The root program is emitted directly from the decoder's positional
recursion. The initial heap and immutable source-record representation are
explicit; runtime best-route reconstruction is a separate phase. -/
def rootCode (graph : DAG n) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (base : ℕ) (root : Fin graph.nodeCount) :
    ForestCounter.Code width :=
  emitOperations graph records layout index b target base (cursorOps graph root [])

/-- Whole emitted coverage splits into the physical current block and the
recursive continuation at its actual end address. -/
theorem emitOperations_coverage (program : Program width 4) (graph : DAG n)
    (records : GraphRecords width heap graph) (layout : SelectorLayout n)
    (index : OccurrenceIndex graph) (b : ℕ) (target : Channel n) (base : ℕ)
    (operation : CursorOp n) (rest : List (CursorOp n))
    (stored : BlockAt program base
      (emitOperations graph records layout index b target base (operation :: rest))) :
    BlockAt program base (operationCode graph records layout index base b target operation) ∧
    BlockAt program (base + (operationCode graph records layout index base b target operation).length)
      (emitOperations graph records layout index b target
        (base + (operationCode graph records layout index base b target operation).length) rest) := by
  exact ⟨BlockAt.prefix program base _ _ stored, BlockAt.suffix program base _ _ stored⟩

/-- A successful selector preserves every immutable source or descriptor cell
outside its two metadata addresses. This is the heap-frame seam needed when
joining the next source operation. -/
theorem committed_readonly (heap : Array (Word width)) (layout : SelectorLayout n)
    (pointer address : ℕ) (valid : address < heap.size)
    (foundValid : layout.found < heap.size) (bestValid : layout.best < heap.size)
    (notFound : layout.found ≠ address) (notBest : layout.best ≠ address) :
    ForestGuardSchedule.storedWord (committedHeap width heap layout.best layout.found pointer) address =
      ForestGuardSchedule.storedWord heap address := by
  have heapEq : committedHeap width heap layout.best layout.found pointer =
      (heap.set layout.best (word width pointer) bestValid).set layout.found (word width 1)
        (by simpa using foundValid) := by
    simp [committedHeap, Array.setIfInBounds_def, bestValid, foundValid]
  rw [heapEq, ForestGuardSchedule.storedWord_eq _ _ (by simpa using valid),
    ForestGuardSchedule.storedWord_eq heap address valid]
  rw [Array.getElem_set_ne (by simpa using foundValid) (by simpa using valid) notFound,
    Array.getElem_set_ne bestValid valid notBest]

/-- A valid parent index selects its represented positional child record. -/
@[simp] theorem childRecordAddress_valid (graph : DAG n)
    (records : GraphRecords width heap graph) (node : Fin graph.nodeCount) (position : ℕ) :
    childRecordAddress graph records node.val position = records.childBase node + position := by
  simp [childRecordAddress, node.isLt]

@[simp] theorem guardRecordAddress_valid (graph : DAG n)
    (records : GraphRecords width heap graph) (node : Fin graph.nodeCount) (position : ℕ) :
    guardRecordAddress graph records node.val position = records.guardBase node + position := by
  simp [guardRecordAddress, node.isLt]

/-- Child navigation reads the actual source child ID at its stored position. -/
theorem source_child_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (records : GraphRecords width heap graph)
    (node : Fin graph.nodeCount) (position : Fin (graph.node node).children.length) (base : ℕ)
    (address loaded temporary : Word width)
    (fits : base + 2 < 2 ^ width)
    (recordFits : records.childBase node + position.val < 2 ^ width)
    (block : BlockAt program base
      (recordReadCode width (childRecordAddress graph records node.val position.val))) :
    Execution program (counterState heap base address loaded temporary)
      (counterState heap (base + 2) (word width (records.childBase node + position.val))
        (word width ((graph.node node).children.get position).val) temporary)
      2 (5 + heap.size) := by
  exact record_read_execution program heap base _ address loaded temporary _ fits recordFits
    (records.childValid node position) (records.childWord node position) (by simpa using block)

/-- Each repeated guard-label position is read separately from the finite source
record layout before its corresponding counter update. -/
theorem source_guard_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (records : GraphRecords width heap graph)
    (node : Fin graph.nodeCount) (position : Fin (graph.node node).guardLabels.length) (base : ℕ)
    (address loaded temporary : Word width)
    (fits : base + 2 < 2 ^ width)
    (recordFits : records.guardBase node + position.val < 2 ^ width)
    (block : BlockAt program base
      (recordReadCode width (guardRecordAddress graph records node.val position.val))) :
    Execution program (counterState heap base address loaded temporary)
      (counterState heap (base + 2) (word width (records.guardBase node + position.val))
        (word width ((graph.node node).guardLabels.get position).val) temporary)
      2 (5 + heap.size) := by
  exact record_read_execution program heap base _ address loaded temporary _ fits recordFits
    (records.guardValid node position) (records.guardWord node position) (by simpa using block)

/-- The abstract callback state follows the production cursor; navigation
operations carry physical effects but leave this callback state unchanged. -/
abbrev CursorState (n : ℕ) := WeightedCounters n × Option (LeafRoute × ℕ)

def cursorStep (b : ℕ) (target : Channel n) (state : CursorState n) :
    CursorOp n → CursorState n
  | .enter _ _ channel => (enterWeightedLabel (fun _ => 0) state.1 channel, state.2)
  | .leave _ _ channel => (leaveWeightedLabel (fun _ => 0) state.1 channel, state.2)
  | .leaf _ route head =>
      (state.1, keepBestRoute b target 0 route head state.1 state.2)
  | .node _ | .down _ _ _ | .up => state

/-- Zero weights remove arithmetic work without removing any guard incidence. -/
theorem enter_zero (counters : GuardCounters n) (score : ℕ) (channel : Channel n) :
    enterWeightedLabel (fun _ => 0) (counters, score) channel =
      (enterGuards counters [channel], score) := by
  simp [enterWeightedLabel]

theorem leave_zero (counters : GuardCounters n) (score : ℕ) (channel : Channel n) :
    leaveWeightedLabel (fun _ => 0) (counters, score) channel =
      (leaveGuards counters [channel], score) := by
  simp [leaveWeightedLabel]

/-- Exit order has no effect on zero-weight counters, including duplicated
labels. The physical order is reversed to retain a well-bracketed trace. -/
theorem leave_reverse (counters : GuardCounters n) (labels : List (Channel n)) :
    leaveGuards counters labels.reverse = leaveGuards counters labels := by
  funext channel
  rw [leaveGuards_count, leaveGuards_count, List.count_reverse]

def guardProjection : CursorOp n → List (ForestGuardSchedule.GuardEvent n)
  | .enter _ _ channel => [.enter channel]
  | .leave _ _ channel => [.leave channel]
  | _ => []

/-- Indexed guard records enumerate exactly the source labels. -/
theorem indexed_guard_projection (owner : ℕ) (labels : List (Channel n)) :
    ((List.finRange labels.length).map (fun position =>
      CursorOp.enter owner position.val (labels.get position))).flatMap guardProjection =
      labels.map ForestGuardSchedule.GuardEvent.enter := by
  calc
    _ = ((List.finRange labels.length).map labels.get).map
        ForestGuardSchedule.GuardEvent.enter := by
      simp only [List.flatMap_map, guardProjection, ← List.map_eq_flatMap, List.map_map, Function.comp_def]
    _ = _ := by rw [List.map_get_finRange]

/-- Replacing positional enumeration by source list traversal preserves every
child occurrence, even when two positions hold the same terminal reference. -/
theorem indexed_flatMap (items : List α) (visit : α → List β) :
    (List.finRange items.length).flatMap (fun position => visit (items.get position)) =
      items.flatMap visit := by
  rw [← List.flatMap_map, List.map_get_finRange]

theorem indexed_leave_projection (owner : ℕ) (labels : List (Channel n)) :
    ((List.finRange labels.length).reverse.map (fun position =>
      CursorOp.leave owner position.val (labels.get position))).flatMap guardProjection =
      labels.reverse.map ForestGuardSchedule.GuardEvent.leave := by
  calc
    _ = ((List.finRange labels.length).reverse.map labels.get).map
        ForestGuardSchedule.GuardEvent.leave := by
      rw [List.flatMap_map]
      simp only [guardProjection, ← List.map_eq_flatMap, List.map_map, Function.comp_def]
    _ = ((List.finRange labels.length).map labels.get).reverse.map
        ForestGuardSchedule.GuardEvent.leave := by rw [List.map_reverse]
    _ = _ := by rw [List.map_get_finRange]

/-- The actual source-rooted operation list has exactly the guard event trace
whose positivity and no-wrap theorem is already checked. -/
theorem cursor_guard_projection (graph : DAG n) (node : Fin graph.nodeCount)
    (routePrefix : LeafRoute) :
    (cursorOps graph node routePrefix).flatMap guardProjection =
      ForestGuardSchedule.walkEvents graph node := by
  have claim : ∀ rank : ℕ, ∀ node : Fin graph.nodeCount, node.val = rank →
      ∀ routePrefix : LeafRoute,
        (cursorOps graph node routePrefix).flatMap guardProjection =
          ForestGuardSchedule.walkEvents graph node := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current equal route
      rw [cursorOps, ForestGuardSchedule.walkEvents]
      cases equation : graph.node current with
      | zero => rfl
      | input head => rfl
      | liveAnd left right => rfl
      | disj refs =>
          simp only [List.flatMap_cons, guardProjection, List.nil_append, List.flatMap_assoc]
          have each : ∀ position : Fin refs.length,
              (([CursorOp.down current.val position.val
                    (graph.childIndex current (refs.get position)).val] ++
                  cursorOps graph (graph.childIndex current (refs.get position))
                    (position.val :: route) ++ [CursorOp.up]).flatMap guardProjection) =
                ForestGuardSchedule.walkEvents graph (graph.childIndex current (refs.get position)) := by
            intro position
            simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              guardProjection, List.nil_append, List.append_nil]
            exact ih _ (by have earlier := graph.childIndex_lt current (refs.get position); omega)
              _ rfl _
          simp_rw [each]
          exact indexed_flatMap refs (fun child => ForestGuardSchedule.walkEvents graph (graph.childIndex current child))
      | guard child labels =>
          simp only [List.flatMap_cons, guardProjection, List.nil_append, List.flatMap_append,
            List.flatMap_nil, List.append_nil]
          rw [indexed_guard_projection, indexed_leave_projection]
          rw [ih _ (by have earlier := graph.childIndex_lt current child; omega) _ rfl]
  exact claim node.val node rfl routePrefix

/-- The physical source tag read is tied to an actual decoder node. -/
theorem source_tag_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (records : GraphRecords width heap graph)
    (node : Fin graph.nodeCount) (base : ℕ)
    (address loaded temporary : Word width)
    (fits : base + 2 < 2 ^ width)
    (recordFits : records.recordBase + 2 * node.val < 2 ^ width)
    (block : BlockAt program base
      (recordReadCode width (records.recordBase + 2 * node.val))) :
    Execution program (counterState heap base address loaded temporary)
      (counterState heap (base + 2) (word width (records.recordBase + 2 * node.val))
        (word width (match graph.node node with
          | .zero => 0 | .input _ => 1 | .disj _ => 2 | .guard _ _ => 3 | .liveAnd _ _ => 4))
        temporary) 2 (5 + heap.size) := by
  exact record_read_execution program heap base _ address loaded temporary _ fits recordFits
    (records.tagValid node) (records.tagWord node) block

end Controller.Cost.ForestCursorTraversal
