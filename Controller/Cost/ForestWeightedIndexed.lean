module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestWeightedCaller
public import Controller.Cost.CompilerArrayTrace
public import Controller.Cost.ForestCursorWholeProgram

@[expose] public section

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestCursorTraversal
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Validation traverses each original incidence once and retains its order. -/
def boundedIds (bound : Nat) : List Nat → Option (List (Fin bound))
  | [] => some []
  | value :: rest =>
      if valid : value < bound then
        (boundedIds bound rest).map (⟨value, valid⟩ :: ·)
      else none

/-- Original row operands are decoded with checked channel and child bounds. -/
def decodeRow (n owner : Nat) (row : Row) : Option (Gate n owner) :=
  match row.tag with
  | 0 => some .zero
  | 1 => if valid : row.head < n then some (.input ⟨row.head, valid⟩) else none
  | 2 => (boundedIds owner row.children).map Gate.disj
  | 3 => do
      let children ← boundedIds owner row.children
      let labels ← boundedIds n row.guards
      match children with
      | [child] => some (.guard child labels)
      | _ => none
  | 4 => do
      let children ← boundedIds owner row.children
      match children with
      | [first, second] => some (.liveAnd first second)
      | _ => none
  | _ => none

abbrev Source (n : Nat) := Array (Option (Sigma fun owner : Nat => Gate n owner))

/-- The table is formed from supplied rows, rather than evaluating DAG.node. -/
def sourceItems (n : Nat) (rows : List Row) : List (Option (Sigma fun owner : Nat => Gate n owner)) :=
  rows.zipIdx.map fun item => (decodeRow n item.2 item.1).map (Sigma.mk item.2)

def source (n : Nat) (rows : List Row) : Source n := (sourceItems n rows).toArray

/-- Each visit performs one indexed table lookup and one rank comparison. -/
def readNode (table : Source n) (owner : Nat) : Gate n owner :=
  match table[owner]? with
  | some (some ⟨rank, gate⟩) => if same : rank = owner then same ▸ gate else .zero
  | _ => .zero

structure State (n : Nat) (W : Type) where
  counters : Array Nat
  blockedWeight : W
  descriptors : ForestCursorDescriptors.Builder
  selected : Option (Candidate W)
  operations : Nat
  arithmetic : Nat

def arrayView (counts : Array Nat) (channel : Channel n) : Nat :=
  counts[channel.val]?.getD 0

def counter (state : State n W) : Channel n → Nat := arrayView state.counters

def view (state : State n W) : ForestWeightedDirect.State n W :=
  ⟨⟨(counter state, state.blockedWeight), state.descriptors, state.selected⟩,
    state.operations, state.arithmetic⟩

/-- Generic weight arithmetic is counted separately from source/counter reads.
The counters use actual array reads and writes; descriptor lists only grow by
constant-size cons operations and never copy a candidate route. -/
def emit (weights : Channel n → W) (total : W) (root b : Nat) (target : Channel n)
    (state : State n W) (operation : CursorOp n) : State n W :=
  let next := { state with
    descriptors := ForestCursorDescriptors.step root state.descriptors operation
    operations := state.operations + 1
    arithmetic := state.arithmetic + ForestWeightedDirect.arithmeticCount b target (view state).data operation }
  match operation with
  | .enter _ _ channel =>
      { next with
        counters := state.counters.setIfInBounds channel.val (counter state channel + 1)
        blockedWeight := if counter state channel = 0 then state.blockedWeight + weights channel else state.blockedWeight }
  | .leave _ _ channel =>
      { next with
        counters := state.counters.setIfInBounds channel.val (counter state channel - 1)
        blockedWeight := if counter state channel = 1 then state.blockedWeight - weights channel else state.blockedWeight }
  | .leaf _ _ head =>
      if counter state head = 0 ∧ (b ≠ 1 ∨ counter state target = 0) then
        { next with selected := choose state.selected ⟨root, state.descriptors.current, total - state.blockedWeight⟩ }
      else next
  | _ => next

/-- Runtime recursion reads the decoded table, not the graph specification.
Child bounds come from decodeRow and make the actual traversal decreasing. -/
def runNode (table : Source n) (weights : Channel n → W) (total : W) (root b : Nat)
    (target : Channel n) (owner : Nat) (state : State n W) : State n W :=
  let entered := emit weights total root b target state (.node owner)
  match readNode table owner with
  | .zero => entered
  | .liveAnd _ _ => entered
  | .input head => emit weights total root b target entered (.leaf owner [] head)
  | .disj children => children.zipIdx.foldl (fun current item =>
      let down := emit weights total root b target current (.down owner item.2 item.1.val)
      let visited := runNode table weights total root b target item.1.val down
      emit weights total root b target visited .up) entered
  | .guard child labels =>
      let indexed := labels.zipIdx
      let guarded := indexed.foldl (fun current item => emit weights total root b target current (.enter owner item.2 item.1)) entered
      let down := emit weights total root b target guarded (.down owner 0 child.val)
      let visited := runNode table weights total root b target child.val down
      let up := emit weights total root b target visited .up
      indexed.reverse.foldl (fun current item => emit weights total root b target current (.leave owner item.2 item.1)) up
termination_by owner
decreasing_by all_goals exact Fin.isLt _

def runRoots (table : Source n) (weights : Channel n → W) (total : W) (b : Nat)
    (target : Channel n) (roots : List Nat) (state : State n W) : State n W :=
  roots.zipIdx.foldl (fun current item =>
    runNode table weights total item.2 b target item.1
      { current with descriptors := ForestCursorDescriptors.beginRoot current.descriptors }) state

/-- A single initialized counter array is shared by all root occurrences. -/
def runAll (table : Source n) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (roots : List Nat) : W × State n W :=
  let total := (List.finRange n).foldl (fun value channel => value + weights channel) 0
  (total, runRoots table weights total b target roots
    ⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩)

theorem source_formation (n : Nat) (rows : List Row) :
    CompilerArrayTrace.Trace (sourceItems n rows) #[] (source n rows) rows.length := by
  have trace := CompilerArrayTrace.empty_array (sourceItems n rows)
  simpa only [source, sourceItems, List.length_map, List.length_zipIdx] using trace

theorem boundedIds_fin_values (items : List (Fin bound)) :
    boundedIds bound (items.map Fin.val) = some items := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.map_cons, boundedIds, dite_eq_left head.isLt, ih, Option.map_some]

theorem decodeRow_matches (row : Row) (gate : Gate n owner) (matched : row.Matches gate) :
    decodeRow n owner row = some gate := by
  obtain ⟨tag, head, children, guards⟩ := matched
  cases gate with
  | zero => simp only [Gate.children, Gate.guardLabels] at children guards; simp [decodeRow, tag]
  | input channel =>
      have same := head channel rfl
      simp only [decodeRow, tag, same, dite_eq_left channel.isLt]
  | disj refs => simp only [decodeRow, tag, children, Gate.children, boundedIds_fin_values, Option.map_some]
  | guard child labels =>
      simp only [decodeRow, tag, children, guards, Gate.children, Gate.guardLabels,
        boundedIds_fin_values]
      rfl
  | liveAnd first second =>
      simp only [decodeRow, tag, children, Gate.children, boundedIds_fin_values]
      rfl

theorem readNode_matches (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (index : Fin graph.nodeCount) :
    readNode (source n rows) index.val = graph.node index := by
  have valid : index.val < rows.length := by rw [matched.length_eq]; exact index.isLt
  have decoded := decodeRow_matches _ (graph.node index) (matched.node index)
  have cell : (source n rows)[index.val]? = some (some ⟨index.val, graph.node index⟩) := by
    simp only [source, List.getElem?_toArray, sourceItems, List.getElem?_map,
      List.getElem?_zipIdx, List.getElem?_eq_getElem valid, Option.map_some,
      Nat.zero_add, decoded]
  simp [readNode, cell]

/-- One in-place indexed write has the exact functional-counter projection. -/
theorem arrayView_set (counts : Array Nat) (size : counts.size = n)
    (channel : Channel n) (value : Nat) :
    arrayView (counts.setIfInBounds channel.val value) = Function.update (arrayView counts) channel value := by
  funext other
  by_cases same : channel = other
  · subst other
    have valid : channel.val < counts.size := by rw [size]; exact channel.isLt
    simp only [arrayView, Array.getElem?_setIfInBounds_self_of_lt valid,
      Option.getD_some, Function.update_self]
  · have distinct : channel.val ≠ other.val := fun equal => same (Fin.ext equal)
    rw [Function.update_of_ne (Ne.symm same)]
    simp only [arrayView, Array.getElem?_setIfInBounds_ne distinct]

theorem emit_size (weights : Channel n → W) (total : W) (root b : Nat) (target : Channel n)
    (state : State n W) (operation : CursorOp n) :
    (emit weights total root b target state operation).counters.size = state.counters.size := by
  cases operation <;> simp only [emit, Array.size_setIfInBounds]
  all_goals split_ifs <;> rfl

/-- Array transitions refine the checked tagged transition exactly, including
zero/one weight changes, strict incumbent replacement and descriptor origin. -/
theorem emit_projection (weights : Channel n → W) (total : W) (root b : Nat) (target : Channel n)
    (state : State n W) (size : state.counters.size = n) (operation : CursorOp n) :
    view (emit weights total root b target state operation) =
      ForestWeightedDirect.emit weights total root b target (view state) operation := by
  cases operation with
  | leaf owner route head =>
      by_cases feasible : counter state head = 0 ∧ (b ≠ 1 ∨ counter state target = 0)
      · simp [emit, view, ForestWeightedDirect.emit, taggedStep, feasible] <;> rfl
      · simp [emit, view, ForestWeightedDirect.emit, taggedStep, feasible] <;> rfl
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel =>
      simp [emit, view, counter, ForestWeightedDirect.emit, taggedStep, GenericWeight.enter,
        enterGuards, arrayView_set state.counters size] <;> rfl
  | leave owner position channel =>
      simp [emit, view, counter, ForestWeightedDirect.emit, taggedStep, GenericWeight.leave,
        leaveGuards, arrayView_set state.counters size] <;> rfl

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestCursorTraversal
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

private theorem fold_refines (items : List α) (left : State n W → α → State n W)
    (right : ForestWeightedDirect.State n W → α → ForestWeightedDirect.State n W)
    (step : ∀ current item, current.counters.size = n →
      view (left current item) = right (view current) item ∧ (left current item).counters.size = n)
    (state : State n W) (size : state.counters.size = n) :
    view (items.foldl left state) = items.foldl right (view state) ∧
      (items.foldl left state).counters.size = n := by
  induction items generalizing state with
  | nil => exact ⟨rfl, size⟩
  | cons head rest ih =>
      obtain ⟨one, nextSize⟩ := step state head size
      obtain ⟨later, finalSize⟩ := ih (left state head) nextSize
      simp only [List.foldl_cons]
      exact ⟨later.trans (congrArg (fun initial => rest.foldl right initial) one), finalSize⟩

/-- The whole indexed traversal refines the frozen direct evaluator; its
counter array keeps its single allocated size through repeated guard labels. -/
theorem runNode_projection (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (weights : Channel n → W) (total : W) (root b : Nat) (target : Channel n) :
    ∀ (index : Fin graph.nodeCount) (state : State n W), state.counters.size = n →
      view (runNode (source n rows) weights total root b target index.val state) =
        ForestWeightedDirect.runNode graph weights total root b target index (view state) ∧
      (runNode (source n rows) weights total root b target index.val state).counters.size = n := by
  have claim : ∀ rank : Nat, ∀ index : Fin graph.nodeCount, index.val = rank →
      ∀ state : State n W, state.counters.size = n →
      view (runNode (source n rows) weights total root b target index.val state) =
        ForestWeightedDirect.runNode graph weights total root b target index (view state) ∧
      (runNode (source n rows) weights total root b target index.val state).counters.size = n := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro index same state size
      let entered := emit weights total root b target state (.node index.val)
      have enteredSize : entered.counters.size = n := (emit_size weights total root b target state _).trans size
      have enteredView := emit_projection weights total root b target state size (.node index.val)
      rw [runNode.eq_def, readNode_matches graph rows matched index, ForestWeightedDirect.runNode.eq_def]
      cases kind : graph.node index with
      | zero => exact ⟨enteredView, enteredSize⟩
      | liveAnd first second => exact ⟨enteredView, enteredSize⟩
      | input channel =>
          have next := emit_projection weights total root b target entered enteredSize (.leaf index.val [] channel)
          exact ⟨next.trans (congrArg (fun current => ForestWeightedDirect.emit weights total root b target current (.leaf index.val [] channel)) enteredView),
            (emit_size weights total root b target entered _).trans enteredSize⟩
      | disj children =>
          let left := fun current (item : Fin index.val × Nat) =>
            emit weights total root b target
              (runNode (source n rows) weights total root b target item.1.val
                (emit weights total root b target current (.down index.val item.2 item.1.val))) .up
          let right := fun current (item : Fin index.val × Nat) =>
            ForestWeightedDirect.emit weights total root b target
              (ForestWeightedDirect.runNode graph weights total root b target (graph.childIndex index item.1)
                (ForestWeightedDirect.emit weights total root b target current (.down index.val item.2 item.1.val))) .up
          have one : ∀ current item, current.counters.size = n →
              view (left current item) = right (view current) item ∧ (left current item).counters.size = n := by
            intro current item currentSize
            let down := emit weights total root b target current (.down index.val item.2 item.1.val)
            have downSize : down.counters.size = n := (emit_size weights total root b target current _).trans currentSize
            have earlier : (graph.childIndex index item.1).val < rank := by
              rw [DAG.childIndex_val, ← same]
              exact item.1.isLt
            obtain ⟨visitedView, visitedSize⟩ := ih _ earlier (graph.childIndex index item.1) rfl down downSize
            simp only [DAG.childIndex_val] at visitedView visitedSize
            have upView := emit_projection weights total root b target
              (runNode (source n rows) weights total root b target item.1.val down) visitedSize .up
            have downView := emit_projection weights total root b target current currentSize (.down index.val item.2 item.1.val)
            constructor
            · dsimp only [left, right]
              rw [upView, visitedView, downView]
            · exact (emit_size weights total root b target _ .up).trans visitedSize
          obtain ⟨foldView, foldSize⟩ := fold_refines children.zipIdx left right one entered enteredSize
          exact ⟨foldView.trans (congrArg (fun current => children.zipIdx.foldl right current) enteredView), foldSize⟩
      | guard child labels =>
          let indexed := labels.zipIdx
          let enterLeft := fun current (item : Channel n × Nat) => emit weights total root b target current (.enter index.val item.2 item.1)
          let enterRight := fun current (item : Channel n × Nat) => ForestWeightedDirect.emit weights total root b target current (.enter index.val item.2 item.1)
          have enterOne : ∀ current item, current.counters.size = n →
              view (enterLeft current item) = enterRight (view current) item ∧ (enterLeft current item).counters.size = n := by
            intro current item currentSize
            exact ⟨emit_projection weights total root b target current currentSize _,
              (emit_size weights total root b target current _).trans currentSize⟩
          obtain ⟨guardView, guardSize⟩ := fold_refines indexed enterLeft enterRight enterOne entered enteredSize
          let guarded := indexed.foldl enterLeft entered
          let down := emit weights total root b target guarded (.down index.val 0 child.val)
          have downSize : down.counters.size = n := (emit_size weights total root b target guarded _).trans guardSize
          have earlier : (graph.childIndex index child).val < rank := by
            rw [DAG.childIndex_val, ← same]
            exact child.isLt
          obtain ⟨visitedView, visitedSize⟩ := ih _ earlier (graph.childIndex index child) rfl down downSize
          simp only [DAG.childIndex_val] at visitedView visitedSize
          let visited := runNode (source n rows) weights total root b target child.val down
          let up := emit weights total root b target visited .up
          have upSize : up.counters.size = n := (emit_size weights total root b target visited _).trans visitedSize
          have upView := emit_projection weights total root b target visited visitedSize .up
          have downView := emit_projection weights total root b target guarded guardSize (.down index.val 0 child.val)
          let leaveLeft := fun current (item : Channel n × Nat) => emit weights total root b target current (.leave index.val item.2 item.1)
          let leaveRight := fun current (item : Channel n × Nat) => ForestWeightedDirect.emit weights total root b target current (.leave index.val item.2 item.1)
          have leaveOne : ∀ current item, current.counters.size = n →
              view (leaveLeft current item) = leaveRight (view current) item ∧ (leaveLeft current item).counters.size = n := by
            intro current item currentSize
            exact ⟨emit_projection weights total root b target current currentSize _,
              (emit_size weights total root b target current _).trans currentSize⟩
          obtain ⟨foldView, foldSize⟩ := fold_refines indexed.reverse leaveLeft leaveRight leaveOne up upSize
          constructor
          · change view (indexed.reverse.foldl leaveLeft up) = _
            rw [foldView, upView]
            dsimp only [visited]
            rw [visitedView, downView, guardView, enteredView]
            simp only [indexed, enterRight, leaveRight, DAG.childIndex_val]
          · exact foldSize
  intro index state size
  exact claim index.val index rfl state size

private theorem directRoots_fold (graph : DAG n) (weights : Channel n → W) (total : W)
    (b : Nat) (target : Channel n) (positions : List (Fin graph.roots.length))
    (state : ForestWeightedDirect.State n W) :
    ForestWeightedDirect.runRoots graph weights total b target positions state =
      positions.foldl (fun current position =>
        ForestWeightedDirect.runNode graph weights total position.val b target (graph.roots.get position)
          { current with data := { current.data with descriptors := ForestCursorDescriptors.beginRoot current.data.descriptors } }) state := by
  induction positions generalizing state with
  | nil => rfl
  | cons position rest ih =>
      rw [ForestWeightedDirect.runRoots, List.foldl_cons, ih]

theorem root_positions (graph : DAG n) (roots : List Nat) (matched : RootsMatch graph roots) :
    roots.zipIdx = (List.finRange graph.roots.length).map (fun position => ((graph.roots.get position).val, position.val)) := by
  have rootsEq : roots = graph.roots.map Fin.val := matched
  apply List.ext_getElem
  · simp [rootsEq]
  · intro index firstValid secondValid
    simp [rootsEq, List.get_eq_getElem]

theorem runRoots_projection (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (total : W) (b : Nat) (target : Channel n)
    (state : State n W) (size : state.counters.size = n) :
    view (runRoots (source n rows) weights total b target roots state) =
      ForestWeightedDirect.runRoots graph weights total b target (List.finRange graph.roots.length) (view state) ∧
    (runRoots (source n rows) weights total b target roots state).counters.size = n := by
  let left := fun (current : State n W) (position : Fin graph.roots.length) =>
    runNode (source n rows) weights total position.val b target (graph.roots.get position).val
      { current with descriptors := ForestCursorDescriptors.beginRoot current.descriptors }
  let right := fun (current : ForestWeightedDirect.State n W) (position : Fin graph.roots.length) =>
    ForestWeightedDirect.runNode graph weights total position.val b target (graph.roots.get position)
      { current with data := { current.data with descriptors := ForestCursorDescriptors.beginRoot current.data.descriptors } }
  have one : ∀ current position, current.counters.size = n →
      view (left current position) = right (view current) position ∧ (left current position).counters.size = n := by
    intro current position currentSize
    exact runNode_projection graph rows matched weights total position.val b target (graph.roots.get position)
      { current with descriptors := ForestCursorDescriptors.beginRoot current.descriptors } currentSize
  have whole := fold_refines (List.finRange graph.roots.length) left right one state size
  simpa only [runRoots, root_positions graph roots rootsMatch, List.foldl_map, directRoots_fold, left, right] using whole

theorem cached_total (weights : Channel n → W) :
    (List.finRange n).foldl (fun value channel => value + weights channel) 0 =
      (ForestWeightedTrace.cacheTotal weights).1 := by
  rw [← List.foldl_map (f := weights) (g := (· + ·))]
  have items : (List.finRange n).map weights = List.ofFn weights := by rw [← List.ofFn_eq_map]
  rw [items, ← List.sum_eq_foldl, List.sum_ofFn]
  exact (ForestWeightedTrace.cacheTotal_correct weights).1.symm

theorem initial_view (n : Nat) :
    view (⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩ : State n W) =
      ⟨⟨((fun _ => 0), 0), ForestCursorDescriptors.initial, none⟩, 0, n⟩ := by
  have zero : arrayView (Array.replicate n 0) = (fun _ : Channel n => 0) := by
    funext channel
    simp [arrayView, channel.isLt]
  simp only [view, counter, zero]

theorem runAll_projection (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    (runAll (source n rows) weights b target roots).1 = (ForestWeightedDirect.runAll graph weights b target).1 ∧
    view (runAll (source n rows) weights b target roots).2 = (ForestWeightedDirect.runAll graph weights b target).2 := by
  have projected := runRoots_projection graph rows roots matched rootsMatch weights
    (ForestWeightedTrace.cacheTotal weights).1 b target
    (⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩ : State n W) (by simp)
  have calls := (ForestWeightedTrace.cacheTotal_correct weights).2
  constructor
  · exact cached_total weights
  · simpa only [runAll, ForestWeightedDirect.runAll, cached_total, initial_view, calls] using projected.1

/-- The indexed evaluator inherits the original forest arithmetic bound, with
the total computed once and no reconstruction inside candidate callbacks. -/
theorem runAll_arithmetic_bound (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootsMatch : RootsMatch graph roots) (forest : graph.FormulaForest)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    (runAll (source n rows) weights b target roots).2.arithmetic ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences := by
  have projected := congrArg ForestWeightedDirect.State.arithmetic
    (runAll_projection graph rows roots matched rootsMatch weights b target).2
  change (runAll (source n rows) weights b target roots).2.arithmetic = _ at projected
  rw [projected]
  exact ForestWeightedDirect.runAll_arithmetic_bound graph forest weights b target

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCounter Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorAllRootsExecution
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestWitnessWalk Controller.Cost.ForestWitnessMarshal
open Controller.Cost.ForestWeightedPhysicalOptimal
variable {width n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The selected result of the actual indexed-source/array-counter evaluator
supplies the physically marshaled root and pointer. Reconstruction and original
channel output occur once after selection. Source cache loading, descriptor
allocation and weight bit costs keep their explicit separate interfaces. -/
theorem indexed_selected_emission (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (forest : graph.FormulaForest) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (runAll (source n rows) weights b target roots).2.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    (runAll (source n rows) weights b target roots).2.arithmetic ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences ∧
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (setupHeap width (cacheHeap width heap rows roots) graph) base address
            (word width candidate.root) (word width candidate.pointer)).frame stack output)
          final ticks peak ∧
        ticks ≤ 14 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          10 * n + 16 ∧
        peak ≤ 5 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output := by
  have projected := congrArg (fun state : ForestWeightedDirect.State n W => state.data.selected)
    (runAll_projection graph rows roots matched rootMatches weights b target).2
  change (runAll (source n rows) weights b target roots).2.selected =
    (ForestWeightedDirect.runAll graph weights b target).2.data.selected at projected
  have selectedDirect : (ForestWeightedDirect.runAll graph weights b target).2.data.selected = some candidate := by
    rw [← projected]
    exact selected
  obtain ⟨arithmetic, physical⟩ := ForestWeightedCaller.direct_selected_emission program heap graph
    forest guarded rows roots matched rootMatches weights nonnegative b target candidate selectedDirect
    countFits positionFits base countAddress address stack output countValid countWord heapFits programFits block
  exact ⟨runAll_arithmetic_bound graph rows roots matched rootMatches forest weights b target, physical⟩

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorDescriptors
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorMaterialize
open Controller.Cost.GateProgram
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The runtime builder is the one shared descriptor store specified by the
source graph. This equality is a refinement fact, not a second runtime scan. -/
theorem runAll_descriptors (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    (runAll (source n rows) weights b target roots).2.descriptors = buildRoots graph := by
  have indexed := congrArg (fun state : ForestWeightedDirect.State n W => state.data.descriptors)
    (runAll_projection graph rows roots matched rootsMatch weights b target).2
  have direct := congrArg TaggedState.descriptors
    (ForestWeightedDirect.runAll_projection graph weights b target).1
  have scanned := ForestWeightedSemantics.roots_descriptors graph weights b target
    (ForestWeightedTrace.cacheTotal weights).1 (List.finRange graph.roots.length)
    (⟨((fun _ => 0), 0), initial, none⟩ : TaggedState n W)
  exact indexed.trans (direct.trans scanned)

/-- Physical setup operands come from the actual computed descriptor entries;
they do not rerun the decoder or construct any saved candidate route. -/
def descriptorValues (state : State n W) : List Nat :=
  fields state.descriptors.entries.reverse ++ List.replicate (n + 3) 0

def descriptorCode (width : Nat) (state : State n W) : ForestCounter.Code width :=
  writeCode width (descriptorValues state)

theorem descriptorValues_refines (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    descriptorValues (runAll (source n rows) weights b target roots).2 = setupValues graph := by
  unfold descriptorValues setupValues
  rw [runAll_descriptors graph rows roots matched rootsMatch weights b target]

/-- A once-only fetched materialization allocates the descriptor/counter
store whose operands were computed by the indexed weighted traversal. -/
theorem descriptor_setup_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (base : Nat) (address loaded temporary : Word width)
    (fits : base + 4 * (buildRoots graph).count + 2 * (n + 3) < 2 ^ width)
    (room : heap.size + 2 * (buildRoots graph).count + (n + 3) ≤ 2 ^ width)
    (block : BlockAt program base (descriptorCode width (runAll (source n rows) weights b target roots).2)) :
    ∃ finalTemporary : Word width,
      Execution program (counterState heap base address loaded temporary)
        (counterState (setupHeap width heap graph)
          (base + (4 * (buildRoots graph).count + 2 * (n + 3))) address loaded finalTemporary)
        (4 * (buildRoots graph).count + 2 * (n + 3))
        (5 + heap.size + 2 * (buildRoots graph).count + (n + 3)) := by
  have operands := descriptorValues_refines graph rows roots matched rootsMatch weights b target
  have actual : BlockAt program base (setupCode width graph) := by
    simpa only [descriptorCode, operands, setupCode] using block
  exact setup_execution program heap graph base address loaded temporary (by omega) room actual

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestWeightedTagged
open Controller.Decoder

/-- Two resident constants encode the actual final incumbent identifiers. -/
def candidateCode (width : Nat) (candidate : Candidate W) : ForestCounter.Code width :=
  [.constant 1 (word width candidate.root), .constant 2 (word width candidate.pointer)]

private theorem candidate_root_transition (program : Program width 4)
    (heap : Array (Word width)) (cursor root : Nat) (address loaded temporary : Word width)
    (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.constant 1 (word width root))) :
    programStep program (counterState heap cursor address loaded temporary) =
      some (counterState heap (cursor + 1) address (word width root) temporary) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.constant (1 : Fin 4) (word width root))
    (counterState heap cursor address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address loaded temporary).advance.put 1
    (word width root)) = _
  have advanced : (counterState heap cursor address loaded temporary).advance =
      counterState heap (cursor + 1) address loaded temporary := by
    unfold Controller.Cost.State.advance counterState
    rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]
  rw [advanced]
  congr 1
  unfold Controller.Cost.State.put counterState
  congr 1
  funext register
  by_cases zero : register = 0
  · subst register; simp
  · by_cases one : register = 1 <;> simp [zero, one]

/-- The selected identifiers are formed by real fetched instructions. -/
theorem candidate_execution (program : Program width 4) (heap : Array (Word width))
    (base : Nat) (candidate : Candidate W) (address loaded temporary : Word width)
    (fits : base + 2 < 2 ^ width)
    (block : BlockAt program base (candidateCode width candidate)) :
    Execution program (counterState heap base address loaded temporary)
      (counterState heap (base + 2) address (word width candidate.root)
        (word width candidate.pointer)) 2 (5 + heap.size) := by
  have first := candidate_root_transition program heap base candidate.root address loaded temporary
    (by omega) (by simpa [candidateCode] using block 0 (by simp [candidateCode]))
  have second := increment_transition program heap (base + 1) candidate.pointer address
    (word width candidate.root) temporary (by omega)
    (by simpa [candidateCode] using block 1 (by simp [candidateCode]))
  simp only [Nat.add_assoc] at second
  have trace := Execution.cons first (Execution.cons second
    (Execution.refl (counterState heap (base + 2) address (word width candidate.root)
      (word width candidate.pointer))))
  simpa only [counterState_liveWords, Nat.zero_add, Nat.max_self] using trace

/-- Resident code is assembled by the actual list-to-array push recursion. -/
def materialize (prior : Program width 4) (items : ForestCounter.Code width) : Program width 4 :=
  items.toArrayAux prior

theorem materialize_trace (prior : Program width 4) (items : ForestCounter.Code width) :
    CompilerArrayTrace.Trace items prior (materialize prior items) items.length :=
  CompilerArrayTrace.exists_trace items prior

theorem materialize_block (prior : Program width 4)
    (before block after : ForestCounter.Code width) :
    BlockAt (materialize prior (before ++ block ++ after)) (prior.size + before.length) block := by
  intro index within
  have contents := (CompilerArrayTrace.exact_trace
    (materialize_trace prior (before ++ block ++ after))).2.2
  have getter := congrArg (fun values : ForestCounter.Code width =>
    values[prior.size + before.length + index]?) contents
  simp only [Array.getElem?_toList, List.append_assoc] at getter
  simp only [List.append_assoc]
  rw [getter]
  rw [List.getElem?_append_right (by simp only [Array.length_toList]; omega)]
  simp only [Array.length_toList]
  have first : prior.size + before.length + index - prior.size = before.length + index := by omega
  rw [first, List.getElem?_append_right (by omega)]
  have second : before.length + index - before.length = index := by omega
  rw [second, List.getElem?_append_left within]

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorMaterialize
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Materialize the computed descriptors and form the selected registers once,
leaving the machine at the sole reconstruction entry. -/
theorem computed_prefix_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootsMatch : ForestIndexedOperands.RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) (candidate : Candidate W)
    (base : Nat) (address loaded temporary : Word width) (stack output : List (Word width))
    (fits : base + (4 * (buildRoots graph).count + 2 * (n + 3)) + 2 < 2 ^ width)
    (room : heap.size + 2 * (buildRoots graph).count + (n + 3) ≤ 2 ^ width)
    (block : BlockAt program base
      (descriptorCode width (runAll (source n rows) weights b target roots).2 ++
        candidateCode width candidate)) :
    Execution program ((counterState heap base address loaded temporary).frame stack output)
      ((counterState (setupHeap width heap graph)
        (base + (4 * (buildRoots graph).count + 2 * (n + 3)) + 2)
        address (word width candidate.root) (word width candidate.pointer)).frame stack output)
      (4 * (buildRoots graph).count + 2 * (n + 3) + 2)
      (5 + heap.size + 2 * (buildRoots graph).count + (n + 3) + stack.length + output.length) := by
  have operands := descriptorValues_refines graph rows roots matched rootsMatch weights b target
  have prefixLength : (descriptorCode width (runAll (source n rows) weights b target roots).2).length =
      4 * (buildRoots graph).count + 2 * (n + 3) := by
    simp only [descriptorCode, operands, writeCode_length, setupValues_length]
    omega
  obtain ⟨last, leadingCode⟩ := descriptor_setup_execution program heap graph rows roots matched rootsMatch
    weights b target base address loaded temporary (by omega) room
    (BlockAt.prefix program base _ _ block)
  have constants : BlockAt program
      (base + (4 * (buildRoots graph).count + 2 * (n + 3))) (candidateCode width candidate) := by
    simpa only [prefixLength] using BlockAt.suffix program base _ _ block
  have chosen := candidate_execution program (setupHeap width heap graph)
    (base + (4 * (buildRoots graph).count + 2 * (n + 3))) candidate address loaded last fits constants
  have joined := leadingCode.append chosen
  simpa only [setupHeap_size, Nat.add_assoc, Nat.max_self] using joined.frame stack output

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorAllRootsExecution Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWitnessMarshal Controller.Cost.ForestWeightedPhysicalOptimal
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The resident weighted suffix is formed from the computed descriptor store
and incumbent; reconstruction is shared and begins after two identifier writes. -/
def selectedItems (width : Nat) (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (state : State n W) (candidate : Candidate W)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (entry countAddress : Nat) : ForestCounter.Code width :=
  let leadingCode := descriptorCode width state ++ candidateCode width candidate
  let base := entry + leadingCode.length
  leadingCode ++ preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
    (setupLayout (cacheHeap width heap rows roots) graph).best
    (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
    (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
    ForestWitnessWalk.code width (base + 25)
      (ForestWitnessPath.packetLayout heap.size rows.length
        (setupOffset (cacheHeap width heap rows roots) graph)) countAddress

/-- Each actual resident instruction is pushed once into the caller's program.
This construction trace is separate from fetched machine ticks. -/
theorem selectedItems_formation (prior : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (rows : List Row) (roots : List Nat) (state : State n W)
    (candidate : Candidate W) (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (countAddress : Nat) :
    CompilerArrayTrace.Trace
      (selectedItems width heap graph rows roots state candidate countFits positionFits prior.size countAddress)
      prior
      (materialize prior (selectedItems width heap graph rows roots state candidate countFits positionFits prior.size countAddress))
      (selectedItems width heap graph rows roots state candidate countFits positionFits prior.size countAddress).length :=
  materialize_trace _ _

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorAllRootsExecution Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestWeightedGlobal
open Controller.Cost.ForestWitnessMarshal Controller.Cost.ForestWeightedPhysicalOptimal
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The actual resident array executes computed descriptor allocation,
identifier formation and the sole optimal original-channel witness suffix. -/
theorem selected_prefixed_emission (prior : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (forest : graph.FormulaForest) (guarded : graph.Guarded)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : Nat) (target : Channel n)
    (candidate : Candidate W)
    (selected : (runAll (source n rows) weights b target roots).2.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (countAddress : Nat) (address loaded temporary : Word width)
    (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : prior.size + (4 * (buildRoots graph).count + 2 * (n + 3)) + 94 < 2 ^ width) :
    let state := (runAll (source n rows) weights b target roots).2
    let program := materialize prior (selectedItems width heap graph rows roots state candidate
      countFits positionFits prior.size countAddress)
    state.arithmetic ≤ n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences ∧
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (cacheHeap width heap rows roots) prior.size address loaded temporary).frame stack output)
          final ticks peak ∧
        ticks ≤ 18 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          12 * n + 24 ∧
        peak ≤ 5 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output := by
  let state := (runAll (source n rows) weights b target roots).2
  let leadingCode := descriptorCode width state ++ candidateCode width candidate
  let base := prior.size + leadingCode.length
  let suffix := preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
    (setupLayout (cacheHeap width heap rows roots) graph).best
    (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
    (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
    ForestWitnessWalk.code width (base + 25)
      (ForestWitnessPath.packetLayout heap.size rows.length
        (setupOffset (cacheHeap width heap rows roots) graph)) countAddress
  let program := materialize prior (leadingCode ++ suffix)
  have programEq : program = materialize prior (selectedItems width heap graph rows roots state candidate
      countFits positionFits prior.size countAddress) := by
    simp only [program, selectedItems, leadingCode, base, suffix, List.append_assoc]
  have prefixLength : leadingCode.length = 4 * (buildRoots graph).count + 2 * (n + 3) + 2 := by
    have operands := descriptorValues_refines graph rows roots matched rootMatches weights b target
    simp only [leadingCode, List.length_append, descriptorCode, state, operands,
      ForestCursorMaterialize.writeCode_length, setupValues_length, candidateCode,
      List.length_cons, List.length_nil]
    omega
  have prefixBlock : BlockAt program prior.size leadingCode := by
    simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.add_zero, program] using
      materialize_block prior [] leadingCode suffix
  have suffixBlock : BlockAt program base suffix := by
    simpa only [List.append_nil, program, base] using materialize_block prior leadingCode suffix []
  have prefixTrace := computed_prefix_execution program (cacheHeap width heap rows roots) graph rows roots
    matched rootMatches weights b target candidate prior.size address loaded temporary stack output
    (by omega) (by simpa only [setupHeap_size] using heapFits) prefixBlock
  obtain ⟨arithmetic, position, rootEq, blocked, final, ticks, peak, admissible, feasible,
      score, optimal, suffixTrace, time, space, finalStack, finalOutput⟩ :=
    indexed_selected_emission program heap graph forest guarded rows roots matched rootMatches weights
      nonnegative b target candidate selected countFits positionFits base countAddress address stack output
      countValid countWord heapFits (by dsimp only [base]; rw [prefixLength]; omega) suffixBlock
  have boundary : base = prior.size + (4 * (buildRoots graph).count + 2 * (n + 3)) + 2 := by
    dsimp only [base]
    rw [prefixLength]
    omega
  rw [boundary] at suffixTrace
  have joined := prefixTrace.append suffixTrace
  refine ⟨arithmetic, position, rootEq, blocked, final,
    4 * (buildRoots graph).count + 2 * (n + 3) + 2 + ticks,
    max (5 + (cacheHeap width heap rows roots).size + 2 * (buildRoots graph).count + (n + 3) +
      stack.length + output.length) peak,
    admissible, feasible, score, optimal, ?_, by omega, ?_, finalStack, finalOutput⟩
  · simpa only [programEq, Nat.add_assoc] using joined
  · apply max_le
    · simp only [setupHeap_size]
      omega
    · exact space

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorCharging
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestCursorDescriptors
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

private theorem directRoots_operations (graph : DAG n) (weights : Channel n → W) (total : W)
    (b : Nat) (target : Channel n) (positions : List (Fin graph.roots.length))
    (state : ForestWeightedDirect.State n W) :
    (ForestWeightedDirect.runRoots graph weights total b target positions state).operations =
      state.operations + (positions.map fun position =>
        (cursorOps graph (graph.roots.get position) []).length).sum := by
  induction positions generalizing state with
  | nil => simp [ForestWeightedDirect.runRoots]
  | cons position rest ih =>
    let started := { state with data := { state.data with descriptors := beginRoot state.data.descriptors } }
    let current := ForestWeightedDirect.runNode graph weights total position.val b target
      (graph.roots.get position) started
    have one := (ForestWeightedDirect.runOps_counts weights total position.val b target started
      (cursorOps graph (graph.roots.get position) [])).1
    rw [← ForestWeightedDirect.runNode_eq graph weights total position.val b target
      (graph.roots.get position) [] started] at one
    have later := ih current
    change (ForestWeightedDirect.runRoots graph weights total b target rest current).operations = _
    rw [later]
    change current.operations + _ = _
    rw [show current.operations = state.operations +
      (cursorOps graph (graph.roots.get position) []).length from one]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The actual indexed evaluator has a linear source/counter operation count.
The cached n weight additions are accounted for separately. -/
theorem runAll_operations_bound (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootsMatch : ForestIndexedOperands.RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    (runAll (source n rows) weights b target roots).2.operations ≤
      4 * (graph.roots.length + graph.childIncidences) + 2 * graph.guardIncidences := by
  have projected := congrArg ForestWeightedDirect.State.operations
    (runAll_projection graph rows roots matched rootsMatch weights b target).2
  change (runAll (source n rows) weights b target roots).2.operations =
    (ForestWeightedDirect.runAll graph weights b target).2.operations at projected
  rw [projected]
  have exactOps := directRoots_operations graph weights (ForestWeightedTrace.cacheTotal weights).1 b target
    (List.finRange graph.roots.length)
    (⟨⟨((fun _ => 0), 0), initial, none⟩, 0, (ForestWeightedTrace.cacheTotal weights).2.length⟩ :
      ForestWeightedDirect.State n W)
  have exactAll : (ForestWeightedDirect.runAll graph weights b target).2.operations =
      ((List.finRange graph.roots.length).map fun position =>
        (cursorOps graph (graph.roots.get position) []).length).sum := by
    simpa only [ForestWeightedDirect.runAll, Nat.zero_add,
      (ForestWeightedTrace.cacheTotal_correct weights).1] using exactOps
  rw [exactAll]
  have budgetEq : ((List.finRange graph.roots.length).map fun position =>
      (cursorOps graph (graph.roots.get position) []).length).sum = allRootBudget graph := by
    simp only [cursor_length]
    have mapped := congrArg (List.map (operationBudget graph)) (List.map_get_finRange graph.roots)
    simpa only [List.map_map, Function.comp_def, allRootBudget] using congrArg List.sum mapped
  rw [budgetEq]
  exact all_root_budget_bound graph forest

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedTagged
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The resident list size follows the computed descriptor count, with a
constant-size reconstruction/emission body shared by the selected route. -/
theorem selectedItems_length (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W)
    (b : Nat) (target : Channel n) (candidate : Candidate W)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (entry countAddress : Nat) :
    (selectedItems width heap graph rows roots (runAll (source n rows) weights b target roots).2
      candidate countFits positionFits entry countAddress).length =
      4 * (buildRoots graph).count + 2 * n + 100 := by
  simp only [selectedItems, List.length_append, descriptorCode,
    descriptorValues_refines graph rows roots matched rootMatches weights b target,
    ForestCursorMaterialize.writeCode_length, setupValues_length, candidateCode,
    List.length_cons, List.length_nil, ForestWitnessMarshal.preludeCode_length,
    ForestWitnessWalk.code_length]
  omega

/-- Captured parent records are bounded by the original positional source
operation traversal; duplicate declared positions remain charged. -/
theorem computed_descriptor_count_bound (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W)
    (b : Nat) (target : Channel n) :
    (runAll (source n rows) weights b target roots).2.descriptors.count ≤
      4 * (graph.roots.length + graph.childIncidences) + 2 * graph.guardIncidences := by
  rw [runAll_descriptors graph rows roots matched rootMatches weights b target]
  have count := ForestCursorWholeProgram.descriptor_count_le_operations graph
  rw [ForestCursorWholeProgram.rootOperations_total] at count
  exact count.trans (ForestCursorCharging.all_root_budget_bound graph forest)

/-- Descriptor setup and the one emitted witness are charged to original
forest incidences, separately from generic ordered-weight primitive calls. -/
theorem prefixed_ticks_forest (graph : DAG n) (forest : graph.FormulaForest)
    (ticks : Nat)
    (bounded : ticks ≤ 18 * (buildRoots graph).count +
      ForestWitnessAccept.sourceBudget graph graph.nodeCount + 12 * n + 24) :
    ticks ≤ 72 * (graph.roots.length + graph.childIncidences) +
      47 * graph.guardIncidences + 36 * graph.nodeCount + 12 * n + 24 := by
  have count := ForestCursorWholeProgram.descriptor_count_le_operations graph
  rw [ForestCursorWholeProgram.rootOperations_total] at count
  have visits := ForestCursorCharging.all_root_budget_bound graph forest
  rw [ForestWeightedCaller.sourceBudget_exact] at bounded
  omega

/-- Failure is an exact negative result of the actual source-array traversal. -/
theorem indexed_none_iff (graph : DAG n) (guarded : graph.Guarded)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : Nat) (target : Channel n) :
    (runAll (source n rows) weights b target roots).2.selected = none ↔
      ¬ ∃ position : Fin graph.roots.length, ∃ K : Finset (Channel n),
        Controller.Admissible b target K ∧
          graph.eval (Controller.assignmentOfSet K) (graph.roots.get position) = true := by
  have indexed := congrArg (fun state : ForestWeightedDirect.State n W => state.data.selected)
    (runAll_projection graph rows roots matched rootMatches weights b target).2
  have direct := congrArg TaggedState.selected (ForestWeightedDirect.runAll_projection graph weights b target).1
  change (runAll (source n rows) weights b target roots).2.selected =
      (ForestWeightedDirect.runAll graph weights b target).2.data.selected at indexed
  rw [indexed, direct]
  exact ForestWeightedOptimal.global_none_iff graph guarded weights nonnegative b target

end Controller.Cost.ForestWeightedIndexed
namespace Controller.Cost.ForestWeightedIndexed

/-- Each original incidence executes a rank comparison; valid incidences
allocate one decoded finite identifier. Failure stops at its actual position. -/
inductive IdValidationTrace (bound : Nat) : List Nat → Option (List (Fin bound)) → Nat → Nat → Prop
  | nil : IdValidationTrace bound [] (some []) 0 0
  | valid (value : Nat) (valid : value < bound) (rest : List Nat)
      (result : Option (List (Fin bound))) (checks cells : Nat)
      (next : IdValidationTrace bound rest result checks cells) :
      IdValidationTrace bound (value :: rest) (result.map (⟨value, valid⟩ :: ·))
        (checks + 1) (cells + if result.isSome then 1 else 0)
  | invalid (value : Nat) (invalid : ¬ value < bound) (rest : List Nat) :
      IdValidationTrace bound (value :: rest) none 1 0

/-- The operational validator relation follows the actual boundedIds branch,
including early rejection. Its work is not inferred from final array size. -/
theorem boundedIds_validation (bound : Nat) (values : List Nat) :
    ∃ checks cells, IdValidationTrace bound values (boundedIds bound values) checks cells ∧
      checks ≤ values.length ∧ cells ≤ values.length := by
  induction values with
  | nil => exact ⟨0, 0, IdValidationTrace.nil, by simp, by simp⟩
  | cons value rest ih =>
    by_cases valid : value < bound
    · obtain ⟨checks, cells, trace, checkBound, cellBound⟩ := ih
      refine ⟨checks + 1, cells + if (boundedIds bound rest).isSome then 1 else 0, ?_, ?_, ?_⟩
      · simpa only [boundedIds, dite_eq_left valid] using
          IdValidationTrace.valid value valid rest (boundedIds bound rest) checks cells trace
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]
        split_ifs <;> omega
    · exact ⟨1, 0, by simpa only [boundedIds, dite_eq_right valid] using
        IdValidationTrace.invalid value valid rest, by simp, by simp⟩

/-- Successful decoding compares every original incidence, preserving repeated
identifier occurrences rather than collapsing them into a finite set. -/
theorem boundedIds_validation_success (trace : IdValidationTrace bound values decoded checks cells) :
    ∀ result, decoded = some result →
      checks = values.length ∧ cells = values.length ∧ result.map Fin.val = values := by
  induction trace with
  | nil => intro result same; cases same; simp
  | valid value valid rest prior checks cells next ih =>
    intro result same
    cases prior with
    | none => cases same
    | some tail =>
      have exactTail := ih tail rfl
      have equal : (⟨value, valid⟩ :: tail : List (Fin bound)) = result := Option.some.inj same
      rw [← equal]
      simp only [Option.isSome_some, ite_true, List.length_cons, List.map_cons,
        exactTail.1, exactTail.2.1, exactTail.2.2, and_self]
  | invalid value invalid rest => intro result same; cases same

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands

/-- Operational decoding records the tag branch and exactly the incidence
validators called by that branch. Scalar tag/arity/head tests have a fixed
constant charge; the counted identifier traces account for every list scan. -/
inductive RowValidationTrace (n owner : Nat) (row : Row) : Option (Gate n owner) → Nat → Nat → Prop
  | zero (kind : row.tag = 0) : RowValidationTrace n owner row (some .zero) 1 1
  | input (kind : row.tag = 1) :
      RowValidationTrace n owner row
        (if valid : row.head < n then some (.input ⟨row.head, valid⟩) else none) 2 1
  | disj (kind : row.tag = 2) (result : Option (List (Fin owner))) (checks cells : Nat)
      (trace : IdValidationTrace owner row.children result checks cells) :
      RowValidationTrace n owner row (result.map Gate.disj) (checks + 1) (cells + 1)
  | guardAbsent (kind : row.tag = 3) (checks cells : Nat)
      (trace : IdValidationTrace owner row.children none checks cells) :
      RowValidationTrace n owner row none (checks + 1) cells
  | guardPresent (kind : row.tag = 3) (children : List (Fin owner))
      (labels : Option (List (Fin n))) (childChecks childCells guardChecks guardCells : Nat)
      (childTrace : IdValidationTrace owner row.children (some children) childChecks childCells)
      (guardTrace : IdValidationTrace n row.guards labels guardChecks guardCells) :
      RowValidationTrace n owner row
        (labels.bind fun guards => match children with
          | [child] => some (.guard child guards)
          | _ => none)
        (childChecks + guardChecks + 2) (childCells + guardCells + 1)
  | liveAnd (kind : row.tag = 4) (children : Option (List (Fin owner))) (checks cells : Nat)
      (trace : IdValidationTrace owner row.children children checks cells) :
      RowValidationTrace n owner row
        (children.bind fun list => match list with
          | [first, second] => some (.liveAnd first second)
          | _ => none)
        (checks + 2) (cells + 1)
  | unsupported (kind : 5 ≤ row.tag) : RowValidationTrace n owner row none 1 0

private theorem idTrace_bounds (trace : IdValidationTrace bound values result checks cells) :
    checks ≤ values.length ∧ cells ≤ values.length := by
  induction trace with
  | nil => simp
  | valid value valid rest result checks cells next ih =>
      simp only [List.length_cons]
      split_ifs <;> omega
  | invalid value invalid rest => simp

/-- Row validation and its costs follow the actual decoder; no semantic node
function or pre-decoded input is called by this relation. -/
theorem decodeRow_validation (n owner : Nat) (row : Row) :
    ∃ checks cells, RowValidationTrace n owner row (decodeRow n owner row) checks cells ∧
      checks ≤ 3 + row.children.length + row.guards.length ∧
      cells ≤ 1 + row.children.length + row.guards.length := by
  obtain ⟨cc, cs, childTrace, childChecks, childCells⟩ := boundedIds_validation owner row.children
  obtain ⟨gc, gs, guardTrace, guardChecks, guardCells⟩ := boundedIds_validation n row.guards
  by_cases zero : row.tag = 0
  · exact ⟨1, 1, by simpa only [decodeRow, zero] using RowValidationTrace.zero zero, by omega, by omega⟩
  by_cases input : row.tag = 1
  · exact ⟨2, 1, by simpa only [decodeRow, input] using RowValidationTrace.input input, by omega, by omega⟩
  by_cases disj : row.tag = 2
  · refine ⟨cc + 1, cs + 1, ?_, by omega, by omega⟩
    simpa only [decodeRow, disj] using RowValidationTrace.disj disj _ cc cs childTrace
  by_cases guard : row.tag = 3
  · cases childResult : boundedIds owner row.children with
    | none =>
      rw [childResult] at childTrace
      refine ⟨cc + 1, cs, ?_, by omega, by omega⟩
      simpa only [decodeRow, guard, childResult, Option.bind_eq_bind, Option.bind_none] using
        RowValidationTrace.guardAbsent guard cc cs childTrace
    | some children =>
      rw [childResult] at childTrace
      refine ⟨cc + gc + 2, cs + gs + 1, ?_, by omega, by omega⟩
      have actual := RowValidationTrace.guardPresent guard children _ cc cs gc gs childTrace guardTrace
      cases children with
      | nil => simpa only [decodeRow, guard, childResult, Option.bind_eq_bind, Option.bind_some] using actual
      | cons child tail =>
        cases tail <;> simpa only [decodeRow, guard, childResult, Option.bind_eq_bind, Option.bind_some] using actual
  by_cases live : row.tag = 4
  · refine ⟨cc + 2, cs + 1, ?_, by omega, by omega⟩
    simpa only [decodeRow, live, Option.bind_eq_bind] using RowValidationTrace.liveAnd live _ cc cs childTrace
  have unsupported : 5 ≤ row.tag := by omega
  refine ⟨1, 0, ?_, by omega, by omega⟩
  have noDecode : decodeRow n owner row = none := by
    unfold decodeRow
    split <;> simp_all
  rw [noDecode]
  exact RowValidationTrace.unsupported unsupported

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands

def sourceItemsFrom (n owner : Nat) (rows : List Row) : List (Option (Sigma fun rank : Nat => Gate n rank)) :=
  (rows.zipIdx owner).map fun item => (decodeRow n item.2 item.1).map (Sigma.mk item.2)

/-- Array preparation invokes actual row decoding in source order and records
one result-cell push for each row. Each nested validator contributes its work. -/
inductive SourceValidationTrace (n : Nat) : Nat → List Row →
    List (Option (Sigma fun rank : Nat => Gate n rank)) → Nat → Nat → Prop
  | nil (owner : Nat) : SourceValidationTrace n owner [] [] 0 0
  | cons (owner : Nat) (row : Row) (rest : List Row) (result : Option (Gate n owner))
      (rows : List (Option (Sigma fun rank : Nat => Gate n rank)))
      (checks cells laterChecks laterCells : Nat)
      (decoded : RowValidationTrace n owner row result checks cells)
      (next : SourceValidationTrace n (owner + 1) rest rows laterChecks laterCells) :
      SourceValidationTrace n owner (row :: rest) (result.map (Sigma.mk owner) :: rows)
        (checks + 1 + laterChecks) (cells + 1 + laterCells)

/-- Actual row-validation work is linear in source rows and original ordered
child/guard incidences, before the final push trace forms the indexed array. -/
theorem sourceItems_validation (n owner : Nat) (rows : List Row) :
    ∃ checks cells, SourceValidationTrace n owner rows (sourceItemsFrom n owner rows) checks cells ∧
      checks ≤ 4 * rows.length + (rowChildren rows).length + (rowGuards rows).length ∧
      cells ≤ 2 * rows.length + (rowChildren rows).length + (rowGuards rows).length := by
  induction rows generalizing owner with
  | nil => exact ⟨0, 0, SourceValidationTrace.nil owner, by simp [rowChildren, rowGuards], by simp [rowChildren, rowGuards]⟩
  | cons row rest ih =>
    obtain ⟨checks, cells, decoded, checksBound, cellsBound⟩ := decodeRow_validation n owner row
    obtain ⟨laterChecks, laterCells, next, laterChecksBound, laterCellsBound⟩ := ih (owner + 1)
    refine ⟨checks + 1 + laterChecks, cells + 1 + laterCells, ?_, ?_, ?_⟩
    · simpa only [sourceItemsFrom, List.zipIdx_cons, List.map_cons] using
        SourceValidationTrace.cons owner row rest (decodeRow n owner row)
          (sourceItemsFrom n (owner + 1) rest) checks cells laterChecks laterCells decoded next
    all_goals simp only [List.length_cons, rowChildren, rowGuards, List.flatMap_cons,
      List.length_append] at *
    all_goals omega

/-- The source array's actual validation scans and cell pushes have an original
node/incidence bound. This includes validation rather than just array size. -/
theorem source_validation_bound (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows) :
    ∃ checks cells, SourceValidationTrace n 0 rows (sourceItems n rows) checks cells ∧
      checks ≤ 4 * graph.nodeCount + graph.childIncidences + graph.guardIncidences ∧
      cells ≤ 2 * graph.nodeCount + graph.childIncidences + graph.guardIncidences := by
  obtain ⟨checks, cells, trace, work, storage⟩ := sourceItems_validation n 0 rows
  have lengths := matched_incidence_lengths graph rows matched
  exact ⟨checks, cells, trace, by simpa only [matched.length_eq, lengths.1, lengths.2] using work,
    by simpa only [matched.length_eq, lengths.1, lengths.2] using storage⟩

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorTraversal
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Word-equivalent retained storage retains every parent record, leaf record and
navigation cons cell. The two generic weight values have separate bit costs. -/
def liveCells (state : State n W) : Nat :=
  state.counters.size + 4 * state.descriptors.entries.length +
    5 * state.descriptors.leaves.length + 2 * state.descriptors.parents.length + 9

/-- A real indexed transition allocates at most one descriptor plus parent
cons, or one leaf cons. Incumbent replacement does not copy a saved route. -/
theorem emit_liveCells (weights : Channel n → W) (total : W) (root b : Nat)
    (target : Channel n) (state : State n W) (operation : CursorOp n) :
    liveCells (emit weights total root b target state operation) ≤ liveCells state + 6 := by
  cases operation <;> simp only [emit, liveCells, ForestCursorDescriptors.step,
    Array.size_setIfInBounds, List.length_cons, List.length_tail]
  all_goals try split_ifs
  all_goals try simp only [liveCells, List.length_cons, List.length_tail]
  all_goals omega

/-- Starting a new declared occurrence shares retained records and clears only
the navigation list; it does not reinitialize the n-element counter array. -/
def startRoot (state : State n W) : State n W :=
  { state with descriptors := beginRoot state.descriptors }

theorem startRoot_liveCells (state : State n W) : liveCells (startRoot state) ≤ liveCells state := by
  simp only [liveCells, startRoot, beginRoot, List.length_nil]
  omega

/-- The once-only counter initialization has a real n-push construction trace. -/
theorem initial_counter_trace (n : Nat) :
    Controller.Cost.CompilerArrayTrace.Trace (List.replicate n (0 : Nat)) #[] (Array.replicate n 0) n := by
  simpa only [List.toArray_replicate, List.length_replicate] using
    Controller.Cost.CompilerArrayTrace.empty_array (List.replicate n (0 : Nat))

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Checkpoints are the actual persistent states of indexed traversal.
The peak includes the state before and after each operation and root entry. -/
inductive StoreTrace (weights : Channel n → W) (total : W) (b : Nat) (target : Channel n) :
    State n W → State n W → Nat → Prop
  | refl (state : State n W) : StoreTrace weights total b target state state (liveCells state)
  | operation (state : State n W) (root : Nat) (operation : CursorOp n) :
      StoreTrace weights total b target state (emit weights total root b target state operation)
        (max (liveCells state) (liveCells (emit weights total root b target state operation)))
  | root (state : State n W) : StoreTrace weights total b target state (startRoot state) (liveCells state)
  | append {first middle last : State n W} {left right : Nat}
      (earlier : StoreTrace weights total b target first middle left)
      (later : StoreTrace weights total b target middle last right) :
      StoreTrace weights total b target first last (max left right)

private theorem emit_operations (state : State n W) (operation : CursorOp n) :
    (emit weights total root b target state operation).operations = state.operations + 1 := by
  cases operation <;> simp only [emit]
  all_goals split_ifs <;> rfl

/-- Every retained checkpoint is charged to actual indexed operations. Root
entry only clears navigation, so it consumes no new counter initialization. -/
theorem StoreTrace.bound {weights : Channel n → W} {total : W} {b : Nat}
    {target : Channel n} {first last : State n W} {peak : Nat}
    (trace : StoreTrace weights total b target first last peak) :
    first.operations ≤ last.operations ∧
      liveCells last ≤ peak ∧
      peak ≤ liveCells first + 6 * (last.operations - first.operations) := by
  induction trace with
  | refl state => simp
  | operation state root operation =>
    have size := emit_liveCells weights total root b target state operation
    rw [emit_operations]
    refine ⟨by omega, le_max_right _ _, ?_⟩
    apply max_le <;> omega
  | root state =>
    exact ⟨Nat.le_refl _, startRoot_liveCells state, by simp [startRoot]⟩
  | append earlier later ihLeft ihRight =>
    obtain ⟨opsLeft, liveLeft, peakLeft⟩ := ihLeft
    obtain ⟨opsRight, liveRight, peakRight⟩ := ihRight
    refine ⟨Nat.le_trans opsLeft opsRight, le_trans liveRight (le_max_right _ _), ?_⟩
    apply max_le <;> omega

private theorem traced_fold (items : List A) (step : State n W → A → State n W)
    (each : ∀ state item, ∃ peak, StoreTrace weights total b target state (step state item) peak)
    (state : State n W) :
    ∃ peak, StoreTrace weights total b target state (items.foldl step state) peak := by
  induction items generalizing state with
  | nil => exact ⟨liveCells state, StoreTrace.refl state⟩
  | cons item rest ih =>
    obtain ⟨firstPeak, first⟩ := each state item
    obtain ⟨restPeak, remaining⟩ := ih (step state item)
    exact ⟨max firstPeak restPeak, first.append remaining⟩

/-- This trace is derived from runNode itself, including both guard passes
and the actual decreasing child recursion. It is not a caller-supplied path. -/
theorem runNode_store_trace (table : Source n) (weights : Channel n → W)
    (total : W) (root b : Nat) (target : Channel n) (owner : Nat) (state : State n W) :
    ∃ peak, StoreTrace weights total b target state
      (runNode table weights total root b target owner state) peak := by
  induction owner using Nat.strong_induction_on generalizing state with
  | h owner ih =>
    let entered := emit weights total root b target state (.node owner)
    have enterTrace := StoreTrace.operation (weights := weights) (total := total)
      (b := b) (target := target) state root (.node owner)
    have after : ∃ peak, StoreTrace weights total b target entered
        (runNode table weights total root b target owner state) peak := by
      rw [runNode.eq_def]
      change ∃ peak, StoreTrace weights total b target entered
        (match readNode table owner with
        | .zero => entered
        | .liveAnd _ _ => entered
        | .input head => emit weights total root b target entered (.leaf owner [] head)
        | .disj children => children.zipIdx.foldl (fun current item =>
          let down := emit weights total root b target current (.down owner item.2 item.1.val)
          let visited := runNode table weights total root b target item.1.val down
          emit weights total root b target visited .up) entered
        | .guard child labels =>
          let indexed := labels.zipIdx
          let guarded := indexed.foldl (fun current item => emit weights total root b target current (.enter owner item.2 item.1)) entered
          let down := emit weights total root b target guarded (.down owner 0 child.val)
          let visited := runNode table weights total root b target child.val down
          let up := emit weights total root b target visited .up
          indexed.reverse.foldl (fun current item => emit weights total root b target current (.leave owner item.2 item.1)) up) peak
      cases readNode table owner with
      | zero => exact ⟨_, StoreTrace.refl entered⟩
      | liveAnd first second => exact ⟨_, StoreTrace.refl entered⟩
      | input head => exact ⟨_, StoreTrace.operation entered root (.leaf owner [] head)⟩
      | disj children =>
        apply traced_fold
        intro current item
        let down := emit weights total root b target current (.down owner item.2 item.1.val)
        let visited := runNode table weights total root b target item.1.val down
        obtain ⟨childPeak, childTrace⟩ := ih item.1.val item.1.isLt down
        exact ⟨_, (StoreTrace.operation current root (.down owner item.2 item.1.val)).append
          (childTrace.append (StoreTrace.operation visited root .up))⟩
      | guard child labels =>
        let indexed := labels.zipIdx
        let guarded := indexed.foldl (fun current item => emit weights total root b target current (.enter owner item.2 item.1)) entered
        let down := emit weights total root b target guarded (.down owner 0 child.val)
        let visited := runNode table weights total root b target child.val down
        let up := emit weights total root b target visited .up
        obtain ⟨guardPeak, guardTrace⟩ := traced_fold indexed
          (fun current item => emit weights total root b target current (.enter owner item.2 item.1))
          (fun current item => ⟨_, StoreTrace.operation current root (.enter owner item.2 item.1)⟩) entered
        obtain ⟨childPeak, childTrace⟩ := ih child.val child.isLt down
        obtain ⟨leavePeak, leaveTrace⟩ := traced_fold indexed.reverse
          (fun current item => emit weights total root b target current (.leave owner item.2 item.1))
          (fun current item => ⟨_, StoreTrace.operation current root (.leave owner item.2 item.1)⟩) up
        exact ⟨_, guardTrace.append ((StoreTrace.operation guarded root (.down owner 0 child.val)).append
          (childTrace.append ((StoreTrace.operation visited root .up).append leaveTrace)))⟩
    obtain ⟨afterPeak, afterTrace⟩ := after
    exact ⟨_, enterTrace.append afterTrace⟩

theorem runRoots_store_trace (table : Source n) (weights : Channel n → W)
    (total : W) (b : Nat) (target : Channel n) (roots : List Nat) (state : State n W) :
    ∃ peak, StoreTrace weights total b target state
      (runRoots table weights total b target roots state) peak := by
  unfold runRoots
  apply traced_fold
  intro current item
  obtain ⟨peak, trace⟩ := runNode_store_trace table weights total item.2 b target item.1 (startRoot current)
  exact ⟨_, (StoreTrace.root current).append trace⟩

/-- The maximum retained array/descriptor/leaf/navigation store is linear in
original forest incidence. Generic weight bit lengths remain separate. -/
theorem runAll_store_bound (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List ForestIndexedOperands.Row) (matched : ForestIndexedOperands.RowsMatch graph rows)
    (roots : List Nat) (rootsMatch : ForestIndexedOperands.RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    ∃ peak, StoreTrace weights (runAll (source n rows) weights b target roots).1 b target
      ⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩
      (runAll (source n rows) weights b target roots).2 peak ∧
      peak ≤ n + 24 * (graph.roots.length + graph.childIncidences) + 12 * graph.guardIncidences + 9 := by
  obtain ⟨peak, trace⟩ := runRoots_store_trace (source n rows) weights
    ((List.finRange n).foldl (fun value channel => value + weights channel) 0) b target roots
    ⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩
  have bounds := trace.bound.2.2
  have operations := runAll_operations_bound graph forest rows roots matched rootsMatch weights b target
  refine ⟨peak, trace, ?_⟩
  have initialLive : liveCells (⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩ : State n W) = n + 9 := by
    simp only [liveCells, Array.size_replicate, ForestCursorDescriptors.initial, List.length_nil]
  change peak ≤ liveCells (⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩ : State n W) +
    6 * ((runAll (source n rows) weights b target roots).2.operations - 0) at bounds
  rw [initialLive, Nat.sub_zero] at bounds
  omega

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG

/-- Each live recursive frame retains its original child/guard zip lists.
The constant accounts for the recursive call frame. Child zip pairs and
reversed guard cons cells are charged even while their ancestor remains live. -/
def controlFrame (gate : Gate n owner) : Nat :=
  12 + 4 * gate.children.length + 6 * gate.guardLabels.length

def controlBudget (table : Source n) : Nat → Nat
  | 0 => 0
  | owner + 1 => controlBudget table owner + controlFrame (readNode table owner)

private theorem controlBudget_mono (table : Source n) {first last : Nat} (ordered : first ≤ last) :
    controlBudget table first ≤ controlBudget table last := by
  induction ordered with
  | refl => exact Nat.le_refl _
  | step ordered ih =>
    exact le_trans ih (Nat.le_add_right _ _)

/-- This mirrors the real call structure: siblings are visited sequentially,
whereas an ancestor's iterator remains live until its child returns. -/
def controlPeak (table : Source n) (owner : Nat) : Nat :=
  let gate := readNode table owner
  controlFrame gate + match gate with
    | .zero => 0
    | .input _ => 0
    | .liveAnd _ _ => 0
    | .disj children => children.foldl (fun peak child => max peak (controlPeak table child.val)) 0
    | .guard child _ => controlPeak table child.val
termination_by owner
decreasing_by all_goals exact Fin.isLt _

private theorem maxFold_bound (items : List A) (value : A → Nat)
    (bounded : ∀ item ∈ items, value item ≤ budget) (initial : Nat) (initialBound : initial ≤ budget) :
    items.foldl (fun peak item => max peak (value item)) initial ≤ budget := by
  induction items generalizing initial with
  | nil => exact initialBound
  | cons item rest ih =>
    exact ih (fun other member => bounded other (List.mem_cons_of_mem _ member))
      (max _ _) (max_le initialBound (bounded item (List.mem_cons_self)))

/-- Strictly decreasing original row ranks charge simultaneous ancestor
iterators to distinct rows, not to nodeCount times total incidence. -/
theorem controlPeak_bound (table : Source n) (owner : Nat) :
    controlPeak table owner ≤ controlBudget table (owner + 1) := by
  induction owner using Nat.strong_induction_on with
  | h owner ih =>
    rw [controlPeak.eq_def]
    change controlFrame (readNode table owner) + _ ≤
      controlBudget table owner + controlFrame (readNode table owner)
    have childBound : ∀ child : Fin owner, controlPeak table child.val ≤ controlBudget table owner := by
      intro child
      exact le_trans (ih child.val child.isLt)
        (controlBudget_mono table (Nat.succ_le_of_lt child.isLt))
    cases readNode table owner with
    | zero => simp only [Nat.add_zero]; omega
    | input head => simp only [Nat.add_zero]; omega
    | liveAnd first second => simp only [Nat.add_zero]; omega
    | disj children =>
      have bound := maxFold_bound children (fun child => controlPeak table child.val)
        (fun child _ => childBound child) 0 (Nat.zero_le _)
      change controlFrame (.disj children) + children.foldl (fun peak child => max peak (controlPeak table child.val)) 0 ≤ _
      omega
    | guard child labels =>
      have bound := childBound child
      change controlFrame (.guard child labels) + controlPeak table child.val ≤ _
      omega

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG

private theorem controlBudget_eq_sum (table : Source n) (count : Nat) :
    controlBudget table count = ((List.range count).map fun owner => controlFrame (readNode table owner)).sum := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [controlBudget, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton, ih]

private theorem frame_sum (items : List A) (children labels : A → Nat) :
    (items.map (fun item => 12 + 4 * children item + 6 * labels item)).sum =
      12 * items.length + 4 * (items.map children).sum + 6 * (items.map labels).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

/-- Topological ranking ensures that simultaneously retained iterator lists
use distinct original rows; their complete bound is the stored incidence sum. -/
theorem controlBudget_source (graph : DAG n) (rows : List ForestIndexedOperands.Row)
    (matched : ForestIndexedOperands.RowsMatch graph rows) :
    controlBudget (source n rows) graph.nodeCount =
      12 * graph.nodeCount + 4 * graph.childIncidences + 6 * graph.guardIncidences := by
  rw [controlBudget_eq_sum]
  have ranged := List.ofFn_getElem_eq_map (List.range graph.nodeCount)
    (fun owner => controlFrame (readNode (source n rows) owner))
  have sums : ((List.range graph.nodeCount).map
      (fun owner => controlFrame (readNode (source n rows) owner))).sum =
      (List.ofFn (fun index : Fin graph.nodeCount => controlFrame (graph.node index))).sum := by
    apply congrArg List.sum
    calc
      _ = List.ofFn (fun index : Fin graph.nodeCount => controlFrame (readNode (source n rows) index.val)) := by
        apply List.ext_getElem
        · simp only [List.length_map, List.length_range, List.length_ofFn]
        · intro index left right
          simp only [List.getElem_map, List.getElem_ofFn]
          have rangedIndex : index < (List.range graph.nodeCount).length := by
            simpa only [List.length_map] using left
          exact congrArg (fun owner => controlFrame (readNode (source n rows) owner))
            (List.getElem_range rangedIndex)
      _ = _ := by congr 1; funext index; rw [readNode_matches graph rows matched index]
  rw [sums]
  change (List.ofFn (fun index : Fin graph.nodeCount =>
    12 + 4 * (graph.node index).children.length + 6 * (graph.node index).guardLabels.length)).sum = _
  simpa only [List.ofFn_eq_map, List.length_finRange, DAG.childIncidences,
    DAG.guardIncidences] using frame_sum (List.finRange graph.nodeCount)
      (fun index => (graph.node index).children.length)
      (fun index => (graph.node index).guardLabels.length)

theorem controlPeak_source (graph : DAG n) (rows : List ForestIndexedOperands.Row)
    (matched : ForestIndexedOperands.RowsMatch graph rows) (owner : Fin graph.nodeCount) :
    controlPeak (source n rows) owner.val ≤
      12 * graph.nodeCount + 4 * graph.childIncidences + 6 * graph.guardIncidences := by
  have first := controlPeak_bound (source n rows) owner.val
  have budget := controlBudget_mono (source n rows) (Nat.succ_le_of_lt owner.isLt)
  rw [controlBudget_source graph rows matched] at budget
  exact le_trans first budget

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands

/-- The decoded source stores one array slot and rank/gate metadata per row,
plus two words per child/guard cons. Proof fields of finite IDs are erased. -/
def decodedWords (item : Option (Sigma fun owner : Nat => Gate n owner)) : Nat :=
  match item with
  | none => 0
  | some ⟨_, gate⟩ => 6 + 2 * gate.children.length + 2 * gate.guardLabels.length

def sourceWords (n : Nat) (rows : List Row) : Nat :=
  ((sourceItems n rows).map fun item => 1 + decodedWords item).sum

private theorem rowWords_sum (rows : List Row) :
    (rows.map (fun row => 7 + 2 * row.children.length + 2 * row.guards.length)).sum =
      7 * rows.length + 2 * (rowChildren rows).length + 2 * (rowGuards rows).length := by
  induction rows with
  | nil => simp [rowChildren, rowGuards]
  | cons row rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, rowChildren, rowGuards,
      List.flatMap_cons, List.length_append] at *
    omega

/-- Stored source footprint follows from the actual decoder, not a caller's
pre-decoded semantic array. Repeated incidences remain individual cons cells. -/
theorem sourceWords_exact (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows) :
    sourceWords n rows = 7 * graph.nodeCount + 2 * graph.childIncidences + 2 * graph.guardIncidences := by
  have decoded : (sourceItems n rows).map (fun item => 1 + decodedWords item) =
      rows.map (fun row => 7 + 2 * row.children.length + 2 * row.guards.length) := by
    apply List.ext_getElem
    · simp only [List.length_map, sourceItems, List.length_zipIdx]
    · intro index left right
      have valid : index < graph.nodeCount := by simpa only [List.length_map, matched.length_eq] using right
      let owner : Fin graph.nodeCount := ⟨index, valid⟩
      have row := matched.node owner
      have actual : decodeRow n index (rows[index]'(by simpa only [List.length_map] using right)) =
          some (graph.node owner) := decodeRow_matches _ (graph.node owner) row
      have zipBound : index < rows.zipIdx.length := by simpa only [List.length_zipIdx, List.length_map] using right
      have zipped : rows.zipIdx[index]'zipBound = (rows[index]'(by simpa only [List.length_map] using right), index) := by
        simpa only [Nat.zero_add] using (List.getElem_zipIdx (l := rows) (j := 0) zipBound)
      simp only [sourceItems, List.getElem_map]
      rw [zipped]
      simp only [actual, Option.map_some, decodedWords]
      have children : (rows[index]'(by simpa only [List.length_map] using right)).children.length =
          (graph.node owner).children.length := by
        simpa only [owner, List.length_map] using congrArg List.length row.2.2.1
      have guards : (rows[index]'(by simpa only [List.length_map] using right)).guards.length =
          (graph.node owner).guardLabels.length := by
        simpa only [owner, List.length_map] using congrArg List.length row.2.2.2
      rw [← children, ← guards]
      omega
  unfold sourceWords
  rw [decoded, rowWords_sum]
  have lengths := matched_incidence_lengths graph rows matched
  rw [matched.length_eq, lengths.1, lengths.2]

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Decoder Controller.Decoder.DAG
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Retained weighted state, decoded rows, active recursive iterators, and the
original typed source occupy a linear number of scalar/reference words.
Weight values are charged by their own bit lengths. Root-index pairs retain
all declared occurrences; no candidate contains a copied path. -/
theorem indexed_store_total_bound (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootsMatch : ForestIndexedOperands.RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    ∃ peak, StoreTrace weights (runAll (source n rows) weights b target roots).1 b target
      ⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩
      (runAll (source n rows) weights b target roots).2 peak ∧
      peak + sourceWords n rows + controlBudget (source n rows) graph.nodeCount +
        (6 * graph.nodeCount + 2 * graph.childIncidences + 2 * graph.guardIncidences +
          2 * graph.roots.length + 5) + 6 * graph.roots.length + 7 ≤
        n + 25 * graph.nodeCount + 32 * graph.roots.length +
          32 * graph.childIncidences + 22 * graph.guardIncidences + 21 := by
  obtain ⟨peak, trace, bound⟩ := runAll_store_bound graph forest rows matched roots rootsMatch weights b target
  refine ⟨peak, trace, ?_⟩
  rw [sourceWords_exact graph rows matched, controlBudget_source graph rows matched]
  omega

end Controller.Cost.ForestWeightedIndexed

namespace Controller.Cost.ForestWeightedIndexed
open Controller.Cost Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestMarkerMachine Controller.Cost.ForestCursorReconstruct
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorAllRootsExecution
open Controller.Cost.ForestCursorProgram Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorMaterialize
open Controller.Cost.ForestWitnessMarshal Controller.Cost.ForestWitnessWalk
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedGlobal Controller.Cost.ForestWeightedPhysicalOptimal
open Controller.Cost.ForestCursorExecution
open Controller.Decoder Controller.Decoder.DAG
variable {width n : Nat}
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- A complete successful trace uses only fetched slots present in its source
program. Extending the resident code preserves that same trace exactly. -/
theorem execution_same_fetched_prefix {registers : Nat}
    (sourceProgram targetProgram : Program width registers)
    (before after : Controller.Cost.State width registers) (ticks peak : Nat)
    (trace : Execution sourceProgram before after ticks peak)
    (agree : ∀ slot, slot < sourceProgram.size → targetProgram[slot]? = sourceProgram[slot]?) :
    Execution targetProgram before after ticks peak := by
  induction trace with
  | refl state => exact Execution.refl state
  | @cons first middle last ticks peak transition rest ih =>
    have lifted : programStep targetProgram first = some middle := by
      unfold programStep at transition ⊢
      cases found : sourceProgram[first.pc.val]? with
      | none =>
        rw [found] at transition
        change none = some middle at transition
        cases transition
      | some instruction =>
        have valid := (Array.getElem?_eq_some_iff.mp found).1
        rw [agree first.pc.val valid]
        exact transition
    exact Execution.cons lifted ih

theorem abstract_walk_endpoint_execution (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List ℕ) (head : Channel n) (blocked : Finset (Channel n))
    (path : RoutePath graph node route head blocked) (feasible : head ∉ blocked)
    (program : Program width 4) (state : Controller.Cost.State width 4) (layout : ForestWitnessPath.Layout)
    (source : WalkSource width state.heap graph layout) (markers : MarkerCells source ∅)
    (stack : List (Word width)) (base countAddress : ℕ)
    (countBefore : countAddress < layout.markerBase)
    (countWord : state.heap[countAddress]'(by have := source.region; omega) = word width n)
    (held : state.reg 0 = word width node.val)
    (positions : state.stack = route.map (word width) ++ stack)
    (pc : state.pc = word width base) (running : state.halted = false)
    (programFits : base + 67 < 2 ^ width) (heapFits : state.heap.size ≤ 2 ^ width)
    (block : BlockAt program base (ForestWitnessWalk.code width base layout countAddress)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ ForestWitnessAccept.sourceBudget graph graph.nodeCount + 10 * n + 4 ∧
      peak ≤ state.liveWords + n + 1 ∧ final.stack = stack ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ state.output ∧
      graph.eval (assignmentOfSet (fullUnblocked blocked)) node = true ∧
      final.pc = word width (base + 67) ∧ final.halted = false ∧
      final.heap.size = state.heap.size := by
  obtain ⟨walkTicks, cost⟩ := route_cost path
  obtain ⟨final, peak, execution, peakBound, finalSize, finalStack, finalOutput, finalPC, finalRunning, _, truth⟩ :=
    walk_and_emit cost feasible program state layout source markers stack base countAddress
      countBefore countWord held positions pc running programFits heapFits block
  have bound := (ForestWitnessAccept.routeCost_le_source graph cost).trans
    (ForestWitnessAccept.sourceBudget_mono graph (Nat.succ_le_of_lt node.isLt))
  refine ⟨final, walkTicks + 10 * n + 4, peak, execution, by omega,
    peakBound, finalStack, ?_, truth, finalPC, finalRunning, finalSize⟩
  simpa only [fullUnblocked, Finset.mem_sdiff, Finset.mem_univ, true_and, decide_not] using finalOutput

theorem selected_walk_endpoint_execution (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (position : Fin graph.roots.length) (head : Channel n) (blocked : Finset (Channel n))
    (path : RoutePath graph (graph.roots.get position)
      ((setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).route candidate.pointer).reverse head blocked)
    (feasible : pathFeasible b target head blocked) (temporary : Word width)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    let packet := cacheHeap width heap rows roots
    let routes := selectedRoutes width packet graph (cacheRecords heap graph rows roots matched)
      countFits positionFits candidate.root candidate.pointer
    let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
    let ready := ((counterState (selectedHeap width packet graph candidate.root candidate.pointer)
      (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary).frame
        ((routes.route candidate.pointer).reverse.map (word width) ++ stack) output)
    ∃ final ticks peak,
      Execution program ready final ticks peak ∧
      ticks ≤ ForestWitnessAccept.sourceBudget graph graph.nodeCount + 10 * n + 4 ∧
      peak ≤ 5 + (setupHeap width packet graph).size +
        ((routes.route candidate.pointer).length + stack.length + output.length) + n + 1 ∧
      final.stack = stack ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
      graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
      final.pc = word width (base + 92) ∧ final.halted = false ∧
      final.heap.size = (setupHeap width packet graph).size := by
  let packet := cacheHeap width heap rows roots
  let initialHeap := setupHeap width packet graph
  let layout := ForestWitnessPath.packetLayout heap.size rows.length (setupOffset packet graph)
  let records := cacheRecords heap graph rows roots matched
  let routes := selectedRoutes width packet graph records countFits positionFits candidate.root candidate.pointer
  let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
  have walkBlock : BlockAt program (base + 25)
      (ForestWitnessWalk.code width (base + 25) layout countAddress) := by
    simpa only [preludeCode_length] using BlockAt.suffix program base _ _ block
  let ready := ready_state (selectedHeap width packet graph candidate.root candidate.pointer)
    (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary
    (routes.route candidate.pointer).reverse stack output
  obtain ⟨source, markers, countBefore, storedCount⟩ := selected_ready_source heap graph rows roots
    matched candidate.root candidate.pointer countAddress countValid countWord heapFits
  have readyHeap : ready.heap = selectedHeap width packet graph candidate.root candidate.pointer :=
    ready_state_heap _ _ _ _ _ _ _ _
  obtain ⟨readySource, readyMarkers, readyCount⟩ :=
    source_on_state ready _ graph layout readyHeap source markers countAddress countBefore storedCount
  obtain ⟨held, positions, readyPC, readyRunning, readyOutput⟩ :=
    ready_state_fields (selectedHeap width packet graph candidate.root candidate.pointer)
      (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary
      (routes.route candidate.pointer).reverse stack output
  have routePath : RoutePath graph (graph.roots.get position)
      (routes.route candidate.pointer).reverse head blocked := path
  have readyFits : ready.heap.size ≤ 2 ^ width := by
    rw [readyHeap]
    exact (marshaled_size initialHeap (provenanceCell packet graph) (setupLayout packet graph).best
      (word width candidate.root) (word width candidate.pointer)).le.trans heapFits
  obtain ⟨final, walkTicks, walkPeak, afterWalk, costBound, peakBound, finalStack, finalOutput, truth, finalPC, finalRunning, finalSize⟩ :=
    abstract_walk_endpoint_execution graph (graph.roots.get position) (routes.route candidate.pointer).reverse
      head blocked routePath feasible.1 program ready layout readySource readyMarkers stack (base + 25)
      countAddress countBefore readyCount held positions readyPC readyRunning (by omega) readyFits walkBlock
  have actualWalk : Execution program
      ((counterState (selectedHeap width packet graph candidate.root candidate.pointer)
        (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary).frame
        ((routes.route candidate.pointer).reverse.map (word width) ++ stack) output)
      final walkTicks walkPeak := by
    simpa only [ready, ready_state_eq] using afterWalk
  refine ⟨final, walkTicks, walkPeak, actualWalk, costBound, ?_, finalStack, ?_, truth, ?_, finalRunning, ?_⟩
  · have words : ready.liveWords = 5 + initialHeap.size +
        ((routes.route candidate.pointer).length + stack.length + output.length) := by
      rw [show ready = _ from ready_state_eq _ _ _ _ _ _ _ _]
      exact (ready_liveWords (selectedHeap width packet graph candidate.root candidate.pointer)
        (base + 25) (word width (graph.roots.get position).val) (word width rootBase) temporary
        (routes.route candidate.pointer) stack output).trans
        (congrArg (fun size => 5 + size +
          ((routes.route candidate.pointer).length + stack.length + output.length))
          (marshaled_size initialHeap (provenanceCell packet graph) (setupLayout packet graph).best
            (word width candidate.root) (word width candidate.pointer)))
    simpa only [words] using peakBound
  · have outputEq : ready.output = output := readyOutput
    exact finalOutput.trans (congrArg (fun suffix =>
      List.ofFn (fun channel : Channel n =>
        boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ suffix) outputEq)
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC
  · rw [finalSize, readyHeap]
    simp only [selectedHeap, marshaled_size]
    rfl

theorem selected_emission_endpoint (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (runGlobal graph weights b target).2.1.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (setupHeap width (cacheHeap width heap rows roots) graph) base address
            (word width candidate.root) (word width candidate.pointer)).frame stack output)
          final ticks peak ∧
        ticks ≤ 14 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          10 * n + 16 ∧
        peak ≤ 5 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
        final.pc = word width (base + 92) ∧ final.halted = false ∧
        final.heap.size = (setupHeap width (cacheHeap width heap rows roots) graph).size := by
  let packet := cacheHeap width heap rows roots
  let initialHeap := setupHeap width packet graph
  let layout := ForestWitnessPath.packetLayout heap.size rows.length (setupOffset packet graph)
  let records := cacheRecords heap graph rows roots matched
  let routes := selectedRoutes width packet graph records countFits positionFits candidate.root candidate.pointer
  let rootBase := heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length
  obtain ⟨position, rootEq, head, blocked, path, feasible, score, optimal⟩ :=
    global_physical_optimal width packet graph guarded weights nonnegative b target countFits
      positionFits candidate selected
  have allocated := ForestWeightedReconstruction.selected_pointer_bound graph weights b target candidate selected
  obtain ⟨temporary, beforeWalk⟩ := selected_prelude_execution program heap graph guarded rows roots
    matched rootMatches weights nonnegative b target candidate selected countFits positionFits
    position rootEq allocated base countAddress address stack output countValid countWord heapFits programFits block
  have pointerBound : candidate.pointer ≤ routes.count := allocated
  obtain ⟨final, walkTicks, walkPeak, afterWalk, costBound, peakBound, finalStack, finalOutput, truth, finalPC, finalRunning, finalSize⟩ :=
    selected_walk_endpoint_execution program heap graph guarded rows roots matched rootMatches weights nonnegative
      b target candidate selected countFits positionFits position head blocked path feasible temporary
      base countAddress address stack output countValid countWord heapFits programFits block
  have routeBound := reconstruction_bounds routes candidate.pointer pointerBound
  have joined := beforeWalk.append afterWalk
  refine ⟨position, rootEq, blocked, final, _, _,
    fullUnblocked_admissible b target head blocked feasible, truth, score, optimal, joined,
    ?_, ?_, finalStack, finalOutput, finalPC, finalRunning, finalSize⟩
  · change 14 * (routes.route candidate.pointer).length + 12 + walkTicks ≤
      14 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount + 10 * n + 16
    have lengthBound : (routes.route candidate.pointer).length ≤ (buildRoots graph).count := routeBound.2
    omega
  · change max (5 + initialHeap.size +
        ((routes.route candidate.pointer).length + stack.length + output.length)) walkPeak ≤
      5 + initialHeap.size + (buildRoots graph).count + stack.length + output.length + n + 1
    change walkPeak ≤ 5 + initialHeap.size +
      ((routes.route candidate.pointer).length + stack.length + output.length) + n + 1 at peakBound
    have lengthBound : (routes.route candidate.pointer).length ≤ (buildRoots graph).count := routeBound.2
    apply max_le <;> omega

theorem direct_selected_emission_endpoint (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (forest : graph.FormulaForest) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (Controller.Cost.ForestWeightedDirect.runAll graph weights b target).2.data.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    (Controller.Cost.ForestWeightedDirect.runAll graph weights b target).2.arithmetic ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences ∧
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (setupHeap width (cacheHeap width heap rows roots) graph) base address
            (word width candidate.root) (word width candidate.pointer)).frame stack output)
          final ticks peak ∧
        ticks ≤ 14 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          10 * n + 16 ∧
        peak ≤ 5 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
        final.pc = word width (base + 92) ∧ final.halted = false ∧
        final.heap.size = (setupHeap width (cacheHeap width heap rows roots) graph).size := by
  have projected := (Controller.Cost.ForestWeightedDirect.runAll_projection graph weights b target).1
  have selectedGlobal : (runGlobal graph weights b target).2.1.selected = some candidate := by
    rw [← projected]
    exact selected
  exact ⟨Controller.Cost.ForestWeightedDirect.runAll_arithmetic_bound graph forest weights b target,
    selected_emission_endpoint program heap graph guarded rows roots matched rootMatches weights nonnegative
      b target candidate selectedGlobal countFits positionFits base countAddress address stack output
      countValid countWord heapFits programFits block⟩

theorem indexed_selected_emission_endpoint (program : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (forest : graph.FormulaForest) (guarded : graph.Guarded) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : Candidate W)
    (selected : (runAll (source n rows) weights b target roots).2.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (base countAddress : ℕ) (address : Word width) (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : base + 92 < 2 ^ width)
    (block : BlockAt program base
      (preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
        (setupLayout (cacheHeap width heap rows roots) graph).best
        (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
        (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
       ForestWitnessWalk.code width (base + 25)
        (ForestWitnessPath.packetLayout heap.size rows.length
          (setupOffset (cacheHeap width heap rows roots) graph)) countAddress)) :
    (runAll (source n rows) weights b target roots).2.arithmetic ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences ∧
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (setupHeap width (cacheHeap width heap rows roots) graph) base address
            (word width candidate.root) (word width candidate.pointer)).frame stack output)
          final ticks peak ∧
        ticks ≤ 14 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          10 * n + 16 ∧
        peak ≤ 5 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
        final.pc = word width (base + 92) ∧ final.halted = false ∧
        final.heap.size = (setupHeap width (cacheHeap width heap rows roots) graph).size := by
  have projected := congrArg (fun state : ForestWeightedDirect.State n W => state.data.selected)
    (runAll_projection graph rows roots matched rootMatches weights b target).2
  change (runAll (source n rows) weights b target roots).2.selected =
    (ForestWeightedDirect.runAll graph weights b target).2.data.selected at projected
  have selectedDirect : (ForestWeightedDirect.runAll graph weights b target).2.data.selected = some candidate := by
    rw [← projected]
    exact selected
  obtain ⟨arithmetic, physical⟩ := direct_selected_emission_endpoint program heap graph
    forest guarded rows roots matched rootMatches weights nonnegative b target candidate selectedDirect
    countFits positionFits base countAddress address stack output countValid countWord heapFits programFits block
  exact ⟨runAll_arithmetic_bound graph rows roots matched rootMatches forest weights b target, physical⟩

theorem selected_prefixed_emission_endpoint (prior : Program width 4) (heap : Array (Word width))
    (graph : DAG n) (forest : graph.FormulaForest) (guarded : graph.Guarded)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : Nat) (target : Channel n)
    (candidate : Candidate W)
    (selected : (runAll (source n rows) weights b target roots).2.selected = some candidate)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (countAddress : Nat) (address loaded temporary : Word width)
    (stack output : List (Word width))
    (countValid : countAddress < heap.size) (countWord : heap[countAddress] = word width n)
    (heapFits : (setupHeap width (cacheHeap width heap rows roots) graph).size ≤ 2 ^ width)
    (programFits : prior.size + (4 * (buildRoots graph).count + 2 * (n + 3)) + 94 < 2 ^ width) :
    let state := (runAll (source n rows) weights b target roots).2
    let program := materialize prior (selectedItems width heap graph rows roots state candidate
      countFits positionFits prior.size countAddress)
    state.arithmetic ≤ n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences ∧
    ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
      ∃ blocked final ticks peak,
        Admissible b target (fullUnblocked blocked) ∧
        graph.eval (assignmentOfSet (fullUnblocked blocked)) (graph.roots.get position) = true ∧
        candidate.score = GenericWeight.total weights (fullUnblocked blocked) ∧
        (∀ other K, Admissible b target K →
          graph.eval (assignmentOfSet K) (graph.roots.get other) = true →
          GenericWeight.total weights K ≤ GenericWeight.total weights (fullUnblocked blocked)) ∧
        Execution program
          ((counterState (cacheHeap width heap rows roots) prior.size address loaded temporary).frame stack output)
          final ticks peak ∧
        ticks ≤ 18 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount +
          12 * n + 24 ∧
        peak ≤ 5 + (setupHeap width (cacheHeap width heap rows roots) graph).size +
          (buildRoots graph).count + stack.length + output.length + n + 1 ∧
        final.stack = stack ∧
        final.output = List.ofFn (fun channel : Channel n =>
          boolWord width (decide (channel ∈ fullUnblocked blocked))) ++ output ∧
        final.pc = word width (prior.size + 4 * (buildRoots graph).count + 2 * (n + 3) + 94) ∧
        final.halted = false ∧
        final.heap.size = (setupHeap width (cacheHeap width heap rows roots) graph).size := by
  let state := (runAll (source n rows) weights b target roots).2
  let leadingCode := descriptorCode width state ++ candidateCode width candidate
  let base := prior.size + leadingCode.length
  let suffix := preludeCode width base (provenanceCell (cacheHeap width heap rows roots) graph)
    (setupLayout (cacheHeap width heap rows roots) graph).best
    (setupRoutes width (cacheHeap width heap rows roots) graph countFits positionFits).base
    (heap.size + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) ++
    ForestWitnessWalk.code width (base + 25)
      (ForestWitnessPath.packetLayout heap.size rows.length
        (setupOffset (cacheHeap width heap rows roots) graph)) countAddress
  let program := materialize prior (leadingCode ++ suffix)
  have programEq : program = materialize prior (selectedItems width heap graph rows roots state candidate
      countFits positionFits prior.size countAddress) := by
    simp only [program, selectedItems, leadingCode, base, suffix, List.append_assoc]
  have prefixLength : leadingCode.length = 4 * (buildRoots graph).count + 2 * (n + 3) + 2 := by
    have operands := descriptorValues_refines graph rows roots matched rootMatches weights b target
    simp only [leadingCode, List.length_append, descriptorCode, state, operands,
      ForestCursorMaterialize.writeCode_length, setupValues_length, candidateCode,
      List.length_cons, List.length_nil]
    omega
  have prefixBlock : BlockAt program prior.size leadingCode := by
    simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.add_zero, program] using
      materialize_block prior [] leadingCode suffix
  have suffixBlock : BlockAt program base suffix := by
    simpa only [List.append_nil, program, base] using materialize_block prior leadingCode suffix []
  have prefixTrace := computed_prefix_execution program (cacheHeap width heap rows roots) graph rows roots
    matched rootMatches weights b target candidate prior.size address loaded temporary stack output
    (by omega) (by simpa only [setupHeap_size] using heapFits) prefixBlock
  obtain ⟨arithmetic, position, rootEq, blocked, final, ticks, peak, admissible, feasible,
      score, optimal, suffixTrace, time, space, finalStack, finalOutput, finalPC, finalRunning, finalSize⟩ :=
    indexed_selected_emission_endpoint program heap graph forest guarded rows roots matched rootMatches weights
      nonnegative b target candidate selected countFits positionFits base countAddress address stack output
      countValid countWord heapFits (by dsimp only [base]; rw [prefixLength]; omega) suffixBlock
  have boundary : base = prior.size + (4 * (buildRoots graph).count + 2 * (n + 3)) + 2 := by
    dsimp only [base]
    rw [prefixLength]
    omega
  rw [boundary] at suffixTrace
  have joined := prefixTrace.append suffixTrace
  refine ⟨arithmetic, position, rootEq, blocked, final,
    4 * (buildRoots graph).count + 2 * (n + 3) + 2 + ticks,
    max (5 + (cacheHeap width heap rows roots).size + 2 * (buildRoots graph).count + (n + 3) +
      stack.length + output.length) peak,
    admissible, feasible, score, optimal, ?_, by omega, ?_, finalStack, finalOutput, ?_, finalRunning, finalSize⟩
  · simpa only [programEq, Nat.add_assoc] using joined
  · apply max_le
    · simp only [setupHeap_size]
      omega
    · exact space
  · rw [boundary] at finalPC
    simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC

end Controller.Cost.ForestWeightedIndexed
