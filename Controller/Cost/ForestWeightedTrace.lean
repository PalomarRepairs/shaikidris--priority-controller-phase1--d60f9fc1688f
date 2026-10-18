module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorSemantics
public import Controller.Cost.ForestCursorCharging
public import Controller.Decoder.ForestGeneric
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Arithmetic trace of the ordered-weight source cursor

Guard entry and exit use the cached blocked-union weight. A feasible callback
subtracts that weight from one caller-supplied total and optionally compares the
result with the current best score. The trace records the operands of those
actual arithmetic calls. Weight-operation counts are distinct from the costs of
representing their operands as machine words or bit strings.
-/
namespace Controller.Cost.ForestWeightedTrace

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorSemantics

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

abbrev WeightedState (n : ℕ) (W : Type) :=
  (GuardCounters n × W) × Option (LeafRoute × W)

inductive Arithmetic (W : Type) where
  | add (first second : W)
  | subtract (first second : W)
  | compare (first second : W)

def weightedStep (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : WeightedState n W) : CursorOp n → WeightedState n W
  | .enter _ _ channel => (GenericWeight.enter weights state.1 channel, state.2)
  | .leave _ _ channel => (GenericWeight.leave weights state.1 channel, state.2)
  | .leaf _ route head => (state.1, keepBestGenericRoute b target total route head state.1 state.2)
  | _ => state

/-- The total is passed through every step; it is not recomputed at callbacks. -/
def traceStep (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : WeightedState n W) (operation : CursorOp n) : WeightedState n W × List (Arithmetic W) :=
  match operation with
  | .enter _ _ channel =>
      if state.1.1 channel = 0 then
        let value := state.1.2 + weights channel
        (((enterGuards state.1.1 [channel], value), state.2), [.add state.1.2 (weights channel)])
      else (((enterGuards state.1.1 [channel], state.1.2), state.2), [])
  | .leave _ _ channel =>
      if state.1.1 channel = 1 then
        let value := state.1.2 - weights channel
        (((leaveGuards state.1.1 [channel], value), state.2), [.subtract state.1.2 (weights channel)])
      else (((leaveGuards state.1.1 [channel], state.1.2), state.2), [])
  | .leaf _ route head =>
      if state.1.1 head = 0 ∧ (b ≠ 1 ∨ state.1.1 target = 0) then
        let score := total - state.1.2
        match state.2 with
        | none => ((state.1, some (route, score)), [.subtract total state.1.2])
        | some previous =>
            ((state.1, if previous.2 < score then some (route, score) else state.2),
              [.subtract total state.1.2, .compare previous.2 score])
      else (state, [])
  | _ => (state, [])

theorem traceStep_projection (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : WeightedState n W) (operation : CursorOp n) :
    (traceStep weights b target total state operation).1 = weightedStep weights b target total state operation := by
  cases operation with
  | enter owner position channel =>
      by_cases zero : state.1.1 channel = 0
      · simp [traceStep, weightedStep, GenericWeight.enter, zero]
      · simp [traceStep, weightedStep, GenericWeight.enter, zero]
  | leave owner position channel =>
      by_cases last : state.1.1 channel = 1
      · simp [traceStep, weightedStep, GenericWeight.leave, last]
      · simp [traceStep, weightedStep, GenericWeight.leave, last]
  | leaf owner route head =>
      by_cases feasible : state.1.1 head = 0 ∧ (b ≠ 1 ∨ state.1.1 target = 0)
      · cases best : state.2 <;> simp [traceStep, weightedStep, keepBestGenericRoute, feasible, best]
      · simp [traceStep, weightedStep, keepBestGenericRoute, feasible]
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl

/-- At most one weight operation occurs at a guard incidence; callbacks use
one subtraction and, only when a best score exists, one comparison. -/
theorem traceStep_length (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : WeightedState n W) (operation : CursorOp n) :
    (traceStep weights b target total state operation).2.length ≤ 2 := by
  cases operation with
  | enter owner position channel =>
      by_cases zero : state.1.1 channel = 0 <;> simp [traceStep, zero]
  | leave owner position channel =>
      by_cases last : state.1.1 channel = 1 <;> simp [traceStep, last]
  | leaf owner route head =>
      by_cases feasible : state.1.1 head = 0 ∧ (b ≠ 1 ∨ state.1.1 target = 0)
      · cases best : state.2 <;> simp [traceStep, feasible, best]
      · simp [traceStep, feasible]
  | node owner => simp [traceStep]
  | down owner position child => simp [traceStep]
  | up => simp [traceStep]

def traceFoldStep (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (saved : WeightedState n W × List (Arithmetic W)) (operation : CursorOp n) :
    WeightedState n W × List (Arithmetic W) :=
  let result := traceStep weights b target total saved.1 operation
  (result.1, result.2.reverse ++ saved.2)

def runTrace (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : WeightedState n W) (operations : List (CursorOp n)) :
    WeightedState n W × List (Arithmetic W) :=
  operations.foldl (traceFoldStep weights b target total) (state, [])

private theorem trace_fold_projection (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (saved : WeightedState n W × List (Arithmetic W)) (operations : List (CursorOp n)) :
    (operations.foldl (traceFoldStep weights b target total) saved).1 =
      operations.foldl (weightedStep weights b target total) saved.1 := by
  induction operations generalizing saved with
  | nil => rfl
  | cons operation rest ih =>
      change (rest.foldl (traceFoldStep weights b target total)
        (traceFoldStep weights b target total saved operation)).1 = _
      rw [ih]
      simp only [traceFoldStep, traceStep_projection, List.foldl_cons]

theorem runTrace_projection (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : WeightedState n W) (operations : List (CursorOp n)) :
    (runTrace weights b target total state operations).1 =
      operations.foldl (weightedStep weights b target total) state :=
  trace_fold_projection weights b target total (state, []) operations

private theorem trace_fold_length (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (saved : WeightedState n W × List (Arithmetic W)) (operations : List (CursorOp n)) :
    (operations.foldl (traceFoldStep weights b target total) saved).2.length ≤
      saved.2.length + 2 * operations.length := by
  induction operations generalizing saved with
  | nil => simp
  | cons operation rest ih =>
      have bounded := ih (traceFoldStep weights b target total saved operation)
      have localBound := traceStep_length weights b target total saved.1 operation
      simp only [List.foldl_cons, traceFoldStep, List.length_append, List.length_reverse] at bounded
      simp only [List.foldl_cons, List.length_cons, traceFoldStep,
        List.length_append, List.length_reverse]
      omega

theorem runTrace_length (weights : Channel n → W) (b : ℕ) (target : Channel n) (total : W)
    (state : WeightedState n W) (operations : List (CursorOp n)) :
    (runTrace weights b target total state operations).2.length ≤ 2 * operations.length := by
  simpa [runTrace] using trace_fold_length weights b target total (state, []) operations

def shifted (state : GuardCounters n × W) (offset : W) : GuardCounters n × W :=
  (state.1, state.2 + offset)

private theorem leave_shifted (weights : Channel n → W) (state : GuardCounters n × W)
    (offset : W) (label : Channel n) :
    GenericWeight.leave weights (shifted state offset) label =
      shifted (GenericWeight.leave weights state label) offset := by
  by_cases last : state.1 label = 1
  · apply Prod.ext
    · rfl
    · simp only [GenericWeight.leave, shifted, last, ite_true]
      abel
  · simp [GenericWeight.leave, shifted, last]

private theorem leave_labels_shifted (weights : Channel n → W) (state : GuardCounters n × W)
    (offset : W) (labels : List (Channel n)) :
    leaveGenericGuards weights (shifted state offset) labels =
      shifted (leaveGenericGuards weights state labels) offset := by
  induction labels generalizing state with
  | nil => rfl
  | cons label rest ih =>
      change leaveGenericGuards weights (GenericWeight.leave weights (shifted state offset) label) rest = _
      rw [leave_shifted, ih]
      rfl

/-- Exit order is independent even for an arbitrary cached-weight offset.
Repeated labels remain counted; the ordered group handles the offset exactly. -/
theorem leave_reverse_generic (weights : Channel n → W) (state : GuardCounters n × W)
    (labels : List (Channel n)) :
    leaveGenericGuards weights state labels.reverse = leaveGenericGuards weights state labels := by
  let canonical : GuardCounters n × W := (state.1, GenericWeight.total weights (blockedChannels state.1))
  let offset := state.2 - canonical.2
  have represented : state = shifted canonical offset := by
    apply Prod.ext
    · rfl
    · change state.2 = canonical.2 + (state.2 - canonical.2)
      abel
  rw [represented, leave_labels_shifted, leave_labels_shifted]
  congr 1
  apply Prod.ext
  · rw [leaveGenericGuards_counters, leaveGenericGuards_counters, leave_reverse]
  · rw [leaveGenericGuards_correct weights canonical labels.reverse (by rfl),
      leaveGenericGuards_correct weights canonical labels (by rfl)]
    rw [leaveGenericGuards_counters, leaveGenericGuards_counters, leave_reverse]

theorem indexed_enter_generic (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (owner : ℕ) (labels : List (Channel n)) (state : WeightedState n W) :
    ((List.finRange labels.length).map (fun position =>
      CursorOp.enter owner position.val (labels.get position))).foldl
        (weightedStep weights b target total) state =
      (enterGenericGuards weights state.1 labels, state.2) := by
  rw [List.foldl_map]
  calc
    _ = ((List.finRange labels.length).map labels.get).foldl
        (fun previous label => (GenericWeight.enter weights previous.1 label, previous.2)) state := by
      rw [List.foldl_map]
      rfl
    _ = labels.foldl
        (fun previous label => (GenericWeight.enter weights previous.1 label, previous.2)) state := by
      rw [List.map_get_finRange]
    _ = _ := fold_pair labels _ state.1 state.2

theorem indexed_leave_generic (weights : Channel n → W) (b : ℕ) (target : Channel n)
    (total : W) (owner : ℕ) (labels : List (Channel n)) (state : WeightedState n W) :
    ((List.finRange labels.length).reverse.map (fun position =>
      CursorOp.leave owner position.val (labels.get position))).foldl
        (weightedStep weights b target total) state =
      (leaveGenericGuards weights state.1 labels, state.2) := by
  rw [List.foldl_map]
  calc
    _ = ((List.finRange labels.length).reverse.map labels.get).foldl
        (fun previous label => (GenericWeight.leave weights previous.1 label, previous.2)) state := by
      rw [List.foldl_map]
      rfl
    _ = labels.reverse.foldl
        (fun previous label => (GenericWeight.leave weights previous.1 label, previous.2)) state := by
      rw [List.map_reverse, List.map_get_finRange]
    _ = (leaveGenericGuards weights state.1 labels.reverse, state.2) :=
      fold_pair labels.reverse _ state.1 state.2
    _ = _ := by rw [leave_reverse_generic]

/-- The arithmetic-bearing source operation fold refines the production
ordered-weight cursor, with its single supplied total shared by all callbacks. -/
theorem weighted_cursor_correct (graph : DAG n) (weights : Channel n → W)
    (node : Fin graph.nodeCount) (routePrefix : LeafRoute) (b : ℕ) (target : Channel n)
    (total : W) (state : WeightedState n W) :
    (cursorOps graph node routePrefix).foldl (weightedStep weights b target total) state =
      graph.foldGenericLeafCursor weights node routePrefix state.1 state.2
        (keepBestGenericRoute b target total) := by
  have claim : ∀ rank : ℕ, ∀ current : Fin graph.nodeCount, current.val = rank →
      ∀ routePrefix : LeafRoute, ∀ state : WeightedState n W,
        (cursorOps graph current routePrefix).foldl (weightedStep weights b target total) state =
          graph.foldGenericLeafCursor weights current routePrefix state.1 state.2
            (keepBestGenericRoute b target total) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current equal route currentState
      rw [cursorOps, foldGenericLeafCursor]
      cases equation : graph.node current with
      | zero => rfl
      | input head => rfl
      | liveAnd left right => rfl
      | disj refs =>
          simp only [List.foldl_cons, weightedStep, List.foldl_flatMap]
          congr 1
          funext previous position
          simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, weightedStep] using
            ih _ (by have earlier := graph.childIndex_lt current (refs.get position); omega)
              _ rfl (position.val :: route) previous
      | guard child labels =>
          simp only [List.foldl_cons, weightedStep, List.foldl_append, List.foldl_nil]
          rw [indexed_enter_generic]
          rw [ih _ (by have earlier := graph.childIndex_lt current child; omega) _ rfl]
          rw [indexed_leave_generic]
  exact claim node.val node rfl routePrefix state

/-- Exact production result and arithmetic-call count for one actual source
root. The reverse trace accumulator performs at most two conses per source step. -/
theorem source_trace_correct (graph : DAG n) (weights : Channel n → W)
    (root : Fin graph.nodeCount) (b : ℕ) (target : Channel n) (total : W)
    (state : WeightedState n W) :
    (runTrace weights b target total state (cursorOps graph root [])).1 =
      graph.foldGenericLeafCursor weights root [] state.1 state.2
        (keepBestGenericRoute b target total) ∧
    (runTrace weights b target total state (cursorOps graph root [])).2.length ≤
      2 * (cursorOps graph root []).length := by
  exact ⟨(runTrace_projection weights b target total state _).trans
    (weighted_cursor_correct graph weights root [] b target total state),
    runTrace_length weights b target total state _⟩

def sumTraceStep (state : W × List (Arithmetic W)) (weight : W) : W × List (Arithmetic W) :=
  let value := state.1 + weight
  (value, .add state.1 weight :: state.2)

def cacheTotal (weights : Channel n → W) : W × List (Arithmetic W) :=
  (List.ofFn weights).foldl sumTraceStep (0, [])

private theorem sum_trace_value (items : List W) (state : W × List (Arithmetic W)) :
    (items.foldl sumTraceStep state).1 = state.1 + items.sum := by
  induction items generalizing state with
  | nil => simp
  | cons weight rest ih =>
      change (rest.foldl sumTraceStep (sumTraceStep state weight)).1 = _
      rw [ih]
      simp [sumTraceStep, add_assoc]

private theorem sum_trace_length (items : List W) (state : W × List (Arithmetic W)) :
    (items.foldl sumTraceStep state).2.length = state.2.length + items.length := by
  induction items generalizing state with
  | nil => simp
  | cons weight rest ih =>
      change (rest.foldl sumTraceStep (sumTraceStep state weight)).2.length = _
      rw [ih]
      simp [sumTraceStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The caller computes the global total once, by exactly n additions. That
trace is shared rather than inserted into each root's arithmetic trace. -/
theorem cacheTotal_correct (weights : Channel n → W) :
    (cacheTotal weights).1 = GenericWeight.total weights Finset.univ ∧
    (cacheTotal weights).2.length = n := by
  constructor
  · simpa [cacheTotal, GenericWeight.total, List.sum_ofFn] using
      sum_trace_value (List.ofFn weights) (0, [])
  · simpa [cacheTotal] using sum_trace_length (List.ofFn weights) (0, [])

/-- One shared total computation followed by the actual declared-root scans. -/
def runAllRoots (graph : DAG n) (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    (W × List (Arithmetic W)) × List (WeightedState n W × List (Arithmetic W)) :=
  let cached := cacheTotal weights
  (cached, graph.roots.map fun root =>
    runTrace weights b target cached.1 ((fun _ => 0, 0), none) (cursorOps graph root []))

def allArithmeticLength (result : (W × List (Arithmetic W)) ×
    List (WeightedState n W × List (Arithmetic W))) : ℕ :=
  result.1.2.length + (result.2.map fun root => root.2.length).sum

private theorem root_trace_sum (graph : DAG n) (weights : Channel n → W) (b : ℕ)
    (target : Channel n) (total : W) (roots : List (Fin graph.nodeCount)) :
    (roots.map fun root =>
      (runTrace weights b target total ((fun _ => 0, 0), none) (cursorOps graph root [])).2.length).sum ≤
      2 * (roots.map (Controller.Cost.ForestCursorCharging.operationBudget graph)).sum := by
  induction roots with
  | nil => simp
  | cons root rest ih =>
      have bounded := runTrace_length weights b target total ((fun _ => 0, 0), none) (cursorOps graph root [])
      rw [Controller.Cost.ForestCursorCharging.cursor_length] at bounded
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The actual shared-total caller executes at most n + 8(q+C) + 4K generic
arithmetic operations. This is independent of operand encoding costs and of
constructing or materializing the source traversal and reconstruction witnesses. -/
theorem allRoots_arithmetic_bound (graph : DAG n) (forest : graph.FormulaForest)
    (weights : Channel n → W) (b : ℕ) (target : Channel n) :
    allArithmeticLength (runAllRoots graph weights b target) ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences := by
  have sumBound := root_trace_sum graph weights b target (cacheTotal weights).1 graph.roots
  have budget := Controller.Cost.ForestCursorCharging.all_root_budget_bound graph forest
  have cached := (cacheTotal_correct weights).2
  simp only [allArithmeticLength, runAllRoots, List.map_map, Function.comp_def]
  rw [cached]
  unfold Controller.Cost.ForestCursorCharging.allRootBudget at budget
  omega

end Controller.Cost.ForestWeightedTrace
