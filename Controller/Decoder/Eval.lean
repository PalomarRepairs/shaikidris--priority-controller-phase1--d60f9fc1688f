module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Syntax
public import Mathlib.Data.Finset.Union

@[expose] public section

/-!
# Decoder evaluation and syntactic channel scope

Evaluation follows earlier node references. Scope includes all reachable
positive-channel and guard occurrences, including occurrences in false
branches. Agreement on that scope is sufficient for equal evaluation. These
are semantic recursions on the stored DAG. A prefix-table fold computes the
same node values in topological order, without a runtime claim.
-/

namespace Controller.Decoder

private theorem any_congr_on {α : Type*} (items : List α) (first second : α → Bool) :
    (∀ item ∈ items, first item = second item) → items.any first = items.any second := by
  induction items with
  | nil =>
      intro _
      rfl
  | cons item rest inductionHypothesis =>
      intro agreement
      have headAgreement := agreement item (by simp)
      have tailAgreement : ∀ other ∈ rest, first other = second other := by
        intro other membership
        exact agreement other (by simp [membership])
      simp only [List.any_cons]
      rw [headAgreement, inductionHypothesis tailAgreement]

namespace Gate

variable {n available : ℕ}

/-- A gate reads only its listed direct channels and live children. -/
theorem eval_congr (gate : Gate n available) (first second : Assignment n)
    (firstEarlier secondEarlier : Fin available → Bool)
    (channelAgreement : ∀ channel ∈ gate.directChannels, first channel = second channel)
    (childAgreement : ∀ child ∈ gate.children, firstEarlier child = secondEarlier child) :
    gate.eval first firstEarlier = gate.eval second secondEarlier := by
  cases gate with
  | zero => rfl
  | input channel =>
      exact channelAgreement channel (by simp [directChannels])
  | disj refs =>
      exact any_congr_on refs firstEarlier secondEarlier (by
        simpa only [children] using childAgreement)
  | guard child labels =>
      have childEquality := childAgreement child (by simp [children])
      have guardEquality := any_congr_on labels first second (by
        simpa only [directChannels] using channelAgreement)
      simp only [eval, childEquality, guardEquality]
  | liveAnd left right =>
      have leftEquality := childAgreement left (by simp [children])
      have rightEquality := childAgreement right (by simp [children])
      simp only [eval, leftEquality, rightEquality]

/-- With all channels and live children false, every permitted gate is false. -/
@[simp] theorem eval_false (gate : Gate n available) :
    gate.eval (fun _ => false) (fun _ => false) = false := by
  cases gate <;> simp [eval]

end Gate

namespace DAG

variable {n : ℕ}

/-- Evaluate a represented node by recursion on its topological index. -/
def eval (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount) : Bool :=
  (graph.node index).eval assignment (fun child =>
    graph.eval assignment (graph.childIndex index child))
termination_by index.val
decreasing_by exact graph.childIndex_lt index child

/-- The gate equation defining a node's semantic value. -/
theorem eval_eq (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount) :
    graph.eval assignment index =
      (graph.node index).eval assignment (fun child =>
        graph.eval assignment (graph.childIndex index child)) := by
  rw [eval]

/-- Build a value table for an initial segment, extending it by one evaluated gate. -/
def evalPrefix (graph : DAG n) (assignment : Assignment n) :
    (length : ℕ) → length ≤ graph.nodeCount → Fin length → Bool
  | 0, _ => Fin.elim0
  | length + 1, bound =>
      let earlier := graph.evalPrefix assignment length
        (Nat.le_trans (Nat.le_succ length) bound)
      let gate := graph.node ⟨length, Nat.lt_of_lt_of_le (Nat.lt_succ_self length) bound⟩
      Fin.lastCases (gate.eval assignment earlier) earlier

/-- Every entry in a prefix table agrees with its semantic node value. -/
theorem evalPrefix_eq_eval (graph : DAG n) (assignment : Assignment n) :
    ∀ (length : ℕ) (bound : length ≤ graph.nodeCount) (index : Fin length),
      graph.evalPrefix assignment length bound index =
        graph.eval assignment (index.castLE bound) := by
  intro length
  induction length with
  | zero =>
      intro bound index
      exact Fin.elim0 index
  | succ length inductionHypothesis =>
      intro bound index
      refine Fin.lastCases ?_ (fun earlierIndex => ?_) index
      · simp only [evalPrefix, Fin.lastCases_last]
        rw [graph.eval_eq]
        apply Gate.eval_congr
        · intro channel membership
          rfl
        · intro child membership
          exact inductionHypothesis _ child
      · simp only [evalPrefix, Fin.lastCases_castSucc]
        simpa only [Fin.castLE, Fin.castSucc, Fin.castAdd] using
          inductionHypothesis (Nat.le_trans (Nat.le_succ length) bound) earlierIndex

/-- The complete finite value table obtained by the topological prefix fold. -/
def evalTable (graph : DAG n) (assignment : Assignment n) : Fin graph.nodeCount → Bool :=
  graph.evalPrefix assignment graph.nodeCount (Nat.le_refl graph.nodeCount)

/-- Topological table evaluation and semantic evaluation agree pointwise. -/
theorem evalTable_eq_eval (graph : DAG n) (assignment : Assignment n) :
    graph.evalTable assignment = graph.eval assignment := by
  funext index
  exact graph.evalPrefix_eq_eval assignment graph.nodeCount (Nat.le_refl _) index

/-- Every syntactically reachable positive or negative channel label. -/
def scope (graph : DAG n) (index : Fin graph.nodeCount) : Finset (Channel n) :=
  (graph.node index).directChannels.toFinset ∪
    (graph.node index).children.toFinset.biUnion (fun child =>
      graph.scope (graph.childIndex index child))
termination_by index.val
decreasing_by exact graph.childIndex_lt index child

/-- Scope consists of direct channels and the scopes of listed child references. -/
theorem scope_eq (graph : DAG n) (index : Fin graph.nodeCount) :
    graph.scope index = (graph.node index).directChannels.toFinset ∪
      (graph.node index).children.toFinset.biUnion (fun child =>
        graph.scope (graph.childIndex index child)) := by
  rw [scope]

/-- Every direct channel of a node belongs to that node's scope. -/
theorem mem_scope_of_mem_directChannels (graph : DAG n) (index : Fin graph.nodeCount)
    {channel : Channel n} (membership : channel ∈ (graph.node index).directChannels) :
    channel ∈ graph.scope index := by
  rw [scope_eq]
  exact Finset.mem_union_left _ (by simpa using membership)

/-- The scope of a listed child is contained in its parent's scope. -/
theorem scope_child_subset (graph : DAG n) (index : Fin graph.nodeCount)
    (child : Fin index.val) (membership : child ∈ (graph.node index).children) :
    graph.scope (graph.childIndex index child) ⊆ graph.scope index := by
  intro channel channelMembership
  rw [scope_eq]
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨child, by simpa using membership, channelMembership⟩)

/-- Agreement on a node's syntactic scope implies equality of its value. -/
theorem eval_eq_of_agree_scope (graph : DAG n) (first second : Assignment n)
    (index : Fin graph.nodeCount)
    (agreement : ∀ channel ∈ graph.scope index, first channel = second channel) :
    graph.eval first index = graph.eval second index := by
  have inductionClaim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount,
      current.val = bound →
      (∀ channel ∈ graph.scope current, first channel = second channel) →
      graph.eval first current = graph.eval second current := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound inductionHypothesis =>
        intro current currentBound currentAgreement
        rw [graph.eval_eq first current, graph.eval_eq second current]
        apply Gate.eval_congr
        · intro channel membership
          exact currentAgreement channel
            (graph.mem_scope_of_mem_directChannels current membership)
        · intro child membership
          have earlier : child.val < bound := by
            simpa only [currentBound] using child.isLt
          apply inductionHypothesis child.val earlier (graph.childIndex current child) rfl
          intro channel channelMembership
          exact currentAgreement channel
            (graph.scope_child_subset current child membership channelMembership)
  exact inductionClaim index.val index rfl agreement

/-- A zero node is false on every assignment. -/
theorem eval_zero (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount)
    (gateEquation : graph.node index = .zero) : graph.eval assignment index = false := by
  simpa only [gateEquation, Gate.eval] using graph.eval_eq assignment index

/-- A channel node reads precisely its labelled channel. -/
theorem eval_input (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount)
    (channel : Channel n) (gateEquation : graph.node index = .input channel) :
    graph.eval assignment index = assignment channel := by
  simpa only [gateEquation, Gate.eval] using graph.eval_eq assignment index

/-- An OR node uses all listed children, including repeated incidences. -/
theorem eval_disj (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount)
    (refs : List (Fin index.val)) (gateEquation : graph.node index = .disj refs) :
    graph.eval assignment index =
      refs.any (fun child => graph.eval assignment (graph.childIndex index child)) := by
  simpa only [gateEquation, Gate.eval] using graph.eval_eq assignment index

/-- A guard reads its live child and the negative channel labels. -/
theorem eval_guard (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount)
    (child : Fin index.val) (labels : List (Channel n))
    (gateEquation : graph.node index = .guard child labels) :
    graph.eval assignment index =
      (graph.eval assignment (graph.childIndex index child) && !(labels.any assignment)) := by
  simpa only [gateEquation, Gate.eval] using graph.eval_eq assignment index

/-- A live conjunction reads both child references. -/
theorem eval_liveAnd (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount)
    (left right : Fin index.val) (gateEquation : graph.node index = .liveAnd left right) :
    graph.eval assignment index =
      (graph.eval assignment (graph.childIndex index left) &&
        graph.eval assignment (graph.childIndex index right)) := by
  simpa only [gateEquation, Gate.eval] using graph.eval_eq assignment index

/-- Every decoder node is false when every channel is false, including live-AND nodes. -/
theorem eval_false (graph : DAG n) (index : Fin graph.nodeCount) :
    graph.eval (fun _ => false) index = false := by
  have inductionClaim : ∀ bound : ℕ, ∀ current : Fin graph.nodeCount,
      current.val = bound → graph.eval (fun _ => false) current = false := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound inductionHypothesis =>
        intro current currentBound
        rw [eval_eq]
        have childValues :
            (fun child : Fin current.val =>
              graph.eval (fun _ => false) (graph.childIndex current child)) =
            (fun _ => false) := by
          funext child
          apply inductionHypothesis child.val _ (graph.childIndex current child) rfl
          simpa only [currentBound] using child.isLt
        rw [childValues]
        exact Gate.eval_false _
  exact inductionClaim index.val index rfl

/-- The set-valued empty assignment makes every decoder node false. -/
@[simp] theorem eval_empty (graph : DAG n) (index : Fin graph.nodeCount) :
    graph.eval (assignmentOfSet ∅) index = false := by
  rw [assignmentOfSet_empty]
  exact graph.eval_false index

/-- Values of the observed roots, preserving their given order and multiplicity. -/
def outputValues (graph : DAG n) (assignment : Assignment n) : List Bool :=
  graph.roots.map (graph.eval assignment)

/-- Channels occurring in any observed root's syntactic cone. -/
def outputScope (graph : DAG n) : Finset (Channel n) :=
  graph.roots.toFinset.biUnion graph.scope

/-- Agreement on the output scope preserves the complete observed vector. -/
theorem outputValues_eq_of_agree_scope (graph : DAG n) (first second : Assignment n)
    (agreement : ∀ channel ∈ graph.outputScope, first channel = second channel) :
    graph.outputValues first = graph.outputValues second := by
  apply List.map_congr_left
  intro index membership
  apply graph.eval_eq_of_agree_scope first second index
  intro channel channelMembership
  apply agreement channel
  exact Finset.mem_biUnion.mpr
    ⟨index, by simpa using membership, channelMembership⟩

end DAG
end Controller.Decoder
