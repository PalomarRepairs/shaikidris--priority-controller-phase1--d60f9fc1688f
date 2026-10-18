module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestGuardSchedule
public import Controller.Cost.ForestOccurrences
public import Controller.Cost.ForestGuardVisits
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Guard events constructed into an existing tail

The executable walker prepends local labels and folds children into a supplied
tail. It never copies a completed subtree event list. The constructor trace
below counts explicit list-cons operations; indexed-machine graph navigation,
label reversal and compilation require their own refinements.
-/
namespace Controller.Cost.ForestGuardAccumulator

open Controller.Decoder Controller.Cost.ForestGuardSchedule

variable {n : ℕ}

def prepend (labels : List (Channel n)) (make : Channel n → GuardEvent n)
    (tail : List (GuardEvent n)) : List (GuardEvent n) :=
  labels.foldr (fun coordinate rest => make coordinate :: rest) tail

theorem prepend_eq (labels : List (Channel n)) (make : Channel n → GuardEvent n)
    (tail : List (GuardEvent n)) : prepend labels make tail = labels.map make ++ tail := by
  induction labels with
  | nil => rfl
  | cons coordinate rest ih =>
      change make coordinate :: prepend rest make tail = make coordinate :: (rest.map make ++ tail)
      rw [ih]

/-- A constructor trace records only cons operations, without a machine claim. -/
inductive PrependTrace (make : Channel n → GuardEvent n) :
    List (Channel n) → List (GuardEvent n) → List (GuardEvent n) → ℕ → Prop where
  | empty (tail) : PrependTrace make [] tail tail 0
  | cons (coordinate) {labels tail result steps} :
      PrependTrace make labels tail result steps →
      PrependTrace make (coordinate :: labels) tail (make coordinate :: result) (steps + 1)

theorem prepend_trace (labels : List (Channel n)) (make : Channel n → GuardEvent n)
    (tail : List (GuardEvent n)) :
    PrependTrace make labels tail (prepend labels make tail) labels.length := by
  induction labels with
  | nil => exact .empty tail
  | cons coordinate rest ih => simpa [prepend, List.length_cons, Nat.add_comm] using PrependTrace.cons coordinate ih

/-- Exit events enter the tail first, then the subtree, then entry events. -/
def walkAcc (graph : DAG n) (index : Fin graph.nodeCount) (tail : List (GuardEvent n)) :
    List (GuardEvent n) :=
  match graph.node index with
  | .zero | .input _ | .liveAnd _ _ => tail
  | .disj children => children.foldr
      (fun child result => walkAcc graph (graph.childIndex index child) result) tail
  | .guard child labels => prepend labels GuardEvent.enter
      (walkAcc graph (graph.childIndex index child) (prepend labels.reverse GuardEvent.leave tail))
termination_by index.val
decreasing_by all_goals exact graph.childIndex_lt _ _

/-- Tail construction is exactly the schedule specification followed by that tail. -/
theorem walkAcc_eq (graph : DAG n) :
    ∀ (index : Fin graph.nodeCount) (tail : List (GuardEvent n)),
      walkAcc graph index tail = walkEvents graph index ++ tail := by
  have claim : ∀ rank : ℕ, ∀ index : Fin graph.nodeCount, index.val = rank →
      ∀ tail : List (GuardEvent n), walkAcc graph index tail = walkEvents graph index ++ tail := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro index value tail
      rw [walkAcc.eq_def, walkEvents.eq_def]
      cases equation : graph.node index with
      | zero => rfl
      | input coordinate => rfl
      | liveAnd left right => rfl
      | disj children =>
          have childrenClaim : ∀ refs : List (Fin index.val),
              refs.foldr (fun child result => walkAcc graph (graph.childIndex index child) result) tail =
                (refs.flatMap fun child => walkEvents graph (graph.childIndex index child)) ++ tail := by
            intro refs
            induction refs with
            | nil => rfl
            | cons child rest restIH =>
                rw [List.foldr_cons, ih child.val
                  (by have earlier := graph.childIndex_lt index child; omega)
                  (graph.childIndex index child) rfl, restIH]
                simp [List.flatMap_cons, List.append_assoc]
          exact childrenClaim children
      | guard child labels =>
          simp only []
          rw [prepend_eq, ih child.val
            (by have earlier := graph.childIndex_lt index child; omega)
            (graph.childIndex index child) rfl, prepend_eq]
          simp only [List.append_assoc]
  intro index tail
  exact claim index.val index rfl tail

def rootAcc (graph : DAG n) (tail : List (GuardEvent n)) : List (GuardEvent n) :=
  graph.roots.foldr (walkAcc graph) tail

theorem rootAcc_eq (graph : DAG n) (tail : List (GuardEvent n)) :
    rootAcc graph tail = rootEvents graph ++ tail := by
  unfold rootAcc rootEvents
  induction graph.roots with
  | nil => rfl
  | cons index rest ih =>
      rw [List.foldr_cons, walkAcc_eq, ih]
      simp [List.flatMap_cons, List.append_assoc]

/- The constructor relation follows the tail walker. Its cost records only
list-cons operations; gate access, child access and reversal are separate. -/
mutual
  inductive WalkConsTrace (graph : DAG n) : Fin graph.nodeCount →
      List (GuardEvent n) → List (GuardEvent n) → ℕ → Prop where
    | zero {node tail} (equation : graph.node node = .zero) :
        WalkConsTrace graph node tail tail 0
    | input {node tail coordinate} (equation : graph.node node = .input coordinate) :
        WalkConsTrace graph node tail tail 0
    | liveAnd {node tail left right} (equation : graph.node node = .liveAnd left right) :
        WalkConsTrace graph node tail tail 0
    | disj {node children tail result steps}
        (equation : graph.node node = .disj children)
        (childrenTrace : ChildrenConsTrace graph node children tail result steps) :
        WalkConsTrace graph node tail result steps
    | guard {node child labels tail exitTail childResult result exitSteps childSteps entrySteps}
        (equation : graph.node node = .guard child labels)
        (exits : PrependTrace GuardEvent.leave labels.reverse tail exitTail exitSteps)
        (childTrace : WalkConsTrace graph (graph.childIndex node child) exitTail childResult childSteps)
        (entries : PrependTrace GuardEvent.enter labels childResult result entrySteps) :
        WalkConsTrace graph node tail result (exitSteps + childSteps + entrySteps)
  inductive ChildrenConsTrace (graph : DAG n) : (node : Fin graph.nodeCount) →
      List (Fin node.val) → List (GuardEvent n) → List (GuardEvent n) → ℕ → Prop where
    | empty {node} (tail) : ChildrenConsTrace graph node [] tail tail 0
    | cons {node child children tail afterChildren result childSteps restSteps}
        (restTrace : ChildrenConsTrace graph node children tail afterChildren restSteps)
        (childTrace : WalkConsTrace graph (graph.childIndex node child) afterChildren result childSteps) :
        ChildrenConsTrace graph node (child :: children) tail result (restSteps + childSteps)
end

/-- Every execution of the tail walker has the stated constructor trace. -/
theorem walk_cons_trace (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (tail : List (GuardEvent n)),
      WalkConsTrace graph node tail (walkAcc graph node tail) (walkEvents graph node).length := by
  have claim : ∀ rank : ℕ, ∀ (node : Fin graph.nodeCount), node.val = rank →
      ∀ tail : List (GuardEvent n),
        WalkConsTrace graph node tail (walkAcc graph node tail) (walkEvents graph node).length := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value tail
      rw [walkAcc.eq_def, walkEvents.eq_def]
      cases equation : graph.node node with
      | zero => exact .zero equation
      | input coordinate => exact .input equation
      | liveAnd left right => exact .liveAnd equation
      | disj children =>
          have childrenClaim : ∀ refs : List (Fin node.val),
              ChildrenConsTrace graph node refs tail
                (refs.foldr (fun child result => walkAcc graph (graph.childIndex node child) result) tail)
                (refs.flatMap fun child => walkEvents graph (graph.childIndex node child)).length := by
            intro refs
            induction refs with
            | nil => exact .empty tail
            | cons child rest restIH =>
                have childTrace := ih child.val
                  (by have earlier := graph.childIndex_lt node child; omega)
                  (graph.childIndex node child) rfl
                  (rest.foldr (fun child result => walkAcc graph (graph.childIndex node child) result) tail)
                simpa only [List.foldr_cons, List.flatMap_cons, List.length_append,
                  Nat.add_comm] using ChildrenConsTrace.cons restIH childTrace
          exact .disj equation (childrenClaim children)
      | guard child labels =>
          have childTrace := ih child.val
            (by have earlier := graph.childIndex_lt node child; omega)
            (graph.childIndex node child) rfl
            (prepend labels.reverse GuardEvent.leave tail)
          have trace := WalkConsTrace.guard equation
            (prepend_trace labels.reverse GuardEvent.leave tail) childTrace
            (prepend_trace labels GuardEvent.enter
              (walkAcc graph (graph.childIndex node child) (prepend labels.reverse GuardEvent.leave tail)))
          simpa only [List.length_append, List.length_map, List.length_reverse,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using trace
  intro node tail
  exact claim node.val node rfl tail

inductive RootsConsTrace (graph : DAG n) : List (Fin graph.nodeCount) →
    List (GuardEvent n) → List (GuardEvent n) → ℕ → Prop where
  | empty (tail) : RootsConsTrace graph [] tail tail 0
  | cons {node roots tail afterRoots result nodeSteps restSteps}
      (restTrace : RootsConsTrace graph roots tail afterRoots restSteps)
      (nodeTrace : WalkConsTrace graph node afterRoots result nodeSteps) :
      RootsConsTrace graph (node :: roots) tail result (restSteps + nodeSteps)

theorem root_cons_trace (graph : DAG n) (tail : List (GuardEvent n)) :
    RootsConsTrace graph graph.roots tail (rootAcc graph tail) (rootEvents graph).length := by
  have claim : ∀ roots : List (Fin graph.nodeCount),
      RootsConsTrace graph roots tail (roots.foldr (walkAcc graph) tail)
        (roots.flatMap (walkEvents graph)).length := by
    intro roots
    induction roots with
    | nil => exact .empty tail
    | cons node rest restIH =>
        have nodeTrace := walk_cons_trace graph node (rest.foldr (walkAcc graph) tail)
        simpa only [List.foldr_cons, List.flatMap_cons, List.length_append,
          Nat.add_comm] using RootsConsTrace.cons restIH nodeTrace
  exact claim graph.roots

/-- A constructor-operation bound, independent of a RAM refinement. -/
theorem root_cons_trace_bound (graph : DAG n) (forest : graph.FormulaForest)
    (tail : List (GuardEvent n)) :
    ∃ steps, RootsConsTrace graph graph.roots tail (rootAcc graph tail) steps ∧
      steps ≤ 2 * graph.guardIncidences := by
  exact ⟨(rootEvents graph).length, root_cons_trace graph tail,
    Controller.Cost.ForestGuardVisits.root_event_count_le graph forest⟩

/-- The finite budget includes every root and child position, even when several
positions refer to the same terminal. -/
theorem stored_occurrence_card (graph : DAG n) :
    Nat.card graph.StoredOccurrence = graph.roots.length + graph.childIncidences := by
  simp only [DAG.StoredOccurrence, DAG.ParentOccurrence, Nat.card_sum, Nat.card_sigma,
    Nat.card_fin, Nat.card_eq_fintype_card]
  simp [DAG.childIncidences, List.sum_ofFn]

/-- Every positional visit, including a shared terminal, has one route per
incoming root/child position. Endpoint uniqueness is not assumed for terminals. -/
theorem rooted_route_eq_of_incoming (graph : DAG n) (forest : graph.FormulaForest)
    (firstNode secondNode : Fin graph.nodeCount)
    (firstRoute secondRoute : List graph.StoredOccurrence)
    (firstPath : Controller.Cost.ForestOccurrences.RootedPath graph firstNode firstRoute)
    (secondPath : Controller.Cost.ForestOccurrences.RootedPath graph secondNode secondRoute)
    (incoming : firstRoute.head? = secondRoute.head?) : firstRoute = secondRoute := by
  cases firstPath with
  | root firstPosition =>
      cases secondPath with
      | root secondPosition =>
          simp only [List.head?_cons, Option.some.injEq, Sum.inl.injEq] at incoming
          cases incoming
          rfl
      | child parent position ancestorRoute path =>
          simp only [List.head?_cons, Option.some.injEq] at incoming
          cases incoming
  | child firstParent firstPosition firstAncestor firstAncestorPath =>
      cases secondPath with
      | root secondPosition =>
          simp only [List.head?_cons, Option.some.injEq] at incoming
          cases incoming
      | child secondParent secondPosition secondAncestor secondAncestorPath =>
          have positions : (⟨firstParent, firstPosition⟩ : graph.ParentOccurrence) =
              ⟨secondParent, secondPosition⟩ := by
            exact Sum.inr.inj (Option.some.inj incoming)
          have parents : firstParent = secondParent := congrArg Sigma.fst positions
          subst secondParent
          have childPositions : firstPosition = secondPosition := Fin.ext
            (congrArg (fun position : graph.ParentOccurrence => position.2.val) positions)
          subst secondPosition
          have ancestors := Controller.Cost.ForestOccurrences.RootedPath.unique_internal
            graph forest firstParent firstAncestor secondAncestor
            (Controller.Cost.ForestOccurrences.parent_internal graph firstParent firstPosition)
            firstAncestorPath secondAncestorPath
          rw [ancestors]

/-- Ghost node visits retain positional routes, never runtime path allocations. -/
structure NodeVisit (graph : DAG n) where
  node : Fin graph.nodeCount
  route : List graph.StoredOccurrence
  rooted : Controller.Cost.ForestOccurrences.RootedPath graph node route

def NodeVisit.incoming {graph : DAG n} (visit : NodeVisit graph) : graph.StoredOccurrence :=
  visit.route.head visit.rooted.nonempty

theorem incoming_refers (graph : DAG n) (visit : NodeVisit graph) :
    graph.refers visit.incoming = visit.node := by
  cases visit with
  | mk node route rooted => cases rooted <;> rfl

/-- Distinct visits are charged to distinct positions, including shared terminals. -/
theorem incoming_injective (graph : DAG n) (forest : graph.FormulaForest) :
    Function.Injective (NodeVisit.incoming (graph := graph)) := by
  intro first second equal
  have nodes : first.node = second.node := by
    rw [← incoming_refers graph first, ← incoming_refers graph second]
    exact congrArg graph.refers equal
  cases first with
  | mk firstNode firstRoute firstPath =>
    cases second with
    | mk secondNode secondRoute secondPath =>
      dsimp only at nodes
      subst secondNode
      have routes := rooted_route_eq_of_incoming graph forest firstNode firstNode
        firstRoute secondRoute firstPath secondPath (by
          rw [List.head?_eq_some_head firstPath.nonempty,
            List.head?_eq_some_head secondPath.nonempty]
          exact congrArg some equal)
      subst secondRoute
      rfl

/-- Abstract node-visit budget. Generated-list distinctness is a separate bridge. -/
theorem node_visit_card_le (graph : DAG n) (forest : graph.FormulaForest) :
    Nat.card (NodeVisit graph) ≤ graph.roots.length + graph.childIncidences := by
  exact (Nat.card_le_card_of_injective (NodeVisit.incoming (graph := graph))
    (incoming_injective graph forest)).trans_eq (stored_occurrence_card graph)

end Controller.Cost.ForestGuardAccumulator
