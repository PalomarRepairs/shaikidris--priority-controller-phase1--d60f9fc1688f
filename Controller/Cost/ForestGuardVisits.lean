module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestGuardCharging
public import Controller.Cost.ForestGuardSchedule
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup

@[expose] public section

/-!
# Ghost positional witnesses for guard events

Annotated routes serve only as proof witnesses for event counting. The runtime
schedule contains channel events, not these full paths. Cardinality bounds here
do not assert linear-time construction of an annotated list or of the schedule.
-/
namespace Controller.Cost.ForestGuardVisits

open Controller.Decoder Controller.Cost.ForestOccurrences
open Controller.Cost.ForestGuardCharging Controller.Cost.ForestGuardSchedule

variable {n : ℕ}

/-- Stored label positions, with a fixed rooted route and phase. -/
def ownVisits (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
    (phase : Bool) : List (GuardVisit graph) :=
  List.ofFn fun position : Fin (graph.node node).guardLabels.length =>
    ⟨node, route, rooted, position, phase⟩

theorem own_route (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
    (phase : Bool) (visit : GuardVisit graph)
    (present : visit ∈ ownVisits graph node route rooted phase) : visit.route = route := by
  obtain ⟨position, equal⟩ := List.mem_ofFn.mp present
  cases equal
  rfl

theorem own_phase (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
    (phase : Bool) (visit : GuardVisit graph)
    (present : visit ∈ ownVisits graph node route rooted phase) : visit.phase = phase := by
  obtain ⟨position, equal⟩ := List.mem_ofFn.mp present
  cases equal
  rfl

theorem own_nodup (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
    (phase : Bool) : (ownVisits graph node route rooted phase).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro first second equal
  exact Fin.ext (congrArg (fun visit : GuardVisit graph => visit.position.val) equal)

/-- This annotated unfolding is a ghost specification. -/
def walkGhost (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route) :
    List (GuardVisit graph) :=
  ownVisits graph node route rooted false ++
    (List.ofFn fun position : Fin (graph.node node).children.length =>
      walkGhost graph (graph.childIndex node ((graph.node node).children.get position))
        (.inr ⟨node, position⟩ :: route) (RootedPath.child node position route rooted)).flatten ++
    (ownVisits graph node route rooted true).reverse
termination_by node.val
decreasing_by all_goals exact graph.childIndex_lt _ _

/-- Each descendant retains the complete suffix of its ancestor's route. -/
theorem route_suffix (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (route : List graph.StoredOccurrence)
      (rooted : RootedPath graph node route) (visit : GuardVisit graph),
      visit ∈ walkGhost graph node route rooted → route <:+ visit.route := by
  have claim : ∀ rank : ℕ, ∀ (node : Fin graph.nodeCount), node.val = rank →
      ∀ (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
        (visit : GuardVisit graph),
        visit ∈ walkGhost graph node route rooted → route <:+ visit.route := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value route rooted visit present
      rw [walkGhost.eq_def] at present
      rcases List.mem_append.mp present with before | after
      · rcases List.mem_append.mp before with own | descendants
        · rw [own_route graph node route rooted false visit own]
        · obtain ⟨block, blockPresent, visitPresent⟩ := List.mem_flatten.mp descendants
          obtain ⟨position, equal⟩ := List.mem_ofFn.mp blockPresent
          subst block
          have suffix := ih ((graph.node node).children.get position).val
            (by have earlier := graph.childIndex_lt node ((graph.node node).children.get position); omega)
            _ rfl _ _ visit visitPresent
          exact (List.suffix_cons _ route).trans suffix
      · have own := List.mem_reverse.mp after
        rw [own_route graph node route rooted true visit own]
  intro node route rooted visit present
  exact claim node.val node rfl route rooted visit present

/-- Equal-length suffixes of the same list are equal. -/
theorem equal_length_suffix {first second whole : List α}
    (firstSuffix : first <:+ whole) (secondSuffix : second <:+ whole)
    (lengths : first.length = second.length) : first = second := by
  exact (List.suffix_of_suffix_length_le firstSuffix secondSuffix lengths.le).eq_of_length lengths

def childrenGhost (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route) :
    List (GuardVisit graph) :=
  (List.ofFn fun position : Fin (graph.node node).children.length =>
    walkGhost graph (graph.childIndex node ((graph.node node).children.get position))
      (.inr ⟨node, position⟩ :: route) (RootedPath.child node position route rooted)).flatten

/-- Own-node events are disjoint from every proper descendant. -/
theorem own_children_disjoint (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
    (phase : Bool) :
    List.Disjoint (ownVisits graph node route rooted phase) (childrenGhost graph node route rooted) := by
  apply List.disjoint_left.mpr
  intro visit ownPresent descendants
  have ownRoute := own_route graph node route rooted phase visit ownPresent
  obtain ⟨block, blockPresent, visitPresent⟩ := List.mem_flatten.mp descendants
  obtain ⟨position, equal⟩ := List.mem_ofFn.mp blockPresent
  subst block
  have suffix := route_suffix graph _ _ _ visit visitPresent
  have lengths := suffix.length_le
  rw [ownRoute] at lengths
  simp only [List.length_cons] at lengths
  omega

/-- Child positions distinguish even equal stored child endpoints. -/
theorem child_blocks_disjoint (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route)
    (first second : Fin (graph.node node).children.length) (different : first ≠ second) :
    List.Disjoint
      (walkGhost graph (graph.childIndex node ((graph.node node).children.get first))
        (.inr ⟨node, first⟩ :: route) (RootedPath.child node first route rooted))
      (walkGhost graph (graph.childIndex node ((graph.node node).children.get second))
        (.inr ⟨node, second⟩ :: route) (RootedPath.child node second route rooted)) := by
  apply List.disjoint_left.mpr
  intro visit firstPresent secondPresent
  have firstSuffix := route_suffix graph _ _ _ visit firstPresent
  have secondSuffix := route_suffix graph _ _ _ visit secondPresent
  have routes := equal_length_suffix firstSuffix secondSuffix rfl
  have heads := (List.cons.inj routes).1
  have positions : first = second := Fin.ext
    (congrArg (fun occurrence : graph.StoredOccurrence =>
      match occurrence with | .inl _ => 0 | .inr pair => pair.2.val) heads)
  exact different positions

/-- The ghost list is duplicate-free before the forest promise is used. -/
theorem walk_nodup (graph : DAG n) :
    ∀ (node : Fin graph.nodeCount) (route : List graph.StoredOccurrence)
      (rooted : RootedPath graph node route), (walkGhost graph node route rooted).Nodup := by
  classical
  have claim : ∀ rank : ℕ, ∀ (node : Fin graph.nodeCount), node.val = rank →
      ∀ (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route),
        (walkGhost graph node route rooted).Nodup := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value route rooted
      have childrenNodup : (childrenGhost graph node route rooted).Nodup := by
        apply List.nodup_flatten.mpr
        constructor
        · intro block blockPresent
          obtain ⟨position, equal⟩ := List.mem_ofFn.mp blockPresent
          subst block
          exact ih ((graph.node node).children.get position).val
            (by have earlier := graph.childIndex_lt node ((graph.node node).children.get position); omega)
            _ rfl _ _
        · apply List.pairwise_ofFn.mpr
          intro first second before
          exact child_blocks_disjoint graph node route rooted first second (ne_of_lt before)
      have beginningNodup := List.nodup_append'.mpr
        ⟨own_nodup graph node route rooted false, childrenNodup,
          own_children_disjoint graph node route rooted false⟩
      have endsNodup : ((ownVisits graph node route rooted true).reverse).Nodup :=
        List.nodup_reverse.mpr (own_nodup graph node route rooted true)
      have disjoint : List.Disjoint
          (ownVisits graph node route rooted false ++ childrenGhost graph node route rooted)
          (ownVisits graph node route rooted true).reverse := by
        apply List.disjoint_left.mpr
        intro visit present endPresent
        have endOwn := List.mem_reverse.mp endPresent
        rcases List.mem_append.mp present with own | descendant
        · have firstPhase := own_phase graph node route rooted false visit own
          have secondPhase := own_phase graph node route rooted true visit endOwn
          simp_all
        · exact List.disjoint_left.mp (own_children_disjoint graph node route rooted true)
            endOwn descendant
      have joined := List.nodup_append'.mpr ⟨beginningNodup, endsNodup, disjoint⟩
      rw [walkGhost.eq_def]
      exact joined
  intro node route rooted
  exact claim node.val node rfl route rooted

/-- Root positions, including repetitions, are retained in the ghost witness. -/
def rootGhost (graph : DAG n) : List (GuardVisit graph) :=
  (List.ofFn fun position : Fin graph.roots.length =>
    walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).flatten

theorem root_nodup (graph : DAG n) : (rootGhost graph).Nodup := by
  classical
  apply List.nodup_flatten.mpr
  constructor
  · intro block present
    obtain ⟨position, equal⟩ := List.mem_ofFn.mp present
    subst block
    exact walk_nodup graph _ _ _
  · apply List.pairwise_ofFn.mpr
    intro first second before
    apply List.disjoint_left.mpr
    intro visit firstPresent secondPresent
    have firstSuffix := route_suffix graph _ _ _ visit firstPresent
    have secondSuffix := route_suffix graph _ _ _ visit secondPresent
    have routes := equal_length_suffix firstSuffix secondSuffix rfl
    have positions : first = second := Sum.inl.inj (List.cons.inj routes).1
    exact (ne_of_lt before) positions

/-- The generated ghost list is charged through the checked key injection. -/
theorem root_length_le (graph : DAG n) (forest : graph.FormulaForest) :
    (rootGhost graph).length ≤ 2 * graph.guardIncidences := by
  classical
  letI : Finite (GuardVisit graph) := Finite.of_injective
    (GuardVisit.key (graph := graph)) (key_injective graph forest)
  letI : Fintype (GuardVisit graph) := Fintype.ofFinite _
  have bound : (rootGhost graph).length ≤ Nat.card (GuardVisit graph) := by
    simpa only [Nat.card_eq_fintype_card] using (root_nodup graph).length_le_card
  exact bound.trans (visit_card_le graph forest)

/-- Erase the ghost path and stored label position to the runtime channel event. -/
def event {graph : DAG n} (visit : GuardVisit graph) : GuardEvent n :=
  if visit.phase then .leave ((graph.node visit.node).guardLabels.get visit.position)
  else .enter ((graph.node visit.node).guardLabels.get visit.position)

theorem own_events (graph : DAG n) (node : Fin graph.nodeCount)
    (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route) (phase : Bool) :
    (ownVisits graph node route rooted phase).map event =
      if phase then (graph.node node).guardLabels.map GuardEvent.leave
      else (graph.node node).guardLabels.map GuardEvent.enter := by
  cases phase with
  | false =>
      rw [ownVisits, List.map_ofFn]
      exact List.ofFn_getElem_eq_map _ GuardEvent.enter
  | true =>
      rw [ownVisits, List.map_ofFn]
      exact List.ofFn_getElem_eq_map _ GuardEvent.leave

/-- Erasing annotations gives precisely the supplied guarded walk schedule. -/
theorem walk_events (graph : DAG n) (guarded : graph.Guarded) :
    ∀ (node : Fin graph.nodeCount) (route : List graph.StoredOccurrence)
      (rooted : RootedPath graph node route),
      (walkGhost graph node route rooted).map event = walkEvents graph node := by
  have claim : ∀ rank : ℕ, ∀ (node : Fin graph.nodeCount), node.val = rank →
      ∀ (route : List graph.StoredOccurrence) (rooted : RootedPath graph node route),
        (walkGhost graph node route rooted).map event = walkEvents graph node := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro node value route rooted
      have descendants : (childrenGhost graph node route rooted).map event =
          (List.ofFn fun position : Fin (graph.node node).children.length =>
            walkEvents graph (graph.childIndex node ((graph.node node).children.get position))).flatten := by
        simp only [childrenGhost, List.map_flatten, List.map_ofFn]
        apply congrArg List.flatten
        apply congrArg List.ofFn
        funext position
        exact ih ((graph.node node).children.get position).val
          (by have earlier := graph.childIndex_lt node ((graph.node node).children.get position); omega)
          _ rfl _ _
      rw [walkGhost.eq_def]
      change ((ownVisits graph node route rooted false ++ childrenGhost graph node route rooted) ++
        (ownVisits graph node route rooted true).reverse).map event = _
      rw [List.map_append, List.map_append, List.map_reverse, own_events, own_events, descendants]
      rw [walkEvents.eq_def]
      have permitted := guarded node
      cases equation : graph.node node with
      | zero => simp [equation, Gate.guardLabels, Gate.children]
      | input coordinate => simp [equation, Gate.guardLabels, Gate.children]
      | disj children =>
          simp [equation, Gate.guardLabels, Gate.children, List.flatMap]
          exact congrArg List.flatten (List.ofFn_getElem_eq_map children
            (fun child => walkEvents graph (graph.childIndex node child)))
      | guard child labels =>
          simp [equation, Gate.guardLabels, Gate.children, List.ofFn_succ, List.map_reverse]
      | liveAnd left right => simp [equation, Gate.IsGuarded, Gate.isLiveAnd] at permitted
  intro node route rooted
  exact claim node.val node rfl route rooted

/-- The runtime channel-event count, without constructing ghost paths. -/
theorem root_events (graph : DAG n) (guarded : graph.Guarded) :
    (rootGhost graph).map event = rootEvents graph := by
  simp only [rootGhost, List.map_flatten, List.map_ofFn, Function.comp_apply, rootEvents]
  have mapped : (List.ofFn fun position : Fin graph.roots.length =>
      (walkGhost graph (graph.roots.get position) [.inl position] (RootedPath.root position)).map event) =
      List.ofFn fun position : Fin graph.roots.length => walkEvents graph (graph.roots.get position) := by
    apply congrArg List.ofFn
    funext position
    exact walk_events graph guarded _ _ _
  change (List.ofFn fun position : Fin graph.roots.length =>
    (walkGhost graph (graph.roots.get position) [.inl position]
      (RootedPath.root position)).map event).flatten =
    graph.roots.flatMap (walkEvents graph)
  rw [mapped]
  exact congrArg List.flatten (List.ofFn_getElem_eq_map graph.roots (walkEvents graph))

theorem root_event_count_le (graph : DAG n) (forest : graph.FormulaForest) :
    (rootEvents graph).length ≤ 2 * graph.guardIncidences := by
  have counts := congrArg List.length (root_events graph forest.1)
  simp only [List.length_map] at counts
  rw [← counts]
  exact root_length_le graph forest

end Controller.Cost.ForestGuardVisits
