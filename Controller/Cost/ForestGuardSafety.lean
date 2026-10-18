module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestGuardSchedule

@[expose] public section

/-!
# Balanced guard schedules and natural counters

Every guard entry has its matching exit after the subtree visit. Natural
counters restore after a balanced schedule; every exit is positive. Prefix
bounds provide the representability condition used to avoid word wraparound.
These lemmas do not establish the generated-event incidence bound.
-/
namespace Controller.Cost.ForestGuardSafety

open Controller.Decoder Controller.Cost.ForestGuardSchedule

variable {n : ℕ}

inductive Balanced : List (GuardEvent n) → Prop where
  | empty : Balanced []
  | append {first second} : Balanced first → Balanced second → Balanced (first ++ second)
  | wrap (coordinate : Channel n) {body} : Balanced body →
      Balanced (.enter coordinate :: (body ++ [.leave coordinate]))

theorem balanced_labels (labels : List (Channel n)) (body : List (GuardEvent n))
    (inside : Balanced body) :
    Balanced (labels.map GuardEvent.enter ++ body ++ labels.reverse.map GuardEvent.leave) := by
  induction labels with
  | nil => simpa using inside
  | cons coordinate rest ih =>
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using Balanced.wrap coordinate ih

theorem balanced_flatMap (items : List α) (events : α → List (GuardEvent n))
    (each : ∀ item ∈ items, Balanced (events item)) : Balanced (items.flatMap events) := by
  induction items with
  | nil => exact .empty
  | cons item rest ih =>
      exact .append (each item (by simp)) (ih (fun later present => each later (by simp [present])))

theorem walk_balanced (graph : DAG n) (index : Fin graph.nodeCount) :
    Balanced (walkEvents graph index) := by
  have claim : ∀ rank : ℕ, ∀ current : Fin graph.nodeCount,
      current.val = rank → Balanced (walkEvents graph current) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro current value
      rw [walkEvents.eq_def]
      cases equation : graph.node current with
      | zero => exact .empty
      | input coordinate => exact .empty
      | liveAnd left right => exact .empty
      | disj children =>
          apply balanced_flatMap
          intro child membership
          exact ih child.val (by have earlier := graph.childIndex_lt current child; omega)
            (graph.childIndex current child) rfl
      | guard child labels =>
          apply balanced_labels
          exact ih child.val (by have earlier := graph.childIndex_lt current child; omega)
            (graph.childIndex current child) rfl
  exact claim index.val index rfl

theorem roots_balanced (graph : DAG n) : Balanced (rootEvents graph) := by
  exact balanced_flatMap graph.roots (walkEvents graph) (fun index _ => walk_balanced graph index)

def naturalStep (counters : GuardCounters n) : GuardEvent n → GuardCounters n
  | .enter coordinate => enterGuards counters [coordinate]
  | .leave coordinate => leaveGuards counters [coordinate]

def runNatural (counters : GuardCounters n) (events : List (GuardEvent n)) : GuardCounters n :=
  events.foldl naturalStep counters

@[simp] theorem runNatural_nil (counters : GuardCounters n) : runNatural counters [] = counters := rfl

@[simp] theorem runNatural_cons (counters : GuardCounters n) (event : GuardEvent n)
    (rest : List (GuardEvent n)) :
    runNatural counters (event :: rest) = runNatural (naturalStep counters event) rest := rfl

theorem runNatural_append (counters : GuardCounters n) (first second : List (GuardEvent n)) :
    runNatural counters (first ++ second) = runNatural (runNatural counters first) second := by
  simp only [runNatural, List.foldl_append]

/-- Each exit is checked at the counter state immediately before that event. -/
def Positive (counters : GuardCounters n) : List (GuardEvent n) → Prop
  | [] => True
  | event :: rest =>
      (match event with | .enter _ => True | .leave coordinate => 0 < counters coordinate) ∧
      Positive (naturalStep counters event) rest

theorem positive_append (counters : GuardCounters n) (first second : List (GuardEvent n)) :
    Positive counters (first ++ second) ↔
      Positive counters first ∧ Positive (runNatural counters first) second := by
  induction first generalizing counters with
  | nil => simp [Positive]
  | cons event rest ih => simp only [List.cons_append, Positive, runNatural_cons, ih, and_assoc]

/-- Natural counters restore and no decrement is applied to zero. -/
theorem balanced_restore_positive {events : List (GuardEvent n)} (balanced : Balanced events) :
    ∀ counters : GuardCounters n, runNatural counters events = counters ∧ Positive counters events := by
  induction balanced with
  | empty => intro counters; exact ⟨rfl, trivial⟩
  | append first second firstIH secondIH =>
      intro counters
      obtain ⟨firstRestores, firstPositive⟩ := firstIH counters
      obtain ⟨secondRestores, secondPositive⟩ := secondIH counters
      refine ⟨?_, (positive_append counters _ _).mpr ⟨firstPositive, ?_⟩⟩
      · rw [runNatural_append, firstRestores, secondRestores]
      · simpa only [firstRestores] using secondPositive
  | wrap coordinate inside ih =>
      intro counters
      obtain ⟨restores, positive⟩ := ih (enterGuards counters [coordinate])
      constructor
      · simp only [runNatural_cons, runNatural_nil, naturalStep, runNatural_append, restores]
        exact leave_enterGuards counters [coordinate]
      · simp only [Positive, naturalStep, true_and]
        apply (positive_append (enterGuards counters [coordinate]) _ _).mpr
        refine ⟨positive, ?_⟩
        simp [restores, Positive, enterGuards_count]

theorem naturalStep_le (counters : GuardCounters n) (event : GuardEvent n) (coordinate : Channel n) :
    naturalStep counters event coordinate ≤ counters coordinate + 1 := by
  cases event with
  | enter channel =>
      by_cases same : channel = coordinate
      · simp [naturalStep, enterGuards_count, List.count_cons, same]
      · simp [naturalStep, enterGuards_count, List.count_cons, same, Ne.symm same]
  | leave channel =>
      by_cases same : channel = coordinate
      · simp [naturalStep, leaveGuards_count, List.count_cons, same] <;> omega
      · simp [naturalStep, leaveGuards_count, List.count_cons, same, Ne.symm same]

/-- This prefix bound counts events, retaining repeated labels. -/
theorem runNatural_le (counters : GuardCounters n) (events : List (GuardEvent n))
    (coordinate : Channel n) :
    runNatural counters events coordinate ≤ counters coordinate + events.length := by
  induction events generalizing counters with
  | nil => simp
  | cons event rest ih =>
      have bound := ih (naturalStep counters event)
      have stepBound := naturalStep_le counters event coordinate
      simp only [runNatural_cons, List.length_cons]
      omega

/-- Every prefix from zero has room for an entry increment under this explicit
word-width condition. The global event bound is a separate theorem. -/
theorem zero_prefix_representable (events before after : List (GuardEvent n))
    (splitEquation : events = before ++ after) (fits : events.length + 1 < 2 ^ width)
    (coordinate : Channel n) : runNatural (fun _ => 0) before coordinate + 1 < 2 ^ width := by
  have bound := runNatural_le (fun _ => 0) before coordinate
  have lengths := congrArg List.length splitEquation
  simp only [List.length_append] at lengths
  omega

theorem root_exit_positive (graph : DAG n) : Positive (fun _ => 0) (rootEvents graph) :=
  (balanced_restore_positive (roots_balanced graph) (fun _ => 0)).2

theorem root_counters_restore (graph : DAG n) : runNatural (fun _ => 0) (rootEvents graph) = (fun _ => 0) :=
  (balanced_restore_positive (roots_balanced graph) (fun _ => 0)).1

end Controller.Cost.ForestGuardSafety
