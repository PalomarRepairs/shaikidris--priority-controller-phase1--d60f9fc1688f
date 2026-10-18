module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestGuardSafety
public import Controller.Cost.ForestGuardVisits

@[expose] public section

/-!
# Natural counters refined by executed guard schedules

The initial indexed counter layout, positive exits and word-width bounds are
explicit. The schedule is a guard-only program component; graph navigation,
selector arithmetic and event compilation are not charged by these lemmas.
-/
namespace Controller.Cost.ForestGuardRefinement

open Controller.Decoder Controller.Cost.ForestCounter Controller.Cost.GateProgram
open Controller.Cost.ForestGuardSchedule Controller.Cost.ForestGuardSafety
open Controller.Cost.ForestGuardVisits

variable {n : ℕ}

/-- Every natural operation has its positive-exit and no-wrap side condition. -/
def Safe (width : ℕ) (counters : GuardCounters n) : List (GuardEvent n) → Prop
  | [] => True
  | event :: rest =>
      (match event with
        | .enter coordinate => counters coordinate + 1 < 2 ^ width
        | .leave coordinate => 0 < counters coordinate ∧ counters coordinate < 2 ^ width) ∧
      Safe width (naturalStep counters event) rest

theorem safe_of_positive_bound (width : ℕ) (counters : GuardCounters n)
    (events : List (GuardEvent n)) (positive : Positive counters events)
    (bound : ∀ coordinate, counters coordinate + events.length + 1 < 2 ^ width) :
    Safe width counters events := by
  induction events generalizing counters with
  | nil => trivial
  | cons event rest ih =>
      refine ⟨?_, ?_⟩
      · cases event with
        | enter coordinate => have room := bound coordinate; simp only [List.length_cons] at room; omega
        | leave coordinate =>
            refine ⟨positive.1, ?_⟩
            have room := bound coordinate
            omega
      · apply ih (naturalStep counters event) positive.2
        intro coordinate
        have stepBound := naturalStep_le counters event coordinate
        have room := bound coordinate
        simp only [List.length_cons] at room
        omega

theorem root_safe (width : ℕ) (graph : DAG n) (forest : graph.FormulaForest)
    (counterFits : 2 * graph.guardIncidences + 1 < 2 ^ width) :
    Safe width (fun _ => 0) (rootEvents graph) := by
  apply safe_of_positive_bound width _ _ (root_exit_positive graph)
  intro coordinate
  have count := root_event_count_le graph forest
  omega

/-- One actual word store refines its natural entry/exit counter operation. -/
theorem update_stored (width offset : ℕ) (heap : Array (Word width))
    (counters : GuardCounters n) (event : GuardEvent n)
    (stored : CountersStored heap offset counters)
    (condition : match event with
      | .enter coordinate => counters coordinate + 1 < 2 ^ width
      | .leave coordinate => 0 < counters coordinate ∧ counters coordinate < 2 ^ width) :
    CountersStored (update width offset heap event) offset (naturalStep counters event) := by
  cases event with
  | enter coordinate =>
      have lookup : storedWord heap (offset + coordinate.val) = word width (counters coordinate) :=
        (storedWord_eq heap _ (stored.valid coordinate)).trans (stored.held coordinate)
      have count : (word width (counters coordinate)).val = counters coordinate := by
        change counters coordinate % (2 ^ width) = counters coordinate
        exact Nat.mod_eq_of_lt (by omega)
      have one : (word width 1).val = 1 := by
        change 1 % (2 ^ width) = 1
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [update, GuardEvent.channel, GuardEvent.delta, dite_eq_left (stored.valid coordinate),
        lookup, count, one, naturalStep] using countersStored_enter heap offset counters coordinate stored
  | leave coordinate =>
      have lookup : storedWord heap (offset + coordinate.val) = word width (counters coordinate) :=
        (storedWord_eq heap _ (stored.valid coordinate)).trans (stored.held coordinate)
      simpa only [update, GuardEvent.channel, GuardEvent.delta, dite_eq_left (stored.valid coordinate),
        lookup, exit_word width (counters coordinate) condition.1 condition.2, naturalStep] using
        countersStored_leave heap offset counters coordinate stored

def finalHeap (width offset : ℕ) (heap : Array (Word width)) (events : List (GuardEvent n)) :
    Array (Word width) := events.foldl (update width offset) heap

theorem finalHeap_stored (width offset : ℕ) (heap : Array (Word width))
    (counters : GuardCounters n) (events : List (GuardEvent n))
    (stored : CountersStored heap offset counters) (safe : Safe width counters events) :
    CountersStored (finalHeap width offset heap events) offset (runNatural counters events) := by
  induction events generalizing heap counters with
  | nil => exact stored
  | cons event rest ih =>
      exact ih (update width offset heap event) (naturalStep counters event)
        (update_stored width offset heap counters event stored safe.1) safe.2

theorem finalState_heap (width offset base : ℕ) (heap : Array (Word width))
    (oldAddress oldCounter oldIncrement : Word width) (events : List (GuardEvent n)) :
    (finalState width offset base heap oldAddress oldCounter oldIncrement events).heap =
      finalHeap width offset heap events := by
  induction events generalizing base heap oldAddress oldCounter oldIncrement with
  | nil => rfl
  | cons event rest ih => exact ih _ _ _ _ _

/-- The actual guard-only schedule has linear guard ticks and restores the
represented zero counters. Runtime construction and other operations are separate. -/
theorem root_execution (program : Program width 4) (graph : DAG n)
    (forest : graph.FormulaForest) (offset base : ℕ) (heap : Array (Word width))
    (oldAddress oldCounter oldIncrement : Word width) (stack output : List (Word width))
    (stored : CountersStored heap offset (fun _ : Channel n => 0))
    (heapFits : heap.size ≤ 2 ^ width)
    (counterFits : 2 * graph.guardIncidences + 1 < 2 ^ width)
    (programFits : base + 5 * (rootEvents graph).length < 2 ^ width)
    (block : BlockAt program base (code width offset (rootEvents graph))) :
    Execution program ((counterState heap base oldAddress oldCounter oldIncrement).frame stack output)
      ((finalState width offset base heap oldAddress oldCounter oldIncrement (rootEvents graph)).frame stack output)
      (5 * (rootEvents graph).length) (5 + heap.size + stack.length + output.length) ∧
    5 * (rootEvents graph).length ≤ 10 * graph.guardIncidences ∧
    CountersStored (finalState width offset base heap oldAddress oldCounter oldIncrement
      (rootEvents graph)).heap offset (fun _ : Channel n => 0) := by
  have valid := valid_of_addresses width offset heap (rootEvents graph) heapFits
    (fun event _ => stored.valid event.channel)
  refine ⟨execution program offset base heap oldAddress oldCounter oldIncrement
    (rootEvents graph) stack output programFits valid block, ?_, ?_⟩
  · have count := root_event_count_le graph forest
    omega
  · rw [finalState_heap]
    have refined := finalHeap_stored width offset heap (fun _ : Channel n => 0)
      (rootEvents graph) stored (root_safe width graph forest counterFits)
    simpa only [root_counters_restore] using refined

end Controller.Cost.ForestGuardRefinement
