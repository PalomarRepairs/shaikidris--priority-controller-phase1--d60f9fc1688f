module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorExecution
public import Controller.Cost.ForestCursorSemantics

@[expose] public section

/-!
# Operational source-rooted forest cursor

The source-derived instruction blocks compose record reads, positional stack
navigation, guard-counter updates and the production leaf selector. Persistent
source/route cells are rebased on each intermediate heap. Word representability,
code coverage and mutable-region disjointness are explicit caller invariants.
-/
namespace Controller.Cost.ForestCursorRun

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorExecution

/-- A guard store preserves the two disjoint selector metadata cells. -/
theorem metadata_counter_store (heap : Array (Word width)) (layout : SelectorLayout n)
    (selected : Option ℕ) (channel : Channel n) (value : Word width)
    (valid : layout.counterOffset + channel.val < heap.size)
    (metadata : SelectorStored heap layout selected) :
    SelectorStored (heap.set (layout.counterOffset + channel.val) value valid) layout selected := by
  have notFound : layout.counterOffset + channel.val ≠ layout.found := by
    have outside := layout.foundOutside
    have bounded := channel.isLt
    unfold ForestGuardRestore.Outside at outside
    omega
  have notBest : layout.counterOffset + channel.val ≠ layout.best := by
    have outside := layout.bestOutside
    have bounded := channel.isLt
    unfold ForestGuardRestore.Outside at outside
    omega
  refine ⟨by simpa using metadata.foundValid, by simpa using metadata.bestValid, ?_, ?_⟩
  · rw [Array.getElem_set_ne valid metadata.foundValid notFound]
    exact metadata.foundWord
  · intro pointer equal
    rw [Array.getElem_set_ne valid metadata.bestValid notBest]
    exact metadata.bestWord pointer equal

/-- A complete source guard-entry block reads its actual label position and
executes the indexed increment, retaining selector and persistent metadata. -/
theorem source_enter_execution (program : Program width 4) (graph : DAG n)
    (initial heap : Array (Word width))
    (initialRecords : GraphRecords width initial graph)
    (initialRoutes : RouteDescriptors width initial)
    (layout : SelectorLayout n) (readonly : ReadonlyLayout graph initialRecords initialRoutes layout)
    (frame : PersistentFrame graph initialRecords initialRoutes heap)
    (records : GraphRecords width heap graph) (index : OccurrenceIndex graph)
    (node : Fin graph.nodeCount) (position : Fin (graph.node node).guardLabels.length)
    (channel target : Channel n) (channelEq : (graph.node node).guardLabels.get position = channel)
    (base b : ℕ) (counters : GuardCounters n) (selected : Option ℕ)
    (address loaded temporary : Word width) (stack output : List (Word width))
    (stored : CountersStored heap layout.counterOffset counters)
    (metadata : SelectorStored heap layout selected)
    (counterFits : layout.counterOffset + channel.val < 2 ^ width)
    (recordFits : records.guardBase node + position.val < 2 ^ width)
    (countFits : counters channel + 1 < 2 ^ width)
    (fits : base + 7 < 2 ^ width)
    (block : BlockAt program base
      (operationCode graph records layout index base b target (.enter node.val position.val channel))) :
    Execution program ((counterState heap base address loaded temporary).frame stack output)
      ((counterState (heap.set (layout.counterOffset + channel.val)
        (word width (counters channel + 1)) (stored.valid channel)) (base + 7)
        (word width (layout.counterOffset + channel.val))
        (word width (counters channel + 1)) (word width 1)).frame stack output)
      7 (5 + heap.size + (stack.length + output.length)) ∧
    CountersStored (heap.set (layout.counterOffset + channel.val)
      (word width (counters channel + 1)) (stored.valid channel))
      layout.counterOffset (enterGuards counters [channel]) ∧
    SelectorStored (heap.set (layout.counterOffset + channel.val)
      (word width (counters channel + 1)) (stored.valid channel)) layout selected ∧
    PersistentFrame graph initialRecords initialRoutes
      (heap.set (layout.counterOffset + channel.val)
        (word width (counters channel + 1)) (stored.valid channel)) := by
  have readBlock := BlockAt.prefix program base _ _ block
  have entryBlock := BlockAt.suffix program base _ _ block
  have read := source_guard_execution program heap graph records node position base
    address loaded temporary (by omega) recordFits readBlock
  rw [channelEq] at read
  have entry := entry_execution program heap (base + 2) (layout.counterOffset + channel.val)
    (counters channel) (word width (records.guardBase node + position.val))
    (word width channel.val) temporary (by omega) counterFits (stored.valid channel)
    (stored.held channel) countFits (by simpa [operationCode, recordReadCode] using entryBlock)
  have combined := (read.frame stack output).append (entry.frame stack output)
  have updateEq : ForestGuardSchedule.update width layout.counterOffset heap
      (.enter channel) = heap.set (layout.counterOffset + channel.val)
        (word width (counters channel + 1)) (stored.valid channel) := by
    change (if valid : layout.counterOffset + channel.val < heap.size then
      heap.set (layout.counterOffset + channel.val)
        (word width ((ForestGuardSchedule.storedWord heap (layout.counterOffset + channel.val)).val +
          (word width 1).val)) valid else heap) = _
    rw [dite_eq_left (stored.valid channel),
      (ForestGuardSchedule.storedWord_eq heap _ (stored.valid channel)).trans (stored.held channel)]
    have countValue : (word width (counters channel)).val = counters channel := by
      exact Nat.mod_eq_of_lt (by omega)
    have oneValue : (word width 1).val = 1 := by exact Nat.mod_eq_of_lt (by omega)
    rw [countValue, oneValue]
  refine ⟨?_, countersStored_enter heap layout.counterOffset counters channel stored,
    metadata_counter_store heap layout selected channel _ (stored.valid channel) metadata, ?_⟩
  · simpa only [max_self, Nat.add_assoc] using combined
  · rw [← updateEq]
    exact frame_counter graph initialRecords initialRoutes layout readonly heap frame (.enter channel)

/-- A complete source guard-exit block reads its actual label position and
executes the positive indexed decrement, retaining selector and persistent metadata. -/
theorem source_leave_execution (program : Program width 4) (graph : DAG n)
    (initial heap : Array (Word width))
    (initialRecords : GraphRecords width initial graph)
    (initialRoutes : RouteDescriptors width initial)
    (layout : SelectorLayout n) (readonly : ReadonlyLayout graph initialRecords initialRoutes layout)
    (frame : PersistentFrame graph initialRecords initialRoutes heap)
    (records : GraphRecords width heap graph) (index : OccurrenceIndex graph)
    (node : Fin graph.nodeCount) (position : Fin (graph.node node).guardLabels.length)
    (channel target : Channel n) (channelEq : (graph.node node).guardLabels.get position = channel)
    (base b : ℕ) (counters : GuardCounters n) (selected : Option ℕ)
    (address loaded temporary : Word width) (stack output : List (Word width))
    (stored : CountersStored heap layout.counterOffset counters)
    (metadata : SelectorStored heap layout selected)
    (counterFits : layout.counterOffset + channel.val < 2 ^ width)
    (recordFits : records.guardBase node + position.val < 2 ^ width)
    (positive : 0 < counters channel) (countFits : counters channel < 2 ^ width)
    (fits : base + 7 < 2 ^ width)
    (block : BlockAt program base
      (operationCode graph records layout index base b target (.leave node.val position.val channel))) :
    Execution program ((counterState heap base address loaded temporary).frame stack output)
      ((counterState (heap.set (layout.counterOffset + channel.val)
        (word width (counters channel - 1)) (stored.valid channel)) (base + 7)
        (word width (layout.counterOffset + channel.val))
        (word width (counters channel - 1)) (word width (2 ^ width - 1))).frame stack output)
      7 (5 + heap.size + (stack.length + output.length)) ∧
    CountersStored (heap.set (layout.counterOffset + channel.val)
      (word width (counters channel - 1)) (stored.valid channel))
      layout.counterOffset (leaveGuards counters [channel]) ∧
    SelectorStored (heap.set (layout.counterOffset + channel.val)
      (word width (counters channel - 1)) (stored.valid channel)) layout selected ∧
    PersistentFrame graph initialRecords initialRoutes
      (heap.set (layout.counterOffset + channel.val)
        (word width (counters channel - 1)) (stored.valid channel)) := by
  have readBlock := BlockAt.prefix program base _ _ block
  have entryBlock := BlockAt.suffix program base _ _ block
  have read := source_guard_execution program heap graph records node position base
    address loaded temporary (by omega) recordFits readBlock
  rw [channelEq] at read
  have entry := exit_execution program heap (base + 2) (layout.counterOffset + channel.val)
    (counters channel) (word width (records.guardBase node + position.val))
    (word width channel.val) temporary (by omega) counterFits (stored.valid channel)
    (stored.held channel) positive countFits (by simpa [operationCode, recordReadCode] using entryBlock)
  have combined := (read.frame stack output).append (entry.frame stack output)
  have updateEq : ForestGuardSchedule.update width layout.counterOffset heap
      (.leave channel) = heap.set (layout.counterOffset + channel.val)
        (word width (counters channel - 1)) (stored.valid channel) := by
    change (if valid : layout.counterOffset + channel.val < heap.size then
      heap.set (layout.counterOffset + channel.val)
        (word width ((ForestGuardSchedule.storedWord heap (layout.counterOffset + channel.val)).val +
          (word width (2 ^ width - 1)).val)) valid else heap) = _
    rw [dite_eq_left (stored.valid channel),
      (ForestGuardSchedule.storedWord_eq heap _ (stored.valid channel)).trans (stored.held channel),
      exit_word width (counters channel) positive countFits]
  refine ⟨?_, countersStored_leave heap layout.counterOffset counters channel stored,
    metadata_counter_store heap layout selected channel _ (stored.valid channel) metadata, ?_⟩
  · simpa only [max_self, Nat.add_assoc] using combined
  · rw [← updateEq]
    exact frame_counter graph initialRecords initialRoutes layout readonly heap frame (.leave channel)

/-- Source child navigation reads the represented child ID and pushes exactly
its stored child position onto the live caller stack. -/
theorem source_down_execution (program : Program width 4) (graph : DAG n)
    (heap : Array (Word width)) (records : GraphRecords width heap graph)
    (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (node : Fin graph.nodeCount) (position : Fin (graph.node node).children.length)
    (base b : ℕ) (target : Channel n) (address loaded temporary : Word width)
    (stack output : List (Word width)) (fits : base + 4 < 2 ^ width)
    (recordFits : records.childBase node + position.val < 2 ^ width)
    (block : BlockAt program base (operationCode graph records layout index base b target
      (.down node.val position.val ((graph.node node).children.get position).val))) :
    Execution program ((counterState heap base address loaded temporary).frame stack output)
      (((counterState heap (base + 4) (word width position.val)
        (word width ((graph.node node).children.get position).val) temporary).frame
          [word width position.val] []).frame stack output)
      4 (6 + heap.size + (stack.length + output.length)) := by
  have readBlock := BlockAt.prefix program base _ _ block
  have downBlock := BlockAt.suffix program base _ _ block
  have read := source_child_execution program heap graph records node position base
    address loaded temporary (by omega) recordFits readBlock
  have down := down_execution program heap (base + 2) position.val
    (word width (records.childBase node + position.val))
    (word width ((graph.node node).children.get position).val) temporary (by omega)
    (by simpa [operationCode, recordReadCode] using downBlock)
  have combined := (read.frame stack output).append (down.frame stack output)
  convert combined using 1 <;> simp only [Nat.add_assoc] <;> omega

/-- The source up operation executes the actual stack pop, retaining the caller
frame below the current child position. -/
theorem source_up_execution (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address loaded temporary position : Word width)
    (stack output : List (Word width)) (fits : base + 1 < 2 ^ width)
    (block : BlockAt program base (upCode (width := width))) :
    Execution program (((counterState heap base address loaded temporary).frame [position] []).frame stack output)
      ((counterState heap (base + 1) position loaded temporary).frame stack output)
      1 (6 + heap.size + (stack.length + output.length)) :=
  (up_execution program heap base address loaded temporary position fits block).frame stack output

/-- A complete source leaf block reads its actual input record and then runs the
physical production callback under the same persistent heap/navigation frame. -/
theorem source_leaf_execution (program : Program width 4) (graph : DAG n)
    (initial heap : Array (Word width))
    (initialRecords : GraphRecords width initial graph)
    (initialRoutes : RouteDescriptors width initial)
    (layout : SelectorLayout n) (readonly : ReadonlyLayout graph initialRecords initialRoutes layout)
    (frame : PersistentFrame graph initialRecords initialRoutes heap)
    (records : GraphRecords width heap graph) (routes : RouteDescriptors width heap)
    (index : OccurrenceIndex graph) (node : Fin graph.nodeCount)
    (head target : Channel n) (equation : graph.node node = .input head)
    (route : LeafRoute) (base b : ℕ) (counters : GuardCounters n) (selected : Option ℕ)
    (address loaded temporary : Word width) (stack output : List (Word width))
    (stored : CountersStored heap layout.counterOffset counters)
    (metadata : SelectorStored heap layout selected)
    (bounded : ∀ channel, counters channel < 2 ^ width)
    (oneFits : 1 < 2 ^ width)
    (counterFits : ∀ channel : Channel n, layout.counterOffset + channel.val < 2 ^ width)
    (bestFits : layout.best < 2 ^ width) (foundFits : layout.found < 2 ^ width)
    (recordFits : records.recordBase + 2 * node.val + 1 < 2 ^ width)
    (pointerRoute : routes.route (index.pointer route) = route)
    (fits : base + (operationCode graph records layout index base b target
      (.leaf node.val route head)).length < 2 ^ width)
    (block : BlockAt program base
      (operationCode graph records layout index base b target (.leaf node.val route head))) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks : ℕ,
      Execution program ((counterState heap base address loaded temporary).frame stack output)
        ((counterState (leafHeap width heap layout b target head counters selected (index.pointer route))
          (base + (operationCode graph records layout index base b target
            (.leaf node.val route head)).length)
          finalAddress finalLoaded finalTemporary).frame stack output)
        ticks (5 + heap.size + (stack.length + output.length)) ∧
      ticks ≤ 20 ∧
      CountersStored (leafHeap width heap layout b target head counters selected (index.pointer route))
        layout.counterOffset counters ∧
      SelectorStored (leafHeap width heap layout b target head counters selected (index.pointer route))
        layout (leafChoice b target head counters selected (index.pointer route)) ∧
      PersistentFrame graph initialRecords initialRoutes
        (leafHeap width heap layout b target head counters selected (index.pointer route)) ∧
      keepBestRoute b target 0 route head (counters, 0)
        ((selected.map routes.route).map fun path => (path, 0)) =
        ((leafChoice b target head counters selected (index.pointer route)).map routes.route).map
          (fun path => (path, 0)) := by
  have readBlock := BlockAt.prefix program base _ _ block
  have leafBlock := BlockAt.suffix program base _ _ block
  have read := record_read_execution program heap base _ address loaded temporary (word width head.val)
    (by simp only [operationCode, List.length_append, recordReadCode, List.length_cons,
      List.length_nil, leafCode_length] at fits; omega)
    recordFits (records.headValid node) (records.headWord node head equation) readBlock
  have coverage := leafCode_coverage program (base + 2) layout b target head (index.pointer route)
    (by simpa [operationCode, recordReadCode] using leafBlock)
  obtain ⟨fa, fl, ft, ticks, leaf, tickBound, countersHeld, selectedHeld, callback⟩ :=
    leaf_execution program heap layout routes (base + 2) b (index.pointer route) target head route
      counters selected (word width (records.recordBase + 2 * node.val + 1))
      (word width head.val) temporary stack output stored metadata bounded oneFits counterFits
      bestFits foundFits pointerRoute
      (by simp only [operationCode, List.length_append, recordReadCode, List.length_cons,
        List.length_nil, leafCode_length] at fits; omega)
      coverage.1 coverage.2
  have combined := (read.frame stack output).append leaf
  have footprint : (operationCode graph records layout index base b target
      (.leaf node.val route head)).length = 2 + 4 * (leafTests layout b target head).length + 6 := by
    simp only [operationCode, List.length_append, recordReadCode, List.length_cons,
      List.length_nil, leafCode_length]
    omega
  refine ⟨fa, fl, ft, 2 + ticks, ?_, by omega, countersHeld, selectedHeld,
    frame_leaf graph initialRecords initialRoutes layout readonly heap frame b target head
      counters selected (index.pointer route) metadata, callback⟩
  simpa only [footprint, max_self, Nat.add_assoc] using combined

end Controller.Cost.ForestCursorRun
