module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootDirectory

@[expose] public section

namespace Controller.Cost.SharedRootResidentLoop
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestZeroDictionary Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.NativeSourceExecution Controller.Cost.SharedZeroResidentConditions

def Width (parameters : Parameters) (graph : DAG parameters.channels) (retained : Nat) :=
  SharedMachineCapacity.wordWidth retained graph.countedSize (selectedSize parameters).total

def Ready (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd entry : Nat)
    (program : Program (Width parameters graph retained) 8)
    (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (base : Nat)
    (roots : List (Fin graph.nodeCount)) : Prop :=
  ∃ currentRoot : Fin graph.nodeCount,
  ∃ sourceHeap : Array (Word (Width parameters graph retained)),
  ∃ layout : Layout (parameters.channels + graph.nodeCount) state.heap.size,
  SourceConditions parameters state layout
    (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot currentRoot)
    sourceEnd graph.nodeCount ∧
  QueryReady (ambient := parameters.channels + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase entry
    (word (Width parameters graph retained) base :: word (Width parameters graph retained) roots.length :: rest) state ∧
  state.heap.size ≤ retained ∧
  entry + 15 ≤ retained ∧
  roots.length ≤ graph.roots.length ∧
  slot < layout.tableBase ∧
  slot < sourceEnd ∧
  1 < slot ∧
  coordinateBase + (parameters.channels + graph.nodeCount) ≤ slot ∧
  SharedRootDirectory.Stored sourceHeap base roots ∧
  base + roots.length ≤ slot ∧
  SharedRootRead.BlockAt program entry
    (SharedRootLoopCode.code parameters graph T F state.heap layout coordinateBase slot entry currentRoot)

open Controller.Cost.SharedZeroNativeQuery

/-- The emitted native prefix is tied to the source formula of the successful root query. -/
def Witness (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (coordinateBase slot : Nat)
    (root : Fin graph.nodeCount) (observed : List (Word width)) : Prop :=
  ∃ heap : Array (Word width), ∃ layout : Layout (parameters.channels + graph.nodeCount) heap.size,
    QueryNativeWitness parameters heap layout
      (SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root)
      (by omega) observed

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem step (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd entry : Nat)
    (program : Program (Width parameters graph retained) 8)
    (rest : List (Word (Width parameters graph retained)))
    (state : State (Width parameters graph retained) 8) (base : Nat)
    (root : Fin graph.nodeCount) (roots : List (Fin graph.nodeCount))
    (ready : Ready parameters graph T F retained coordinateBase slot sourceEnd entry program rest state base (root :: roots)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = answer ∧
      ticks ≤ 5015 * (graph.countedSize + 1) + (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ state.liveWords + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true ↔ ∃ K, Admissible parameters.buses parameters.bridge.target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) ∧
      (answer = true → Witness parameters graph T F coordinateBase slot root final.output) ∧
      (answer = false → Nonempty (Ready parameters graph T F retained coordinateBase slot sourceEnd entry
        program rest final (base + 1) roots)) ∧
      final.liveWords ≤ state.liveWords + 1 + (if answer then (compile parameters).toState.count else 0) := by
  rcases ready with ⟨currentRoot, sourceHeap, layout, sourceData, query, heapBound, entryBound, countBound, slotBefore, slotBound, headerBefore, tableBefore, directory, directoryBefore, present⟩
  have actualDirectory := SharedRootDirectory.ready_stored sourceHeap state layout.tableBase
    layout.inverseBase entry base _ (root :: roots) query directory
    (by have := directoryBefore; have := slotBefore; omega)
  have stored := SharedRootDirectory.head state.heap base root roots actualDirectory
  have valid := SharedRootDirectory.source_valid state.heap base root roots actualDirectory
  obtain ⟨answer, final, ticks, peak, trace, halted, time, memory, meaning, witness, failed, source, liveBound⟩ :=
    SharedRootIteration.execution parameters graph guarded T F currentRoot root program state
      sourceHeap layout coordinateBase slot sourceEnd entry
      (SharedRootLoopCode.exhausted parameters graph T F state.heap layout coordinateBase slot entry currentRoot)
      base roots.length rest sourceData (by simpa only [Width, List.length_cons, Nat.add_comm] using query) heapBound entryBound
      (by simpa using countBound) valid slotBefore slotBound headerBefore tableBefore stored
      (SharedRootLoopCode.body_at parameters graph T F state.heap layout coordinateBase slot entry currentRoot program present)
  refine ⟨answer, final, ticks, peak, trace, halted, time, memory, meaning, (fun success => ⟨state.heap, layout, witness success⟩), ?_, liveBound⟩
  intro negative
  obtain ⟨sameSize, nextSource⟩ := source negative
  let nextLayout := SharedQuerySourceFrame.layout state final layout sameSize
  have nextQuery := failed negative
  have sourceValid : slot < sourceHeap.size := by
    have := query.sourceFrame.1
    have := query.sourceFrame.2.1
    omega
  let nextHeap := sourceHeap.set slot (word (Width parameters graph retained) root.val) sourceValid
  have nextDirectory := SharedRootDirectory.root_update sourceHeap base slot (root :: roots)
    (word (Width parameters graph retained) root.val) sourceValid directory directoryBefore
  have codeEq := SharedRootLoopCode.shared parameters graph T F state.heap final.heap layout nextLayout
    coordinateBase slot entry currentRoot root sameSize.symm rfl
  refine ⟨⟨root, nextHeap, nextLayout, nextSource, nextQuery, ?_, entryBound, ?_, slotBefore,
    slotBound, headerBefore, tableBefore, SharedRootDirectory.tail _ base root roots nextDirectory, ?_, ?_⟩⟩
  · exact sameSize.le.trans heapBound
  · simp only [List.length_cons] at countBound; omega
  · simp only [List.length_cons] at directoryBefore; omega
  · rw [← codeEq]; exact present



set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd entry : Nat)
    (program : Program (Width parameters graph retained) 8)
    (rest : List (Word (Width parameters graph retained)))
    (roots : List (Fin graph.nodeCount))
    (state : State (Width parameters graph retained) 8) (base : Nat)
    (ready : Ready parameters graph T F retained coordinateBase slot sourceEnd entry program rest state base roots) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = true ∧
      ticks ≤ roots.length * (5015 * (graph.countedSize + 1)) +
        (if answer then 55 * (selectedSize parameters).total else 0) + 5 ∧
      (answer = true ↔ ∃ root ∈ roots, ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
        ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) root = false) ∧
      peak ≤ state.liveWords + roots.length + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true → ∃ root ∈ roots, Witness parameters graph T F coordinateBase slot root final.output) := by
  induction roots generalizing state base with
  | nil =>
    rcases ready with ⟨currentRoot, sourceHeap, layout, sourceData, query, heapBound, entryBound,
      countBound, slotBefore, slotBound, headerBefore, tableBefore, directory, directoryBefore, present⟩
    obtain ⟨final, trace, halted, zero, heap, stack, output⟩ :=
      SharedRootLoopCode.empty_execution parameters graph T F program state sourceHeap layout coordinateBase slot entry
        base currentRoot rest (by simpa only [Width, List.length_nil] using query) (by omega) present
    refine ⟨false, final, 5, state.liveWords, trace, halted, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp only [List.length_nil]; omega
    · simp
  | cons root roots ih =>
    obtain ⟨answer, middle, ticks, peak, trace, halted, time, memory, meaning, certificate, failed, liveBound⟩ :=
      step parameters graph guarded T F retained coordinateBase slot sourceEnd entry program rest state base root roots ready
    cases answer with
    | true =>
      refine ⟨true, middle, ticks, peak, trace, halted, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons, ↓reduceIte, Nat.add_mul, Nat.one_mul]
        simp only [↓reduceIte] at time
        omega
      · constructor
        · intro _
          exact ⟨root, List.mem_cons_self, meaning.mp rfl⟩
        · intro _; rfl
      · simp only [List.length_cons]; omega
      · intro success
        exact ⟨root, List.mem_cons_self, certificate success⟩
    | false =>
      obtain ⟨nextReady⟩ := failed rfl
      obtain ⟨result, final, nextTicks, nextPeak, nextTrace, finalHalted, nextTime, nextMeaning, nextMemory, nextCertificate⟩ :=
        ih middle (base + 1) nextReady
      refine ⟨result, final, ticks + nextTicks, max peak nextPeak, trace.append nextTrace, finalHalted, ?_, ?_, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at time
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · constructor
        · intro yes
          obtain ⟨next, member, K, admissible, fixed, zero⟩ := nextMeaning.mp yes
          exact ⟨next, List.mem_cons_of_mem root member, K, admissible, fixed, zero⟩
        · rintro ⟨next, member, K, admissible, fixed, zero⟩
          rcases List.mem_cons.mp member with same | tail
          · subst next
            have impossible := meaning.mpr ⟨K, admissible, fixed, zero⟩
            contradiction
          · exact nextMeaning.mpr ⟨next, tail, K, admissible, fixed, zero⟩
      · simp only [List.length_cons]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at liveBound
        apply max_le <;> omega
      · intro success
        obtain ⟨next, member, witness⟩ := nextCertificate success
        exact ⟨next, List.mem_cons_of_mem root member, witness⟩


theorem Witness.checked (parameters : Parameters) (raw : parameters.layout = .raw)
    (drive : parameters.drive = true) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (coordinateBase slot : Nat) (root : Fin graph.nodeCount)
    (observed : List (Word width)) (fits : 1 < 2 ^ width)
    (observation : Fin parameters.decoder.roots.length)
    (observationEq : ∀ K, parameters.observations observation (assignmentOfSet K) = graph.eval (assignmentOfSet K) root)
    (healthy : graph.eval (assignmentOfSet {parameters.bridge.target}) root = true)
    (witness : Witness parameters graph T F coordinateBase slot root observed) :
    Certificate.ModelCheck.check (formula parameters)
      (NativeRealizedChecked.decodeOutput observed (compile parameters).toState.count) = true := by
  obtain ⟨heap, layout, native⟩ := witness
  exact native_witness_checked parameters raw drive graph guarded T F root heap layout coordinateBase slot observed
    fits observation observationEq healthy native

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem checked_execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (drive : parameters.drive = true) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels)) (retained coordinateBase slot sourceEnd entry : Nat)
    (program : Program (Width parameters graph retained) 8)
    (rest : List (Word (Width parameters graph retained))) (roots : List (Fin graph.nodeCount))
    (observations : ∀ root ∈ roots, Fin parameters.decoder.roots.length)
    (observationEq : ∀ root (member : root ∈ roots) K,
      parameters.observations (observations root member) (assignmentOfSet K) = graph.eval (assignmentOfSet K) root)
    (healthy : ∀ root ∈ roots, graph.eval (assignmentOfSet {parameters.bridge.target}) root = true)
    (state : State (Width parameters graph retained) 8) (base : Nat)
    (ready : Ready parameters graph T F retained coordinateBase slot sourceEnd entry program rest state base roots) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = true ∧
      ticks ≤ roots.length * (5015 * (graph.countedSize + 1)) +
        (if answer then 55 * (selectedSize parameters).total else 0) + 5 ∧
      peak ≤ state.liveWords + roots.length + 200 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true ↔ ∃ root ∈ roots, ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
        ExtendsFixed T F K ∧ graph.eval (assignmentOfSet K) root = false) ∧
      (answer = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  obtain ⟨answer, final, ticks, peak, trace, halted, time, meaning, memory, certificates⟩ :=
    execution parameters graph guarded T F retained coordinateBase slot sourceEnd entry program rest roots state base ready
  refine ⟨answer, final, ticks, peak, trace, halted, time, memory, meaning, ?_⟩
  intro success
  obtain ⟨root, member, witness⟩ := certificates success
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  apply Witness.checked parameters raw drive graph guarded T F coordinateBase slot root final.output
    (by unfold Width; omega) (observations root member) (observationEq root member) (healthy root member) witness

end Controller.Cost.SharedRootResidentLoop
