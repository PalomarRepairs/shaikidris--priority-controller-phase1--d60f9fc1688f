module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroSource

@[expose] public section

/-! The fetched source constructor, Horn backend, projection and reset execute with linear counted-source bounds. -/
namespace Controller.Cost.SharedZeroQuery
open Controller.Cost.GateProgram Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Decoder Controller.Decoder.DAG

theorem execution (graph : DAG n) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (root : Fin graph.nodeCount) (base slot : Nat)
    (program : Program width 8) (initial : State width 8) (sourceHeap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) initial.heap.size)
    (sourceEnd sourceEntry : Nat) (rest : List (Word width)) (dispatchEntry nextEntry : Nat)
    (plan : SourceQueryPlan (channels := n) program initial layout
      (SharedZeroSource.references graph b target T F base slot root) sourceEnd graph.nodeCount sourceEntry
      rest (by omega) dispatchEntry nextEntry)
    (ready : QueryReady (ambient := n + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase
      sourceEntry rest initial) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program initial final ticks peak ∧
      final.pc = word width dispatchEntry ∧ final.halted = false ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      ticks ≤ 4711 * (graph.countedSize + 1) ∧
      peak ≤ initial.liveWords + 186 * (graph.countedSize + 1) ∧
      final.liveWords ≤ initial.liveWords + 1 + (if answer then n else 0) ∧
      (answer = true ↔ Controller.CNF.Satisfiable
        (constructorFormula initial.heap layout (ForestZeroCompile.empty _)
          (ForestZeroCompile.empty_coherent _) (SharedZeroSource.references graph b target T F base slot root)
          n (by omega))) ∧
      (answer = true → QueryChannelWitness initial.heap layout
        (SharedZeroSource.references graph b target T F base slot root) n (by omega) final.output) ∧
      (answer = false → QueryReady (ambient := n + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase
        nextEntry rest (ForestZeroRootLoop.dispatchState final dispatchEntry nextEntry false)) := by
  obtain ⟨answer, final, ticks, peak, trace, finalPC, running, decision, timeBound, spaceBound, live,
    meaning, witness, reset, dispatchCapacity, dispatchAt⟩ := SourceQueryPlan.execute program initial sourceHeap
      layout (SharedZeroSource.references graph b target T F base slot root) sourceEnd graph.nodeCount sourceEntry
      rest (by omega) dispatchEntry nextEntry plan ready
  have occurrences := SharedZeroSource.occurrence_bound (base := base) (slot := slot) graph b target T F root
  have graphSize := graph.countedSize_eq
  refine ⟨answer, final, ticks, peak, trace, finalPC, running, decision, ?_, ?_, live, meaning, witness, reset⟩
  · split_ifs at timeBound <;> omega
  · omega

end Controller.Cost.SharedZeroQuery
