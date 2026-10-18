module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroMeaning

@[expose] public section

/-! The actual fetched zero query decides admissible fixed extensions that make the selected root false. -/
namespace Controller.Cost.SharedZeroChecked
open Controller.Cost.GateProgram Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Decoder Controller.Decoder.DAG

theorem execution (graph : DAG n) (guarded : graph.Guarded) (b : Nat) (target : Fin n) (T F : Finset (Fin n))
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
      (answer = true ↔ ∃ K, Admissible b target K ∧ ExtendsFixed T F K ∧
        graph.eval (assignmentOfSet K) root = false) ∧
      (answer = true → QueryChannelWitness initial.heap layout
        (SharedZeroSource.references graph b target T F base slot root) n (by omega) final.output) ∧
      (answer = false → QueryReady (ambient := n + graph.nodeCount) sourceHeap layout.tableBase layout.inverseBase
        nextEntry rest (ForestZeroRootLoop.dispatchState final dispatchEntry nextEntry false)) := by
  obtain ⟨answer, final, ticks, peak, trace, finalPC, running, decision, timeBound, spaceBound, live,
    meaning, witness, reset⟩ := SharedZeroQuery.execution graph b target T F root base slot program initial
      sourceHeap layout sourceEnd sourceEntry rest dispatchEntry nextEntry plan ready
  exact ⟨answer, final, ticks, peak, trace, finalPC, running, decision, timeBound, spaceBound, live,
    meaning.trans (SharedZeroMeaning.constructor_satisfiable_iff graph guarded b target T F root initial.heap layout),
    witness, reset⟩

end Controller.Cost.SharedZeroChecked
