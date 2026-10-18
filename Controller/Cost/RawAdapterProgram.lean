module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RawDependencyOrder
public import Controller.Cost.SparseConeReuse
public import Controller.Horn.WorklistAccept
public import Controller.Cost.Initialize
public import Controller.Cost.InputLoad
public import Controller.Cost.ForestZeroCallerWiden

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The raw adapter separates the input-word address domain from retained source
storage. Bounds markers occupy the entire input-word domain; source words are
stored beyond it, so malformed references cannot read source data as markers. -/
namespace Controller.Cost.RawAdapterProgram
open Controller.Cost Controller.Decoder Controller.Horn.Worklist
open Controller.Horn.WorklistSeedRun Controller.Horn.WorklistSeed
open Controller.Horn.WorklistMark Controller.Horn.WorklistBucketReady
variable {width n channels : Nat}

/-- The complete input-word domain, followed by the retained original packet. -/
def markerHeap (domain bound : Nat) (source : Array (Word width)) : Array (Word width) :=
  (Array.ofFn fun position : Fin domain =>
    if position.val < bound then word width 1 else word width 0) ++ source

@[simp] theorem markerHeap_size (domain bound : Nat) (source : Array (Word width)) :
    (markerHeap domain bound source).size = domain + source.size := by
  simp only [markerHeap, Array.size_append, Array.size_ofFn]

/-- Every input word has a safe lookup, independently of source payload values. -/
theorem marker_lookup (domain bound reference : Nat) (source : Array (Word width))
    (inside : reference < domain) :
    (markerHeap domain bound source)[reference]? =
      some (if reference < bound then word width 1 else word width 0) := by
  rw [markerHeap, Array.getElem?_append_left (by simpa using inside)]
  rw [Array.getElem?_eq_getElem (by simpa using inside)]
  simp only [Array.getElem_ofFn]

def probeCode (width accepted : Nat) : Program width 8 :=
  #[.load 0 5, .xor 0 0 3, .branchZero 0 (word width accepted)]

@[simp] theorem probeCode_size (width accepted : Nat) :
    (probeCode width accepted).size = 3 := rfl

private theorem fetched (program : Program width 8) (state : State width 8)
    (address : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width address) (fits : address < 2 ^ width)
    (physical : program[address]? = some instruction) :
    programStep program state = step instruction state := by
  simp only [programStep, position, word, Nat.mod_eq_of_lt fits, physical]
  rfl

/-- A safe marker read and xor classify every represented reference. The invalid
branch falls through to a fetched reject block; it does not fault on a load. -/
theorem probe_execution (program : Program width 8) (entry accepted domain bound reference : Nat)
    (source : Array (Word width)) (state : State width 8)
    (physical : ∀ position : Fin 3,
      program[entry + position.val]? = (probeCode width accepted)[position.val]?)
    (heap : state.heap = markerHeap domain bound source)
    (input : reference < domain) (domainFits : domain ≤ 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (referenceHeld : state.reg 5 = word width reference) (one : state.reg 3 = word width 1)
    (codeFits : entry + 3 < 2 ^ width) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧
      final.pc = word width (if reference < bound then accepted else entry + 3) ∧
      final.reg 0 = word width (if reference < bound then 0 else 1) ∧
      (∀ register, register ≠ 0 → final.reg register = state.reg register) := by
  let loaded := state.advance.put 0 (if reference < bound then word width 1 else word width 0)
  let mixed := loaded.advance.put 0 (word width (if reference < bound then 0 else 1))
  let final := if reference < bound then { mixed with pc := word width accepted } else mixed.advance
  have referenceFits : reference < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have heapBound : reference < state.heap.size := by rw [heap, markerHeap_size]; omega
  have cell : state.heap[reference]'heapBound =
      if reference < bound then word width 1 else word width 0 := by
    have actual := marker_lookup domain bound reference source input
    rw [← heap, Array.getElem?_eq_getElem heapBound] at actual
    exact Option.some.inj actual
  have firstPC : loaded.pc = word width (entry + 1) := by
    simp [loaded, State.advance, State.put, position, word, Nat.mod_eq_of_lt (by omega : entry < 2 ^ width)]
  have secondPC : mixed.pc = word width (entry + 2) := by
    simp [mixed, State.advance, State.put, firstPC, word,
      Nat.mod_eq_of_lt (by omega : entry + 1 < 2 ^ width)]
  have first : programStep program state = some loaded := by
    rw [fetched program state entry (.load 0 5) position (by omega)
      (by simpa [probeCode] using physical ⟨0, by decide⟩)]
    simp [step, running, referenceHeld, word, Nat.mod_eq_of_lt referenceFits, heapBound, cell, loaded]
  have second : programStep program loaded = some mixed := by
    rw [fetched program loaded (entry + 1) (.xor 0 0 3) firstPC (by omega)
      (by simpa [probeCode] using physical ⟨1, by decide⟩)]
    by_cases valid : reference < bound <;>
      simp [step, loaded, mixed, State.advance, State.put, running, one, valid, word,
        Nat.mod_eq_of_lt oneFits]
  have third : programStep program mixed = some final := by
    rw [fetched program mixed (entry + 2) (.branchZero 0 (word width accepted)) secondPC (by omega)
      (by simpa [probeCode] using physical ⟨2, by decide⟩)]
    by_cases valid : reference < bound <;>
      simp [step, final, mixed, loaded, State.advance, State.put, running, valid, word,
        Nat.mod_eq_of_lt oneFits]
  have liveLoaded : loaded.liveWords = state.liveWords := rfl
  have liveMixed : mixed.liveWords = state.liveWords := rfl
  have liveFinal : final.liveWords = state.liveWords := by
    by_cases valid : reference < bound <;> simp [final, valid, State.liveWords, mixed, loaded, State.put, State.advance]
  have trace := Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl final)))
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [liveLoaded, liveMixed, liveFinal, Nat.max_self, Nat.reduceAdd] using trace
  · by_cases valid : reference < bound <;> simp [final, mixed, loaded, State.advance, State.put, valid]
  · by_cases valid : reference < bound <;> simp [final, mixed, loaded, State.advance, State.put, valid]
  · by_cases valid : reference < bound <;> simp [final, mixed, loaded, State.advance, State.put, valid]
  · by_cases valid : reference < bound <;> simp [final, mixed, loaded, State.advance, State.put, valid, running]
  · by_cases valid : reference < bound <;>
      simp [final, valid, State.advance, secondPC, word,
        Nat.mod_eq_of_lt (by omega : entry + 2 < 2 ^ width)]
  · by_cases valid : reference < bound <;> simp [final, mixed, loaded, State.advance, State.put, valid]
  · intro register different
    by_cases valid : reference < bound <;>
      simp [final, mixed, loaded, State.advance, State.put, valid, different]


def rejectCode (width tag : Nat) : Program width 8 :=
  #[.constant 0 (word width tag), .emit 0, .halt]

def checkedProbeCode (width accepted tag : Nat) : Program width 8 :=
  probeCode width accepted ++ rejectCode width tag

@[simp] theorem checkedProbeCode_size (width accepted tag : Nat) :
    (checkedProbeCode width accepted tag).size = 6 := rfl

/-- The actual invalid-reference branch emits its error tag and halts. -/
theorem checked_probe_execution (program : Program width 8)
    (entry accepted tag domain bound reference : Nat) (source : Array (Word width))
    (state : State width 8)
    (physical : ∀ position : Fin 6,
      program[entry + position.val]? = (checkedProbeCode width accepted tag)[position.val]?)
    (heap : state.heap = markerHeap domain bound source)
    (input : reference < domain) (domainFits : domain ≤ 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (referenceHeld : state.reg 5 = word width reference) (one : state.reg 3 = word width 1)
    (codeFits : entry + 6 < 2 ^ width) :
    (reference < bound ∧ ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width accepted ∧ final.halted = false) ∨
    (bound ≤ reference ∧ ∃ final, Execution program state final 6 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = word width tag :: state.output ∧ final.halted = true) := by
  have probeCells : ∀ index : Fin 3,
      program[entry + index.val]? = (probeCode width accepted)[index.val]? := by
    intro index
    have cell := physical ⟨index.val, by have := index.isLt; omega⟩
    rw [checkedProbeCode, Array.getElem?_append_left (by simpa using index.isLt)] at cell
    exact cell
  obtain ⟨classified, first, firstHeap, firstStack, firstOutput, firstRunning,
      firstPC, _, _⟩ := probe_execution program entry accepted domain bound reference source state
    probeCells heap input domainFits position running referenceHeld one (by omega)
  by_cases valid : reference < bound
  · exact Or.inl ⟨valid, classified, first, firstHeap, firstStack, firstOutput,
      by simpa only [ite_eq_left valid] using firstPC, firstRunning⟩
  · have invalid : bound ≤ reference := by omega
    have tagAt : program[entry + 3]? = some (.constant 0 (word width tag)) := by
      simpa [checkedProbeCode, probeCode, rejectCode] using physical ⟨3, by decide⟩
    have emitAt : program[entry + 3 + 1]? = some (.emit 0) := by
      simpa [checkedProbeCode, probeCode, rejectCode, Nat.add_assoc] using physical ⟨4, by decide⟩
    have haltAt : program[entry + 3 + 2]? = some .halt := by
      simpa [checkedProbeCode, probeCode, rejectCode, Nat.add_assoc] using physical ⟨5, by decide⟩
    obtain ⟨emitted, emission, emitHeap, emitStack, emitOutput, _, emitPC, emitRunning⟩ :=
      Controller.Horn.WorklistAccept.tag_execution program (entry + 3) tag classified tagAt emitAt
        (by simpa only [ite_eq_right valid] using firstPC) firstRunning (by omega)
    obtain ⟨final, terminal, finalHeap, finalStack, finalOutput, halted⟩ :=
      Controller.Horn.WorklistAccept.halt_execution program (entry + 3 + 2) emitted
        haltAt emitPC emitRunning (by omega)
    have classifiedLive : classified.liveWords = state.liveWords := by
      unfold State.liveWords
      rw [firstHeap, firstStack, firstOutput]
    have emittedLive : emitted.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [emitHeap, emitStack, emitOutput, firstHeap, firstStack, firstOutput]
      simp only [List.length_cons]
      omega
    refine Or.inr ⟨invalid, final, ?_, finalHeap.trans (emitHeap.trans firstHeap),
      finalStack.trans (emitStack.trans firstStack), ?_, halted⟩
    · have trace := (first.append emission).append terminal
      simpa only [classifiedLive, emittedLive, Nat.reduceAdd,
        show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega,
        Nat.max_self] using trace
    · rw [finalOutput, emitOutput, firstOutput]


theorem dependency_source_all (graph : UnorderedDAG n) :
    RawDependencyOrder.ClauseDependencies graph (RawDependencyOrder.dependencyClauses graph) := by
  intro index parent labels selected child incident
  have size : (RawDependencyOrder.dependencyClauses graph).length = graph.nodeCount := by
    simp only [RawDependencyOrder.dependencyClauses, List.length_ofFn]
  let original : Fin graph.nodeCount := ⟨index.val, by simpa only [size] using index.isLt⟩
  have originalRow : (RawDependencyOrder.dependencyClauses graph)[index.val] =
      RawDependencyOrder.dependencyClause original (graph.node original).children := by
    simp only [RawDependencyOrder.dependencyClauses, List.getElem_ofFn]
    rfl
  have noSelf : original ∉ (graph.node original).children := by
    intro self
    have tautological : Controller.Horn.Tautological
        (RawDependencyOrder.dependencyClause original (graph.node original).children) := by
      refine ⟨(original, false), ?_, ?_⟩
      · exact (RawDependencyOrder.dependency_false_mem original original _).mpr rfl
      · change (original, true) ∈ RawDependencyOrder.dependencyClause original (graph.node original).children
        exact (RawDependencyOrder.dependency_true_mem original original _).mpr self
    have check := (Controller.Horn.Worklist.tautologyCheck_eq_true _).mpr tautological
    rw [originalRow] at selected
    simp [Controller.Horn.Worklist.compileClause, check] at selected
  have compiled : Controller.Horn.Worklist.compileClause
      (RawDependencyOrder.dependencyClauses graph)[index.val] =
      .negative original (graph.node original).children.dedup := by
    rw [originalRow]
    exact RawDependencyOrder.compile_dependency original _ noSelf
  have same := compiled.symm.trans selected
  injection same with parentEq labelsEq
  have source : child ∈ (graph.node original).children := by simpa only [parentEq] using incident
  rw [← labelsEq]
  exact List.mem_dedup.mpr source


private theorem empty_seed_order (graph : UnorderedDAG n)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : RawDependencyOrder.ClauseDependencies graph clauses)
    (row : Fin clauses.length) (parent : Fin graph.nodeCount)
    (labels : List (Fin graph.nodeCount))
    (original : Controller.Horn.Worklist.compileClause clauses[row.val] = .negative parent labels)
    (empty : labels.length = 0) (queue : List (Fin graph.nodeCount))
    (ordered : RawDependencyOrder.DependencyOrder graph queue) :
    RawDependencyOrder.DependencyOrder graph (Controller.Horn.WorklistBucketReady.queueAfter queue parent) := by
  apply RawDependencyOrder.queue_after_order graph queue parent ordered
  intro child incident
  have member : child ∈ labels := source row parent labels original child incident
  have nil : labels = [] := List.length_eq_zero_iff.mp empty
  simp only [nil, List.not_mem_nil] at member


theorem ordered_seed_row (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (recordStart recordEnd base entry done conflict index : Nat) (queue : List (Fin graph.nodeCount))
    (fired : Fin clauses.length → Bool) (state : State width 8) (program : Program width 8)
    (dependencies : RawDependencyOrder.ClauseDependencies graph clauses)
    (ordered : RawDependencyOrder.DependencyOrder graph queue)
    (invariant : ScanInvariant clauses recordStart recordEnd base entry index queue fired state)
    (nonempty : index < clauses.length) (separated : base + 5 * graph.nodeCount + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistSeed.At (n := graph.nodeCount) program base entry done conflict)
    (capacity : entry + 47 < 2 ^ width) :
    ∃ nextQueue nextFired final ticks,
      queue.length ≤ nextQueue.length ∧ nextQueue.length ≤ graph.nodeCount ∧ ticks ≤ 36 + 3 * (nextQueue.length - queue.length) ∧
      Execution program state final ticks state.liveWords ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      ((final.pc = word width conflict ∧ final.halted = false ∧
        ¬ ∃ assignment : Fin graph.nodeCount → Bool, ∀ row : Fin clauses.length,
          (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
        ScanInvariant clauses recordStart recordEnd base entry (index + 1) nextQueue nextFired final ∧
        RawDependencyOrder.DependencyOrder graph nextQueue) := by
  by_cases positive : 0 < (Controller.Horn.Worklist.compileClause clauses[index]).positives.length
  · obtain ⟨final, trace, result, size, stack, output⟩ :=
      nonzero_row_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
        invariant nonempty positive present capacity
    exact ⟨queue, fired, final, 13, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, Or.inr ⟨result, ordered⟩⟩
  · have zeroCount : (Controller.Horn.Worklist.compileClause clauses[index]).positives.length = 0 := by omega
    cases original : Controller.Horn.Worklist.compileClause clauses[index] with
    | skip =>
      obtain ⟨final, trace, result, size, stack, output⟩ :=
        skip_row_execution clauses recordStart recordEnd base entry done conflict index queue fired state program
          invariant nonempty original present capacity
      exact ⟨queue, fired, final, 16, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, Or.inr ⟨result, ordered⟩⟩
    | positive labels =>
      have empty : labels.length = 0 := by simpa only [original, Controller.Horn.Worklist.Rule.positives] using zeroCount
      obtain ⟨final, trace, pc, live, size, stack, output, impossible⟩ :=
        positive_row_execution clauses recordStart recordEnd base entry done conflict index queue fired labels state program
          invariant nonempty original empty present capacity
      exact ⟨queue, fired, final, 17, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, Or.inl ⟨pc, live, impossible⟩⟩
    | negative head labels =>
      have empty : labels.length = 0 := by simpa only [original, Controller.Horn.Worklist.Rule.positives] using zeroCount
      obtain ⟨final, trace, result, size, stack, output⟩ :=
        negative_row_execution clauses recordStart recordEnd base entry done conflict index queue fired head labels state program
          invariant nonempty original empty separated present capacity
      refine ⟨queueAfter queue head,
        (fun other => if other = (⟨index, nonempty⟩ : Fin clauses.length) then true else fired other),
        final, (if head ∈ queue then 36 else 39), ?_, enqueue_bound _ result.fifo.nodup, ?_, trace, size, stack, output, Or.inr ⟨result,
        empty_seed_order graph clauses dependencies ⟨index, nonempty⟩ head labels original empty queue ordered⟩⟩
      · by_cases stale : head ∈ queue <;> simp [queueAfter, stale]
      · by_cases stale : head ∈ queue <;> simp [queueAfter, stale]


theorem ordered_seed_scan (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (dependencies : RawDependencyOrder.ClauseDependencies graph clauses)
    (recordStart recordEnd base entry done conflict : Nat) (program : Program width 8)
    (present : Controller.Horn.WorklistSeed.At (n := graph.nodeCount) program base entry done conflict)
    (separated : base + 5 * graph.nodeCount + 4 ≤ recordStart) (capacity : entry + 47 < 2 ^ width)
    (budget : Nat) :
    ∀ (index : Nat) (queue : List (Fin graph.nodeCount)) (fired : Fin clauses.length → Bool) (state : State width 8),
      index + budget = clauses.length →
      ScanInvariant clauses recordStart recordEnd base entry index queue fired state →
      RawDependencyOrder.DependencyOrder graph queue →
      ∃ nextQueue nextFired final ticks,
        queue.length ≤ nextQueue.length ∧ nextQueue.length ≤ graph.nodeCount ∧ ticks ≤ 36 * budget + 3 * (nextQueue.length - queue.length) + 4 ∧
        Execution program state final ticks state.liveWords ∧
        final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
        ((final.pc = word width conflict ∧ final.halted = false ∧
          ¬ ∃ assignment : Fin graph.nodeCount → Bool, ∀ row : Fin clauses.length,
            (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) ∨
          ScanInvariant clauses recordStart recordEnd base done clauses.length nextQueue nextFired final ∧
          RawDependencyOrder.DependencyOrder graph nextQueue) := by
  induction budget with
  | zero =>
    intro index queue fired state ledger invariant ordered
    have last : index = clauses.length := by omega
    subst index
    obtain ⟨final, trace, result, size, stack, output⟩ := terminal_execution clauses recordStart recordEnd base
      entry done conflict queue fired state program invariant present capacity
    exact ⟨queue, fired, final, 4, Nat.le_refl _, enqueue_bound queue invariant.fifo.nodup, by omega, trace, size, stack, output, Or.inr ⟨result, ordered⟩⟩
  | succ budget ih =>
    intro index queue fired state ledger invariant ordered
    obtain ⟨middleQueue, middleFired, middle, stepTicks, growth, middleBound, stepCost, stepTrace, size, stack, output, outcome⟩ :=
      ordered_seed_row graph clauses recordStart recordEnd base entry done conflict index queue fired state program
        dependencies ordered invariant
        (by omega) separated present capacity
    rcases outcome with conflictResult | ⟨continuing, middleOrder⟩
    · refine ⟨middleQueue, middleFired, middle, stepTicks, growth, middleBound, ?_, stepTrace, size, stack, output, Or.inl conflictResult⟩
      omega
    · obtain ⟨finalQueue, finalFired, final, restTicks, restGrowth, finalBound, restCost, restTrace,
          finalSize, finalStack, finalOutput, result⟩ :=
        ih (index + 1) middleQueue middleFired middle (by omega) continuing middleOrder
      have middleLive : middle.liveWords = state.liveWords := by unfold State.liveWords; rw [size, stack, output]
      refine ⟨finalQueue, finalFired, final, stepTicks + restTicks, Nat.le_trans growth restGrowth, finalBound,
        ?_, ?_, finalSize.trans size, finalStack.trans stack, finalOutput.trans output, result⟩
      · omega
      · simpa only [middleLive, Nat.max_self] using stepTrace.append restTrace


/-- The exact dependency encoding has an all-false model even on cyclic sources. -/
theorem dependency_false_model (graph : UnorderedDAG channels) :
    ∀ row : Fin (RawDependencyOrder.dependencyClauses graph).length,
      (compileClause (RawDependencyOrder.dependencyClauses graph)[row.val]).Holds (fun _ => false) := by
  intro row
  have size : (RawDependencyOrder.dependencyClauses graph).length = graph.nodeCount := by
    simp only [RawDependencyOrder.dependencyClauses, List.length_ofFn]
  let parent : Fin graph.nodeCount := ⟨row.val, by simpa only [size] using row.isLt⟩
  have sourceRow : (RawDependencyOrder.dependencyClauses graph)[row.val] =
      RawDependencyOrder.dependencyClause parent (graph.node parent).children := by
    simp only [RawDependencyOrder.dependencyClauses, List.getElem_ofFn]
    rfl
  rw [sourceRow]
  apply (compileClause_holds_iff _ (RawDependencyOrder.dependency_dual parent _) _).mpr
  exact ⟨(parent, false), (RawDependencyOrder.dependency_false_mem parent parent _).mpr rfl, rfl⟩


theorem dependency_dual_rows (graph : UnorderedDAG channels) :
    ∀ row : Fin (RawDependencyOrder.dependencyClauses graph).length,
      Controller.Horn.DualHornClause (RawDependencyOrder.dependencyClauses graph)[row.val] := by
  intro row
  have size : (RawDependencyOrder.dependencyClauses graph).length = graph.nodeCount := by
    simp only [RawDependencyOrder.dependencyClauses, List.length_ofFn]
  let parent : Fin graph.nodeCount := ⟨row.val, by simpa only [size] using row.isLt⟩
  have sourceRow : (RawDependencyOrder.dependencyClauses graph)[row.val] =
      RawDependencyOrder.dependencyClause parent (graph.node parent).children := by
    simp only [RawDependencyOrder.dependencyClauses, List.getElem_ofFn]
    rfl
  rw [sourceRow]
  exact RawDependencyOrder.dependency_dual parent _


private theorem encoded_dual (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph) :
    ∀ row : Fin clauses.length, Controller.Horn.DualHornClause clauses[row.val] := by
  cases source
  exact dependency_dual_rows graph

private theorem encoded_dependencies (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph) :
    RawDependencyOrder.ClauseDependencies graph clauses := by
  cases source
  exact dependency_source_all graph

private theorem encoded_false_model (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph) :
    ∀ row : Fin clauses.length, (compileClause clauses[row.val]).Holds (fun _ => false) := by
  cases source
  exact dependency_false_model graph

theorem ordered_cold_seed_execution (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (conflict : Nat) (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (codeFits : (program width clauses conflict).size < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ (recordEnd : Nat) (queue : List (Fin graph.nodeCount)) (fired : Fin clauses.length → Bool)
      (final : State width 8) (ticks peak : Nat),
      ColdSeedResult clauses conflict state suffix recordEnd queue fired final ticks peak ∧
      RawDependencyOrder.DependencyOrder graph queue := by
  have dual := encoded_dual graph clauses source
  have dependencies := encoded_dependencies graph clauses source
  have allFalse := encoded_false_model graph clauses source
  obtain ⟨indexed, recordEnd, coldTicks, coldPeak, coldTrace, physical, header, fifo, indexedPC,
      indexedRunning, indexedZero, indexedOne, indexedRoom, indexedStack, indexedOutput, coldCost, coldStorage⟩ :=
    cold_seed_input clauses state suffix emptyHeap input position running dual
      (by have size := program_size width clauses conflict; omega) heapFits
  have separated : Controller.Horn.SourceSerialize.base clauses + 5 * graph.nodeCount + 4 ≤
      Controller.Horn.IndexScanCold.recordStart width clauses := by
    simp [Controller.Horn.IndexScanCold.recordStart, Controller.Horn.NormalizeCold.words]
  have appendedCold : Execution (program width clauses conflict) state indexed coldTicks coldPeak := by
    have appended := Controller.Horn.IndexScanCold.append_execution
      (Controller.Horn.IndexScanCold.program width clauses)
      (coldSetupCode (n := graph.nodeCount) width (Controller.Horn.SourceSerialize.base clauses)
        (Controller.Horn.IndexScanCold.recordStart width clauses)
        ((Controller.Horn.IndexScanCold.program width clauses).size + 9) ++
       Controller.Horn.WorklistSeed.code (n := graph.nodeCount) width (Controller.Horn.SourceSerialize.base clauses)
        ((Controller.Horn.IndexScanCold.program width clauses).size + 9)
        ((Controller.Horn.IndexScanCold.program width clauses).size + 56) conflict) coldTrace
    simpa only [program, Array.append_assoc] using appended
  obtain ⟨started, setupTrace, initial, setupSize, setupStack, setupOutput⟩ :=
    initial_scan_execution clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses) (Controller.Horn.IndexScanCold.program width clauses).size
      ((Controller.Horn.IndexScanCold.program width clauses).size + 9) indexed (program width clauses conflict)
      physical header fifo separated (setup_at width clauses conflict) indexedPC indexedRunning
      indexedZero indexedOne indexedRoom (by have size := program_size width clauses conflict; omega)
  obtain ⟨queue, fired, final, seedTicks, _, queueBound, seedCost, seedTrace, _, seedStack, seedOutput, result⟩ :=
    ordered_seed_scan graph clauses dependencies (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 9)
      ((Controller.Horn.IndexScanCold.program width clauses).size + 56) conflict
      (program width clauses conflict) (scan_at width clauses conflict) separated
      (by have size := program_size width clauses conflict; omega) clauses.length 0 [] (fun _ => false) started (by omega) initial (RawDependencyOrder.empty_order graph)
  have startedLive : started.liveWords = indexed.liveWords := by unfold State.liveWords; rw [setupSize, setupStack, setupOutput]
  have indexedStorage := coldTrace.final_storage_le
  let full := (appendedCold.append setupTrace).append seedTrace
  have finalOrder : RawDependencyOrder.DependencyOrder graph queue := by
    rcases result with conflictResult | ⟨complete, ordered⟩
    · exact False.elim (conflictResult.2.2 ⟨fun _ => false, allFalse⟩)
    · exact ordered
  refine ⟨recordEnd, queue, fired, final, coldTicks + 9 + seedTicks,
    max (max coldPeak indexed.liveWords) started.liveWords, ?_, finalOrder⟩
  refine ⟨full,
    seedStack.trans (setupStack.trans indexedStack), seedOutput.trans (setupOutput.trans indexedOutput),
    queueBound, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_nil, Nat.sub_zero] at seedCost
    omega
  · rw [startedLive]
    omega
  · unfold programWords
    rw [program_size, Controller.Horn.IndexScanCold.program_size, startedLive]
    omega
  · rcases result with conflictResult | ⟨complete, ordered⟩
    · exact Or.inl conflictResult
    · right
      simpa only [program_size] using complete

private def markerNarrow (state : State width 8) : State width 4 :=
  { reg := fun register => state.reg (Controller.Cost.RegisterWiden.widenRegister register)
    heap := state.heap, stack := state.stack, output := state.output,
    pc := state.pc, halted := state.halted }

private theorem markerWidenNarrow (state : State width 8) :
    Controller.Cost.RegisterWiden.widenState (markerNarrow state) state.reg = state := by
  have registers : (Controller.Cost.RegisterWiden.widenState (markerNarrow state) state.reg).reg = state.reg := by
    funext register
    by_cases small : register.val < 4
    · change (if h : register.val < 4 then
        state.reg (Controller.Cost.RegisterWiden.widenRegister ⟨register.val, h⟩) else state.reg register) = state.reg register
      rw [dite_eq_left small]
      have same : Controller.Cost.RegisterWiden.widenRegister ⟨register.val, small⟩ = register := Fin.ext rfl
      rw [same]
    · simp only [Controller.Cost.RegisterWiden.widenState, dite_eq_right small]
  cases state
  simp only [Controller.Cost.RegisterWiden.widenState, markerNarrow] at registers ⊢
  congr 1

def markerInitLow (width domain bound : Nat) : Controller.Cost.GateProgram.Code width :=
  Controller.Cost.Initialize.code (word width 1) bound ++
    Controller.Cost.Initialize.code (word width 0) (domain - bound)

@[simp] theorem markerInitLow_length (width domain bound : Nat) (inside : bound ≤ domain) :
    (markerInitLow width domain bound).length = 2 * domain := by
  simp only [markerInitLow, List.length_append, Controller.Cost.Initialize.code_length]
  omega

private theorem markerHeap_prefix (domain bound : Nat) (inside : bound ≤ domain) :
    markerHeap (width := width) domain bound #[] =
      Array.replicate bound (word width 1) ++ Array.replicate (domain - bound) (word width 0) := by
  apply Array.ext
  · simp only [markerHeap_size, Array.size_append, Array.size_replicate, Array.size_empty]
    omega
  · intro index left right
    simp only [markerHeap, Array.append_empty, Array.getElem_ofFn, Array.getElem_append]
    by_cases valid : index < bound <;> simp [valid]

theorem marker_initialization_execution (program : Program width 8) (entry domain bound : Nat)
    (state : State width 8) (inside : bound ≤ domain)
    (empty : state.heap = #[]) (position : state.pc = word width entry)
    (running : state.halted = false) (codeFits : entry + 2 * domain < 2 ^ width)
    (room : domain ≤ 2 ^ width)
    (present : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt program entry
      (markerInitLow width domain bound)) :
    ∃ final, Execution program state final (2 * domain) (state.liveWords + domain) ∧
      final.heap = markerHeap domain bound #[] ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 2 * domain) ∧
      final.halted = false ∧ (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let low := markerNarrow state
  let view := Controller.Cost.ForestZeroCallerWiden.lowerProgram program
  have lowBlock := Controller.Cost.ForestZeroCallerWiden.lower_block program entry
    (markerInitLow width domain bound) present
  have oneBlock := Controller.Cost.GateProgram.BlockAt.prefix view entry
    (Controller.Cost.Initialize.code (word width 1) bound)
    (Controller.Cost.Initialize.code (word width 0) (domain - bound)) lowBlock
  have zeroBlock := Controller.Cost.GateProgram.BlockAt.suffix view entry
    (Controller.Cost.Initialize.code (word width 1) bound)
    (Controller.Cost.Initialize.code (word width 0) (domain - bound)) lowBlock
  obtain ⟨middle, first, firstHeap, firstStack, firstOutput, firstPC, firstRunning⟩ :=
    Controller.Cost.Initialize.code_execution view low (word width 1) entry bound position running
      (by omega) (by simpa only [low, markerNarrow, empty, Array.size_empty, List.length_nil, Nat.zero_add] using Nat.le_trans inside room) oneBlock
  have tailBlock : Controller.Cost.GateProgram.BlockAt view (entry + 2 * bound)
      (Controller.Cost.Initialize.code (word width 0) (domain - bound)) := by
    simpa only [Controller.Cost.Initialize.code_length] using zeroBlock
  obtain ⟨last, rest, lastHeap, lastStack, lastOutput, lastPC, lastRunning⟩ :=
    Controller.Cost.Initialize.code_execution view middle (word width 0) (entry + 2 * bound)
      (domain - bound) firstPC firstRunning (by omega)
      (by rw [firstHeap]; simp only [Array.size_append, List.size_toArray, List.length_replicate, low, markerNarrow, empty, Array.size_empty, List.length_nil, Nat.zero_add]; omega) tailBlock
  have middleLive : middle.liveWords = low.liveWords + bound := by
    unfold State.liveWords
    rw [firstHeap, firstStack, firstOutput]
    simp only [Array.size_append, List.size_toArray, List.length_replicate]
    omega
  have lowTrace : Execution view low last (2 * domain) (low.liveWords + domain) := by
    have trace := first.append rest
    rw [middleLive] at trace
    convert trace using 1 <;> omega
  have lifted := Controller.Cost.ForestZeroCallerWiden.execution program low last
    (2 * domain) (low.liveWords + domain) lowTrace lastRunning state.reg
  have sourceLive : low.liveWords + 4 = state.liveWords := by
    simp only [low, markerNarrow, State.liveWords]
    omega
  let final := Controller.Cost.RegisterWiden.widenState last state.reg
  refine ⟨final, ?_, ?_, lastStack.trans firstStack, lastOutput.trans firstOutput, ?_, lastRunning, ?_⟩
  · rw [markerWidenNarrow] at lifted
    simpa only [show low.liveWords + domain + 4 = state.liveWords + domain by omega] using lifted
  · change last.heap = markerHeap domain bound #[]
    rw [lastHeap, firstHeap]
    simp only [low, markerNarrow, empty, Array.empty_append, List.toArray_replicate]
    exact (markerHeap_prefix domain bound inside).symm
  · change last.pc = word width (entry + 2 * domain)
    convert lastPC using 1 <;> congr 1 <;> omega
  · intro register high
    exact Controller.Cost.RegisterWiden.widenState_high last state.reg register high

-- Physical consumer: original raw-source word loader and safe-marker slices.
def rawGuardLabels : Controller.Decoder.RawGate → List Nat
  | .guard _ labels => labels
  | _ => []

def rawInputSize (channels : Nat) (raw : Controller.Decoder.RawDAG) : Nat :=
  channels + raw.nodes.size +
    (raw.nodes.toList.map fun gate => gate.children.length).sum +
    (raw.nodes.toList.map fun gate => (rawGuardLabels gate).length).sum + raw.roots.length

def rawInputWidth (channels : Nat) (raw : Controller.Decoder.RawDAG) : Nat :=
  Nat.log 2 (rawInputSize channels raw + 1) + 3

theorem raw_input_capacity (channels : Nat) (raw : Controller.Decoder.RawDAG) :
    4 * (rawInputSize channels raw + 1) < 2 ^ rawInputWidth channels raw := by
  have basic := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (rawInputSize channels raw + 1)
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 4)
  have identity : 4 * 2 ^ (Nat.log 2 (rawInputSize channels raw + 1) + 1) =
      2 ^ rawInputWidth channels raw := by
    simp only [rawInputWidth, Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  simpa only [Nat.succ_eq_add_one, identity] using scaled

theorem raw_input_domain_linear (channels : Nat) (raw : Controller.Decoder.RawDAG) :
    2 ^ rawInputWidth channels raw ≤ 8 * (rawInputSize channels raw + 1) := by
  have power := Nat.pow_log_le_self 2 (by omega : rawInputSize channels raw + 1 ≠ 0)
  have scaled := Nat.mul_le_mul_left 8 power
  simpa only [rawInputWidth, Nat.pow_add, Nat.reducePow, Nat.mul_comm] using scaled

-- Source encoder image theorem: every valid original raw reference has exact
-- Word(rawInputWidth) value. Larger machine width carries that same value by
-- finite inclusion; no modulo loss and no assumed topological numbering.
theorem raw_reference_abi (channels : Nat) (raw : Controller.Decoder.RawDAG)
    (valid : raw.WellFormed channels) :
    (∀ node : Fin raw.nodes.size, ∀ child ∈ raw.nodes[node.val].children,
      child < 2 ^ rawInputWidth channels raw) ∧
    (∀ node : Fin raw.nodes.size, ∀ channel ∈ raw.nodes[node.val].channels,
      channel < 2 ^ rawInputWidth channels raw) ∧
    (∀ root ∈ raw.roots, root < 2 ^ rawInputWidth channels raw) := by
  have capacity := raw_input_capacity channels raw
  have nodeBound : raw.nodes.size ≤ rawInputSize channels raw := by
    unfold rawInputSize; omega
  have channelBound : channels ≤ rawInputSize channels raw := by
    unfold rawInputSize; omega
  constructor
  · intro node child incident
    have bounded := (valid.1 node).1 child incident
    omega
  · constructor
    · intro node channel incident
      have bounded := (valid.1 node).2 channel incident
      omega
    · intro root incident
      have bounded := valid.2 root incident
      omega

-- Clean too-wide Nat rejection is a separate source decoding boundary whose
-- cost counts inspected bit-input length. It is not proved by word modulo
-- conversion and does not inherit the accepted O(G) word-operation bound.
-- Once source words are encoded, every arbitrary narrower ABI word gets the
-- already checked safe probe; invalid represented references tagged-halt.

def referenceSliceCode (width entry accepted tag : Nat) : Program width 8 :=
  #[.branchZero 1 (word width accepted),
    .load 5 4,
    .load 0 5,
    .xor 0 0 3,
    .branchZero 0 (word width (entry + 8)),
    .constant 0 (word width tag),
    .emit 0,
    .halt,
    .add 4 4 3,
    .add 1 1 7,
    .branchZero 6 (word width entry)]


@[simp] theorem referenceSliceCode_size (width entry done tag : Nat) :
    (referenceSliceCode width entry done tag).size = 11 := rfl

private theorem marker_word_decrement (count : Nat) (positive : 0 < count)
    (fits : count < 2 ^ width) :
    word width (count + (2 ^ width - 1)) = word width (count - 1) := by
  apply Fin.ext
  change (count + (2 ^ width - 1)) % (2 ^ width) = (count - 1) % (2 ^ width)
  have split : count + (2 ^ width - 1) = count - 1 + 2 ^ width := by
    have nonzero := Nat.two_pow_pos width
    omega
  rw [split, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]


private theorem referenceAdvancePC (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word, Nat.mod_eq_of_lt fits]

-- Real three-step cursor/count/backedge after the checked probe.
private theorem reference_advance_execution (program : Program width 8)
    (entry cursor count : Nat) (state : State width 8)
    (positive : 0 < count) (countFits : count < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width) (codeFits : entry + 3 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (cursorHeld : state.reg 4 = word width cursor) (countHeld : state.reg 1 = word width count)
    (one : state.reg 3 = word width 1) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) (target : Nat)
    (at0 : program[entry]? = some (.add 4 4 3))
    (at1 : program[entry + 1]? = some (.add 1 1 7))
    (at2 : program[entry + 2]? = some (.branchZero 6 (word width target))) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width target ∧ final.halted = false ∧
      final.reg 4 = word width (cursor + 1) ∧ final.reg 1 = word width (count - 1) ∧
      (∀ register, register ≠ 4 → register ≠ 1 → final.reg register = state.reg register) := by
  let cursorUpdated := state.advance.put 4 (word width (cursor + 1))
  let countUpdated := cursorUpdated.advance.put 1 (word width (count - 1))
  let final := { countUpdated with pc := word width target }
  have oneFits : 1 < 2 ^ width := by omega
  have negativeFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have atFirst : cursorUpdated.pc = word width (entry + 1) := referenceAdvancePC state entry position (by omega)
  have atSecond : countUpdated.pc = word width (entry + 2) := by
    simpa only [countUpdated, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC cursorUpdated (entry + 1) atFirst (by omega)
  have cursorValue : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have oneValue : (word width 1).val = 1 := Nat.mod_eq_of_lt oneFits
  have countValue : (word width count).val = count := Nat.mod_eq_of_lt countFits
  have negativeValue : (word width (2 ^ width - 1)).val = 2 ^ width - 1 := Nat.mod_eq_of_lt negativeFits
  have addCursor : word width ((word width cursor).val + (word width 1).val) = word width (cursor + 1) := by
    rw [cursorValue, oneValue]
  have addCount : word width ((word width count).val + (word width (2 ^ width - 1)).val) = word width (count - 1) := by
    rw [countValue, negativeValue]
    exact marker_word_decrement count positive countFits
  have first : programStep program state = some cursorUpdated := by
    rw [fetched program state entry (.add 4 4 3) position (by omega) at0]
    simp only [step, running, Bool.false_eq_true, ite_false, cursorHeld, one]
    rw [addCursor]
  have second : programStep program cursorUpdated = some countUpdated := by
    rw [fetched program cursorUpdated (entry + 1) (.add 1 1 7) atFirst (by omega) at1]
    simp only [step, cursorUpdated, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, show (1 : Fin 8) ≠ 4 by decide, show (7 : Fin 8) ≠ 4 by decide,
      countHeld, decrement]
    rw [addCount]
    simp only [countUpdated, cursorUpdated, State.advance, State.put, running]
  have third : programStep program countUpdated = some final := by
    rw [fetched program countUpdated (entry + 2) (.branchZero 6 (word width target)) atSecond (by omega) at2]
    simp [step, countUpdated, cursorUpdated, State.advance, State.put, running, zero, final, word]
  have trace := Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl final)))
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_⟩
  · simpa only [final, countUpdated, cursorUpdated, State.liveWords, State.advance, State.put,
      Nat.max_self, Nat.reduceAdd] using trace
  · simp [final, countUpdated, cursorUpdated, State.put, State.advance]
  · rfl
  · intro register notCursor notCount
    simp [final, countUpdated, cursorUpdated, State.put, State.advance, notCursor, notCount]


private theorem source_test_load_execution (program : Program width 8)
    (entry done cursor count reference : Nat) (state : State width 8)
    (positive : 0 < count) (countFits : count < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) (codeFits : entry + 2 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (cursorHeld : state.reg 4 = word width cursor) (countHeld : state.reg 1 = word width count)
    (sourceBound : cursor < state.heap.size)
    (sourceCell : state.heap[cursor]'sourceBound = word width reference)
    (at0 : program[entry]? = some (.branchZero 1 (word width done)))
    (at1 : program[entry + 1]? = some (.load 5 4)) :
    ∃ loaded, Execution program state loaded 2 state.liveWords ∧
      loaded.heap = state.heap ∧ loaded.stack = state.stack ∧ loaded.output = state.output ∧
      loaded.pc = word width (entry + 2) ∧ loaded.halted = false ∧
      loaded.reg 5 = word width reference ∧
      (∀ register, register ≠ 5 → loaded.reg register = state.reg register) := by
  let tested := state.advance
  let loaded := tested.advance.put 5 (word width reference)
  have testedPC : tested.pc = word width (entry + 1) := referenceAdvancePC state entry position (by omega)
  have loadedPC : loaded.pc = word width (entry + 2) := by
    simpa only [loaded, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC tested (entry + 1) testedPC (by omega)
  have first : programStep program state = some tested := by
    rw [fetched program state entry (.branchZero 1 (word width done)) position (by omega) at0]
    simp [step, running, countHeld, word, Nat.mod_eq_of_lt countFits,
      show count ≠ 0 by omega, tested]
  have second : programStep program tested = some loaded := by
    rw [fetched program tested (entry + 1) (.load 5 4) testedPC (by omega) at1]
    simp [step, tested, running, State.advance, cursorHeld, word,
      Nat.mod_eq_of_lt cursorFits, sourceBound, sourceCell, loaded]
  refine ⟨loaded, ?_, rfl, rfl, rfl, loadedPC, running, ?_, ?_⟩
  · simpa only [loaded, tested, State.liveWords, State.advance, State.put,
      Nat.max_self, Nat.reduceAdd] using Execution.cons first (Execution.cons second (Execution.refl loaded))
  · simp [loaded, State.put]
  · intro register different
    simp [loaded, tested, State.put, State.advance, different]

theorem reference_valid_iteration (program : Program width 8)
    (entry done tag domain bound cursor count reference : Nat) (source : Array (Word width))
    (state : State width 8)
    (physical : ∀ position : Fin 11,
      program[entry + position.val]? = (referenceSliceCode width entry done tag)[position.val]?)
    (heap : state.heap = markerHeap domain bound source)
    (represented : reference < domain) (valid : reference < bound) (domainFits : domain ≤ 2 ^ width)
    (positive : 0 < count) (countFits : count < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width) (codeFits : entry + 11 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (cursorHeld : state.reg 4 = word width cursor) (countHeld : state.reg 1 = word width count)
    (one : state.reg 3 = word width 1) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1))
    (sourceBound : cursor < state.heap.size)
    (sourceCell : state.heap[cursor]'sourceBound = word width reference) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 4 = word width (cursor + 1) ∧ final.reg 1 = word width (count - 1) ∧
      final.reg 3 = word width 1 ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) ∧ final.reg 2 = state.reg 2 := by
  obtain ⟨loaded, first, loadHeap, loadStack, loadOutput, loadPC, loadRunning, referenceHeld, loadFrame⟩ :=
    source_test_load_execution program entry done cursor count reference state positive countFits (by omega)
      (by omega) position running cursorHeld countHeld sourceBound sourceCell
      (by simpa [referenceSliceCode] using physical ⟨0, by decide⟩)
      (by simpa [referenceSliceCode] using physical ⟨1, by decide⟩)
  have probeCells : ∀ index : Fin 3,
      program[entry + 2 + index.val]? = (probeCode width (entry + 8))[index.val]? := by
    intro index
    have cell := physical ⟨2 + index.val, by have := index.isLt; omega⟩
    fin_cases index <;> simpa [referenceSliceCode, probeCode, Nat.add_assoc] using cell
  obtain ⟨classified, classification, classHeap, classStack, classOutput, classRunning, classPC, classZero, classFrame⟩ :=
    probe_execution program (entry + 2) (entry + 8) domain bound reference source loaded probeCells
      (loadHeap.trans heap) represented domainFits loadPC loadRunning referenceHeld
      ((loadFrame 3 (by decide)).trans one) (by omega)
  have atAdvance : classified.pc = word width (entry + 8) := by simpa only [ite_eq_left valid] using classPC
  have classCursor : classified.reg 4 = word width cursor :=
    (classFrame 4 (by decide)).trans ((loadFrame 4 (by decide)).trans cursorHeld)
  have classCount : classified.reg 1 = word width count :=
    (classFrame 1 (by decide)).trans ((loadFrame 1 (by decide)).trans countHeld)
  have classOne : classified.reg 3 = word width 1 :=
    (classFrame 3 (by decide)).trans ((loadFrame 3 (by decide)).trans one)
  have classBranchZero : classified.reg 6 = word width 0 :=
    (classFrame 6 (by decide)).trans ((loadFrame 6 (by decide)).trans zero)
  have classDecrement : classified.reg 7 = word width (2 ^ width - 1) :=
    (classFrame 7 (by decide)).trans ((loadFrame 7 (by decide)).trans decrement)
  obtain ⟨final, tail, tailHeap, tailStack, tailOutput, finalPC, finalRunning, finalCursor, finalCount, tailFrame⟩ :=
    reference_advance_execution program (entry + 8) cursor count classified positive countFits cursorFits
      (by omega) atAdvance classRunning classCursor classCount classOne classBranchZero classDecrement entry
      (by simpa [referenceSliceCode] using physical ⟨8, by decide⟩)
      (by simpa [referenceSliceCode, Nat.add_assoc] using physical ⟨9, by decide⟩)
      (by simpa [referenceSliceCode, Nat.add_assoc] using physical ⟨10, by decide⟩)
  have loadedLive : loaded.liveWords = state.liveWords := by unfold State.liveWords; rw [loadHeap, loadStack, loadOutput]
  have classifiedLive : classified.liveWords = state.liveWords := by
    unfold State.liveWords; rw [classHeap, classStack, classOutput, loadHeap, loadStack, loadOutput]
  refine ⟨final, ?_, tailHeap.trans (classHeap.trans loadHeap), tailStack.trans (classStack.trans loadStack),
    tailOutput.trans (classOutput.trans loadOutput), finalPC, finalRunning, finalCursor, finalCount,
    (tailFrame 3 (by decide) (by decide)).trans classOne,
    (tailFrame 6 (by decide) (by decide)).trans classBranchZero,
    (tailFrame 7 (by decide) (by decide)).trans classDecrement,
    (tailFrame 2 (by decide) (by decide)).trans ((classFrame 2 (by decide)).trans (loadFrame 2 (by decide)))⟩
  have full := (first.append classification).append tail
  simpa only [loadedLive, classifiedLive, Nat.max_self, Nat.reduceAdd] using full

theorem reference_invalid_iteration (program : Program width 8)
    (entry done tag domain bound cursor count reference : Nat) (source : Array (Word width))
    (state : State width 8)
    (physical : ∀ position : Fin 11,
      program[entry + position.val]? = (referenceSliceCode width entry done tag)[position.val]?)
    (heap : state.heap = markerHeap domain bound source)
    (represented : reference < domain) (invalid : bound ≤ reference) (domainFits : domain ≤ 2 ^ width)
    (positive : 0 < count) (countFits : count < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) (codeFits : entry + 11 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (cursorHeld : state.reg 4 = word width cursor) (countHeld : state.reg 1 = word width count)
    (one : state.reg 3 = word width 1)
    (sourceBound : cursor < state.heap.size)
    (sourceCell : state.heap[cursor]'sourceBound = word width reference) :
    ∃ final, Execution program state final 8 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = word width tag :: state.output ∧ final.halted = true := by
  obtain ⟨loaded, first, loadHeap, loadStack, loadOutput, loadPC, loadRunning, referenceHeld, loadFrame⟩ :=
    source_test_load_execution program entry done cursor count reference state positive countFits cursorFits
      (by omega) position running cursorHeld countHeld sourceBound sourceCell
      (by simpa [referenceSliceCode] using physical ⟨0, by decide⟩)
      (by simpa [referenceSliceCode] using physical ⟨1, by decide⟩)
  have rejectCells : ∀ index : Fin 6,
      program[entry + 2 + index.val]? = (checkedProbeCode width (entry + 8) tag)[index.val]? := by
    intro index
    have cell := physical ⟨2 + index.val, by have := index.isLt; omega⟩
    fin_cases index <;> simpa [referenceSliceCode, checkedProbeCode, probeCode, rejectCode, Nat.add_assoc] using cell
  have checked := checked_probe_execution program (entry + 2) (entry + 8) tag domain bound reference source
    loaded rejectCells (loadHeap.trans heap) represented domainFits loadPC loadRunning referenceHeld
    ((loadFrame 3 (by decide)).trans one) (by omega)
  rcases checked with ⟨valid, _⟩ | ⟨_, final, rejection, finalHeap, finalStack, finalOutput, finalHalted⟩
  · omega
  · have loadedLive : loaded.liveWords = state.liveWords := by unfold State.liveWords; rw [loadHeap, loadStack, loadOutput]
    refine ⟨final, ?_, finalHeap.trans loadHeap, finalStack.trans loadStack, ?_, finalHalted⟩
    · have full := first.append rejection
      simpa only [loadedLive, Nat.reduceAdd,
        show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega] using full
    · rw [finalOutput, loadOutput]

private theorem reference_terminal_execution (program : Program width 8)
    (entry done : Nat) (state : State width 8)
    (at0 : program[entry]? = some (.branchZero 1 (word width done)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry < 2 ^ width) (emptyCount : state.reg 1 = word width 0) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg = state.reg := by
  let final := { state with pc := word width done }
  have transition : programStep program state = some final := by
    rw [fetched program state entry (.branchZero 1 (word width done)) position codeFits at0]
    simp [step, running, emptyCount, word, final, State.advance]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, rfl⟩
  simpa only [final, State.liveWords, Nat.max_self, Nat.reduceAdd] using
    Execution.cons transition (Execution.refl final)

/-- Validate the actual original slice in order, charging every stored occurrence. -/
theorem reference_slice_execution (program : Program width 8)
    (entry done tag domain bound : Nat) (source : Array (Word width))
    (physical : ∀ position : Fin 11,
      program[entry + position.val]? = (referenceSliceCode width entry done tag)[position.val]?)
    (domainFits : domain ≤ 2 ^ width) (codeFits : entry + 11 < 2 ^ width)
    (labels : List Nat) :
    ∀ (represented : ∀ reference ∈ labels, reference < domain) (cursor : Nat) (state : State width 8),
    (∀ position : Fin labels.length, state.heap[cursor + position.val]? = some (word width labels[position.val])) →
    state.heap = markerHeap domain bound source → labels.length < 2 ^ width →
    cursor + labels.length < 2 ^ width → state.pc = word width entry → state.halted = false →
    state.reg 4 = word width cursor → state.reg 1 = word width labels.length →
    state.reg 3 = word width 1 → state.reg 6 = word width 0 →
    state.reg 7 = word width (2 ^ width - 1) →
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 8 * labels.length + 1 ∧ peak ≤ state.liveWords + 1 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      (( (∀ reference ∈ labels, reference < bound) ∧ final.output = state.output ∧
        final.pc = word width done ∧ final.halted = false ∧
        final.reg 1 = word width 0 ∧ final.reg 4 = word width (cursor + labels.length) ∧
        final.reg 3 = word width 1 ∧ final.reg 6 = word width 0 ∧
        final.reg 7 = word width (2 ^ width - 1) ∧ final.reg 2 = state.reg 2) ∨
       (∃ reference ∈ labels, bound ≤ reference ∧
        final.output = word width tag :: state.output ∧ final.halted = true)) := by
  induction labels with
  | nil =>
    intro represented cursor state original heap countFits cursorFits position running cursorHeld countHeld one zero decrement
    obtain ⟨final, trace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalReg⟩ :=
      reference_terminal_execution program entry done state
        (by simpa [referenceSliceCode] using physical ⟨0, by decide⟩) position running (by omega)
        (by simpa only [List.length_nil] using countHeld)
    refine ⟨final, 1, state.liveWords, trace, by simp, by omega, finalHeap, finalStack, Or.inl ?_⟩
    rw [finalReg]
    exact ⟨by simp, finalOutput, finalPC, finalRunning, countHeld,
      by simpa only [List.length_nil, Nat.add_zero] using cursorHeld, one, zero, decrement, rfl⟩
  | cons reference rest ih =>
    intro represented cursor state original heap countFits cursorFits position running cursorHeld countHeld one zero decrement
    have firstCell : state.heap[cursor]? = some (word width reference) := by
      simpa only [Nat.add_zero, List.getElem_cons_zero] using original ⟨0, by simp⟩
    obtain ⟨sourceBound, sourceCell⟩ := Array.getElem?_eq_some_iff.mp firstCell
    have headRepresented : reference < domain := represented reference (by simp)
    by_cases valid : reference < bound
    · obtain ⟨middle, first, middleHeap, middleStack, middleOutput, middlePC, middleRunning,
        middleCursor, middleCount, middleOne, middleZero, middleDecrement, middleSaved⟩ :=
        reference_valid_iteration program entry done tag domain bound cursor (reference :: rest).length reference source state
          physical heap headRepresented valid domainFits (by simp) countFits (by simp only [List.length_cons] at cursorFits; omega)
          codeFits position running cursorHeld countHeld one zero decrement sourceBound sourceCell
      have tailStored : ∀ position : Fin rest.length,
          middle.heap[cursor + 1 + position.val]? = some (word width rest[position.val]) := by
        intro position
        rw [middleHeap]
        have cell := original ⟨position.val + 1, by simp only [List.length_cons]; have := position.isLt; omega⟩
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cell
      have tailRepresented : ∀ value ∈ rest, value < domain := by
        intro value member; exact represented value (List.mem_cons_of_mem reference member)
      obtain ⟨final, ticks, peak, last, tickBound, peakBound, finalHeap, finalStack, outcome⟩ :=
        ih tailRepresented (cursor + 1) middle tailStored (middleHeap.trans heap)
          (by simp only [List.length_cons] at countFits; omega)
          (by simp only [List.length_cons] at cursorFits; omega) middlePC middleRunning middleCursor
          (by simpa only [List.length_cons, Nat.add_sub_cancel] using middleCount) middleOne middleZero middleDecrement
      have middleLive : middle.liveWords = state.liveWords := by
        unfold State.liveWords; rw [middleHeap, middleStack, middleOutput]
      refine ⟨final, 8 + ticks, max state.liveWords peak, ?_, ?_, ?_,
        finalHeap.trans middleHeap, finalStack.trans middleStack, ?_⟩
      · exact first.append last
      · simp only [List.length_cons]; omega
      · rw [middleLive] at peakBound; omega
      · rcases outcome with ⟨allValid, finalOutput, finalPC, finalRunning, finalCount, finalCursor,
            finalOne, finalZero, finalDecrement, finalSaved⟩ | ⟨bad, member, badBound, finalOutput, finalHalted⟩
        · refine Or.inl ⟨?_, finalOutput.trans middleOutput, finalPC, finalRunning, finalCount,
            ?_, finalOne, finalZero, finalDecrement, finalSaved.trans middleSaved⟩
          · intro value member
            rcases List.mem_cons.mp member with rfl | member
            · exact valid
            · exact allValid value member
          · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalCursor
        · exact Or.inr ⟨bad, List.mem_cons_of_mem reference member, badBound,
            by rw [finalOutput, middleOutput], finalHalted⟩
    · have invalid : bound ≤ reference := by omega
      obtain ⟨final, trace, finalHeap, finalStack, finalOutput, finalHalted⟩ :=
        reference_invalid_iteration program entry done tag domain bound cursor (reference :: rest).length reference source state
          physical heap headRepresented invalid domainFits (by simp) countFits (by simp only [List.length_cons] at cursorFits; omega)
          codeFits position running cursorHeld countHeld one sourceBound sourceCell
      exact ⟨final, 8, state.liveWords + 1, trace, by simp only [List.length_cons]; omega, Nat.le_refl _,
        finalHeap, finalStack, Or.inr ⟨reference, by simp, invalid, finalOutput, finalHalted⟩⟩

/-- Relocation translates branch literals and the instruction pointer; ordinary
constants and every data address retain their original represented values. -/
def relocatedInstruction (delta : Nat) : Instruction width 8 → Instruction width 8
  | .branchZero src target => .branchZero src (word width (target.val + delta))
  | instruction => instruction

def relocatedState (delta : Nat) (state : State width 8) : State width 8 :=
  { state with pc := word width (state.pc.val + delta) }

@[simp] theorem relocatedState_live (delta : Nat) (state : State width 8) :
    (relocatedState delta state).liveWords = state.liveWords := rfl

private theorem relocated_advance_pc (delta : Nat) (state : State width 8) :
    word width ((word width (state.pc.val + delta)).val + 1) =
      word width ((word width (state.pc.val + 1)).val + delta) := by
  apply Fin.ext
  simp only [word, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Successful and faulting primitives commute with relocation alike. This
identity does not reinterpret a failed primitive as a tagged rejection. -/
theorem relocated_step (delta : Nat) (instruction : Instruction width 8)
    (state : State width 8) :
    step (relocatedInstruction delta instruction) (relocatedState delta state) =
      (step instruction state).map (relocatedState delta) := by
  have advancePC := relocated_advance_pc delta state
  dsimp only [relocatedState]
  cases halted : state.halted with
  | true => simp [step, halted]
  | false =>
    cases instruction with
    | load dst address =>
      by_cases valid : (state.reg address).val < state.heap.size
      · simp [relocatedInstruction, step, halted, valid, relocatedState, State.advance, State.put, advancePC]
      · simp [relocatedInstruction, step, halted, valid]
    | store address src =>
      by_cases valid : (state.reg address).val < state.heap.size
      · simp [relocatedInstruction, step, halted, valid, relocatedState, State.advance, advancePC]
      · simp [relocatedInstruction, step, halted, valid]
    | allocate src =>
      by_cases valid : state.heap.size < 2 ^ width
      · simp [relocatedInstruction, step, halted, valid, relocatedState, State.advance, advancePC]
      · simp [relocatedInstruction, step, halted, valid]
    | release =>
      cases empty : state.heap.isEmpty <;>
        simp [relocatedInstruction, step, halted, empty, relocatedState, State.advance, advancePC]
    | pop dst =>
      cases stack : state.stack <;>
        simp [relocatedInstruction, step, halted, stack, relocatedState, State.advance, State.put, advancePC]
    | branchZero src target =>
      by_cases zero : (state.reg src).val = 0
      · simp [relocatedInstruction, step, halted, zero, relocatedState, State.advance,
          word, Nat.mod_eq_of_lt target.isLt]
      · simp [relocatedInstruction, step, halted, zero, relocatedState, State.advance, advancePC]
    | constant dst value => simp [relocatedInstruction, step, halted, relocatedState, State.advance, State.put, advancePC]
    | copy dst src => simp [relocatedInstruction, step, halted, relocatedState, State.advance, State.put, advancePC]
    | add dst left right => simp [relocatedInstruction, step, halted, relocatedState, State.advance, State.put, advancePC]
    | xor dst left right => simp [relocatedInstruction, step, halted, relocatedState, State.advance, State.put, advancePC]
    | push src => simp [relocatedInstruction, step, halted, relocatedState, State.advance, advancePC]
    | emit src => simp [relocatedInstruction, step, halted, relocatedState, State.advance, advancePC]
    | halt => simp [relocatedInstruction, step, halted, relocatedState, State.advance, advancePC]

private theorem relocated_programStep (program source : Program width 8)
    (delta : Nat)
    (physical : ∀ index (valid : index < source.size),
      program[delta + index]? = some (relocatedInstruction delta (source[index]'valid)))
    (capacity : delta + source.size < 2 ^ width)
    (state middle : State width 8)
    (transition : programStep source state = some middle) :
    programStep program (relocatedState delta state) = some (relocatedState delta middle) := by
  cases fetchedSource : source[state.pc.val]? with
  | none => simp [programStep, fetchedSource] at transition
  | some instruction =>
    obtain ⟨valid, sourceInstruction⟩ := Array.getElem?_eq_some_iff.mp fetchedSource
    have pointerFits : state.pc.val + delta < 2 ^ width := by omega
    have residentFetch : program[(relocatedState delta state).pc.val]? =
        some (relocatedInstruction delta instruction) := by
      have actual := physical state.pc.val valid
      rw [sourceInstruction] at actual
      have shiftedValue : (word width (state.pc.val + delta)).val = state.pc.val + delta :=
        Nat.mod_eq_of_lt pointerFits
      change program[(word width (state.pc.val + delta)).val]? = _
      rw [shiftedValue]
      simpa only [Nat.add_comm] using actual
    have primitive : step instruction state = some middle := by
      simpa [programStep, fetchedSource] using transition
    unfold programStep
    rw [residentFetch]
    change step (relocatedInstruction delta instruction) (relocatedState delta state) =
      some (relocatedState delta middle)
    rw [relocated_step, primitive]
    rfl

-- Full Execution induction can now apply this lemma at each successful cons;
-- invalid source PCs cannot occur because transition fetch would be none.
-- In the refl branch liveWords is unchanged; in cons the same max/tick formulas
-- therefore carry without a trace budget hypothesis or extra machine operation.

theorem relocated_execution (program source : Program width 8) (delta : Nat)
    (physical : ∀ index (valid : index < source.size),
      program[delta + index]? = some (relocatedInstruction delta (source[index]'valid)))
    (capacity : delta + source.size < 2 ^ width)
    {state final : State width 8} {ticks peak : Nat}
    (trace : Execution source state final ticks peak) :
    Execution program (relocatedState delta state) (relocatedState delta final) ticks peak := by
  induction trace with
  | refl state => simpa only [relocatedState_live] using Execution.refl (relocatedState delta state)
  | cons transition tail ih =>
    have next := relocated_programStep program source delta physical capacity _ _ transition
    simpa only [relocatedState_live] using Execution.cons next ih

def sourceSaveCell (width address : Nat) : Controller.Cost.GateProgram.Code width :=
  [.constant 0 (word width address), .load 0 0, .push 0]

def sourceSaveCode (width start : Nat) : Nat → Controller.Cost.GateProgram.Code width
  | 0 => []
  | count + 1 => sourceSaveCode width (start + 1) count ++ sourceSaveCell width start

@[simp] theorem sourceSaveCell_length (width address : Nat) :
    (sourceSaveCell width address).length = 3 := rfl

@[simp] theorem sourceSaveCode_length (width start count : Nat) :
    (sourceSaveCode width start count).length = 3 * count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [sourceSaveCode, List.length_append, ih, sourceSaveCell_length]; omega

private theorem source_low_fetch (program : Program width 4) (state : State width 4)
    (entry : Nat) (instruction : Instruction width 4)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (physical : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits, physical]
  rfl

private theorem source_low_advance (state : State width 4) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position]
  rw [show (word width entry).val = entry from Nat.mod_eq_of_lt fits]

private theorem source_save_cell_execution (program : Program width 4)
    (state : State width 4) (entry address : Nat) (value : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 3 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < state.heap.size) (cell : state.heap[address]'valid = value)
    (physical : Controller.Cost.GateProgram.BlockAt program entry (sourceSaveCell width address)) :
    ∃ final, Execution program state final 3 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = value :: state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false := by
  let addressed := state.advance.put 0 (word width address)
  let loaded := addressed.advance.put 0 value
  let final := { loaded.advance with stack := value :: loaded.stack }
  have pc1 : addressed.pc = word width (entry + 1) := source_low_advance state entry position (by omega)
  have pc2 : loaded.pc = word width (entry + 2) := by
    simpa only [loaded, State.put, Nat.add_assoc, Nat.reduceAdd] using
      source_low_advance addressed (entry + 1) pc1 (by omega)
  have first : programStep program state = some addressed := by
    rw [source_low_fetch program state entry (.constant 0 (word width address)) position (by omega)
      (by simpa [sourceSaveCell] using physical 0 (by simp [sourceSaveCell]))]
    simp [step, running, addressed]
  have second : programStep program addressed = some loaded := by
    rw [source_low_fetch program addressed (entry + 1) (.load 0 0) pc1 (by omega)
      (by simpa [sourceSaveCell] using physical 1 (by simp [sourceSaveCell]))]
    simp [step, addressed, State.advance, State.put, running, word,
      Nat.mod_eq_of_lt addressFits, valid, cell, loaded]
  have third : programStep program loaded = some final := by
    rw [source_low_fetch program loaded (entry + 2) (.push 0) pc2 (by omega)
      (by simpa [sourceSaveCell] using physical 2 (by simp [sourceSaveCell]))]
    simp [step, loaded, addressed, State.advance, State.put, running, final]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, running⟩
  · have trace := Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl final)))
    convert trace using 1 <;>
      simp only [final, loaded, addressed, State.liveWords, State.advance, State.put,
        List.length_cons] <;> omega
  · change loaded.advance.pc = word width (entry + 3)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using source_low_advance loaded (entry + 2) pc2 (by omega)

private theorem source_save_low_execution (program : Program width 4)
    (packet : List (Word width)) :
    ∀ (state : State width 4) (entry start : Nat),
    state.pc = word width entry → state.halted = false →
    entry + 3 * packet.length < 2 ^ width → start + packet.length ≤ 2 ^ width →
    (∀ index : Fin packet.length, state.heap[start + index.val]? = some packet[index.val]) →
    Controller.Cost.GateProgram.BlockAt program entry (sourceSaveCode width start packet.length) →
    ∃ final, Execution program state final (3 * packet.length) (state.liveWords + packet.length) ∧
      final.heap = state.heap ∧ final.stack = packet ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3 * packet.length) ∧ final.halted = false := by
  induction packet with
  | nil =>
    intro state entry start position running codeFits sourceFits cells physical
    exact ⟨state, by simpa using Execution.refl (p := program) state, rfl,
      by simp, rfl, by simpa using position, running⟩
  | cons value packet ih =>
    intro state entry start position running codeFits sourceFits cells physical
    have body := Controller.Cost.GateProgram.BlockAt.prefix program entry
      (sourceSaveCode width (start + 1) packet.length) (sourceSaveCell width start) physical
    have tailCells : ∀ index : Fin packet.length,
        state.heap[(start + 1) + index.val]? = some packet[index.val] := by
      intro index
      have actual := cells ⟨index.val + 1, by simp only [List.length_cons]; omega⟩
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using actual
    obtain ⟨middle, first, firstHeap, firstStack, firstOutput, firstPC, firstRunning⟩ :=
      ih state entry (start + 1) position running
        (by simp only [List.length_cons] at codeFits; omega)
        (by simp only [List.length_cons] at sourceFits; omega) tailCells body
    have finish : Controller.Cost.GateProgram.BlockAt program (entry + 3 * packet.length)
        (sourceSaveCell width start) := by
      simpa only [sourceSaveCode_length] using
        Controller.Cost.GateProgram.BlockAt.suffix program entry
          (sourceSaveCode width (start + 1) packet.length) (sourceSaveCell width start) physical
    have headCell : state.heap[start]? = some value := by
      simpa using cells ⟨0, by simp⟩
    obtain ⟨valid, getter⟩ := Array.getElem?_eq_some_iff.mp headCell
    have middleValid : start < middle.heap.size := by rw [firstHeap]; exact valid
    have middleGetter : middle.heap[start]'middleValid = value := by
      simpa only [firstHeap] using getter
    obtain ⟨final, rest, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
      source_save_cell_execution program middle (entry + 3 * packet.length) start value firstPC firstRunning
        (by simp only [List.length_cons] at codeFits; omega)
        (by simp only [List.length_cons] at sourceFits; omega) middleValid middleGetter finish
    have middleLive : middle.liveWords = state.liveWords + packet.length := by
      unfold State.liveWords
      rw [firstHeap, firstStack, firstOutput]
      simp only [List.length_append]
      omega
    refine ⟨final, ?_, finalHeap.trans firstHeap, ?_, finalOutput.trans firstOutput, ?_, finalRunning⟩
    · have trace := first.append rest
      rw [middleLive] at trace
      convert trace using 1 <;> simp only [List.length_cons] <;> omega
    · rw [finalStack, firstStack]
      rfl
    · convert finalPC using 1 <;> congr 1 <;> simp only [List.length_cons] <;> omega

theorem source_save_execution (program : Program width 8) (entry start : Nat)
    (state : State width 8) (packet : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 3 * packet.length < 2 ^ width)
    (sourceFits : start + packet.length ≤ 2 ^ width)
    (cells : ∀ index : Fin packet.length, state.heap[start + index.val]? = some packet[index.val])
    (present : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt program entry
      (sourceSaveCode width start packet.length)) :
    ∃ final, Execution program state final (3 * packet.length) (state.liveWords + packet.length) ∧
      final.heap = state.heap ∧ final.stack = packet ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 3 * packet.length) ∧
      final.halted = false ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let low := markerNarrow state
  let view := Controller.Cost.ForestZeroCallerWiden.lowerProgram program
  have block := Controller.Cost.ForestZeroCallerWiden.lower_block program entry
    (sourceSaveCode width start packet.length) present
  obtain ⟨last, trace, heap, stack, output, pc, active⟩ :=
    source_save_low_execution view packet low entry start position running codeFits sourceFits cells block
  have lifted := Controller.Cost.ForestZeroCallerWiden.execution program low last
    (3 * packet.length) (low.liveWords + packet.length) trace active state.reg
  have sourceLive : low.liveWords + 4 = state.liveWords := by
    simp only [low, markerNarrow, State.liveWords]
    omega
  let final := Controller.Cost.RegisterWiden.widenState last state.reg
  refine ⟨final, ?_, heap, stack, output, pc, active, ?_⟩
  · rw [markerWidenNarrow] at lifted
    simpa only [show low.liveWords + packet.length + 4 = state.liveWords + packet.length by omega] using lifted
  · intro register high
    exact Controller.Cost.RegisterWiden.widenState_high last state.reg register high

/-- Restore the saved original packet through fetched pops and allocations.
Every pre-existing physical queue, row, mark, and link cell is retained. -/
theorem source_reload_execution (program : Program width 8) (entry : Nat)
    (state : State width 8) (packet suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = packet ++ suffix)
    (codeFits : entry + 2 * packet.length < 2 ^ width)
    (room : state.heap.size + packet.length ≤ 2 ^ width)
    (present : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt program entry
      (Controller.Cost.InputLoad.code packet.length)) :
    ∃ final, Execution program state final (2 * packet.length) state.liveWords ∧
      final.heap = state.heap ++ packet.toArray ∧ final.stack = suffix ∧
      final.output = state.output ∧ final.pc = word width (entry + 2 * packet.length) ∧
      final.halted = false ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) ∧
      (∀ address, address < state.heap.size → final.heap[address]? = state.heap[address]?) := by
  let low := markerNarrow state
  let view := Controller.Cost.ForestZeroCallerWiden.lowerProgram program
  have block := Controller.Cost.ForestZeroCallerWiden.lower_block program entry
    (Controller.Cost.InputLoad.code packet.length) present
  obtain ⟨last, trace, heap, stack, output, pc, active⟩ :=
    Controller.Cost.InputLoad.code_execution view low packet suffix entry position running
      saved codeFits room block
  have lifted := Controller.Cost.ForestZeroCallerWiden.execution program low last
    (2 * packet.length) low.liveWords trace active state.reg
  have sourceLive : low.liveWords + 4 = state.liveWords := by
    simp only [low, markerNarrow, State.liveWords]
    omega
  let final := Controller.Cost.RegisterWiden.widenState last state.reg
  refine ⟨final, ?_, heap, stack, output, pc, active, ?_, ?_⟩
  · rw [markerWidenNarrow] at lifted
    simpa only [sourceLive] using lifted
  · intro register high
    exact Controller.Cost.RegisterWiden.widenState_high last state.reg register high
  · intro address valid
    change last.heap[address]? = state.heap[address]?
    rw [heap]
    exact Array.getElem?_append_left valid

def rankCopyCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done), .load 5 1, .add 5 5 4, .store 5 2,
    .add 1 1 3, .add 2 2 3, .add 0 0 7, .branchZero 6 (word width entry)]

@[simp] theorem rankCopyCode_size (width entry done : Nat) :
    (rankCopyCode width entry done).size = 8 := rfl

def actualRankHeap (width rankBase rank : Nat) :
    List Nat → Array (Word width) → Array (Word width)
  | [], heap => heap
  | old :: queue, heap =>
    actualRankHeap width rankBase (rank + 1) queue (heap.setIfInBounds (rankBase + old) (word width rank))

private theorem rank_iteration_execution (program : Program width 8)
    (entry done cursor rank rankBase count old : Nat) (state : State width 8)
    (physical : ∀ position : Fin 8,
      program[entry + position.val]? = (rankCopyCode width entry done)[position.val]?)
    (codeFits : entry + 8 < 2 ^ width) (positive : 0 < count)
    (countFits : count < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (rankFits : rank + 1 < 2 ^ width) (destinationFits : rankBase + old < 2 ^ width)
    (sourceBound : cursor < state.heap.size) (destinationBound : rankBase + old < state.heap.size)
    (sourceCell : state.heap[cursor]'sourceBound = word width old)
    (position : state.pc = word width entry) (running : state.halted = false)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (rankHeld : state.reg 2 = word width rank) (one : state.reg 3 = word width 1)
    (baseHeld : state.reg 4 = word width rankBase) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      final.heap = state.heap.set (rankBase + old) (word width rank) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 2 = word width (rank + 1) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 → register ≠ 5 →
        final.reg register = state.reg register) := by
  let s1 := state.advance
  let s2 := s1.advance.put 5 (word width old)
  let s3 := s2.advance.put 5 (word width (rankBase + old))
  let s4 := { s3.advance with heap := state.heap.set (rankBase + old) (word width rank) }
  let s5 := s4.advance.put 1 (word width (cursor + 1))
  let s6 := s5.advance.put 2 (word width (rank + 1))
  let s7 := s6.advance.put 0 (word width (count - 1))
  let final := { s7.advance with pc := word width entry }
  have pc1 : s1.pc = word width (entry + 1) := referenceAdvancePC state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    simpa only [s4, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    simpa only [s5, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    simpa only [s6, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5 (entry + 5) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 7) := by
    simpa only [s7, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6 (entry + 6) pc6 (by omega)
  have oneFits : 1 < 2 ^ width := by omega
  have negativeFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have oldFits : old < 2 ^ width := by omega
  have baseFits : rankBase < 2 ^ width := by omega
  have countValue : (word width count).val = count := Nat.mod_eq_of_lt countFits
  have oldValue : (word width old).val = old := Nat.mod_eq_of_lt oldFits
  have baseValue : (word width rankBase).val = rankBase := Nat.mod_eq_of_lt baseFits
  have oneValue : (word width 1).val = 1 := Nat.mod_eq_of_lt oneFits
  have cursorValue : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have rankValue : (word width rank).val = rank := Nat.mod_eq_of_lt (by omega)
  have destinationValue : (word width (rankBase + old)).val = rankBase + old := Nat.mod_eq_of_lt destinationFits
  have addDestination : word width ((word width old).val + (word width rankBase).val) =
      word width (rankBase + old) := by rw [oldValue, baseValue, Nat.add_comm]
  have addCursor : word width ((word width cursor).val + (word width 1).val) = word width (cursor + 1) := by rw [cursorValue, oneValue]
  have addRank : word width ((word width rank).val + (word width 1).val) = word width (rank + 1) := by rw [rankValue, oneValue]
  have addCount : word width ((word width count).val + (word width (2 ^ width - 1)).val) = word width (count - 1) := by
    rw [countValue, show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt negativeFits]
    exact marker_word_decrement count positive countFits
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.branchZero 0 (word width done)) position (by omega)
      (by simpa [rankCopyCode] using physical ⟨0, by decide⟩)]
    simp [step, running, countHeld, word, Nat.mod_eq_of_lt countFits, show count ≠ 0 by omega, s1]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.load 5 1) pc1 (by omega)
      (by simpa [rankCopyCode] using physical ⟨1, by decide⟩)]
    simp [step, s1, State.advance, running, cursorHeld, word, Nat.mod_eq_of_lt (by omega : cursor < 2 ^ width), sourceBound, sourceCell, s2]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 5 5 4) pc2 (by omega)
      (by simpa [rankCopyCode] using physical ⟨2, by decide⟩)]
    simp only [step, s2, s1, State.advance, State.put, running, Bool.false_eq_true, ite_false,
      ite_true, show (4 : Fin 8) ≠ 5 by decide, baseHeld]
    rw [addDestination]
    simp only [s3, s2, s1, State.advance, State.put, running]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.store 5 2) pc3 (by omega)
      (by simpa [rankCopyCode] using physical ⟨3, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running, destinationValue, destinationBound, rankHeld, s4]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 1 1 3) pc4 (by omega)
      (by simpa [rankCopyCode] using physical ⟨4, by decide⟩)]
    simp only [step, s4, s3, s2, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, show (1 : Fin 8) ≠ 5 by decide, show (3 : Fin 8) ≠ 5 by decide, cursorHeld, one]
    rw [addCursor]
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, running]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.add 2 2 3) pc5 (by omega)
      (by simpa [rankCopyCode] using physical ⟨5, by decide⟩)]
    simp only [step, s5, s4, s3, s2, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, show (2 : Fin 8) ≠ 1 by decide, show (2 : Fin 8) ≠ 5 by decide,
      show (3 : Fin 8) ≠ 1 by decide, show (3 : Fin 8) ≠ 5 by decide, rankHeld, one]
    rw [addRank]
    simp only [s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) (.add 0 0 7) pc6 (by omega)
      (by simpa [rankCopyCode] using physical ⟨6, by decide⟩)]
    simp only [step, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, show (0 : Fin 8) ≠ 2 by decide, show (0 : Fin 8) ≠ 1 by decide,
      show (0 : Fin 8) ≠ 5 by decide, show (7 : Fin 8) ≠ 2 by decide,
      show (7 : Fin 8) ≠ 1 by decide, show (7 : Fin 8) ≠ 5 by decide, countHeld, decrement]
    rw [addCount]
    simp only [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
  have t7 : programStep program s7 = some final := by
    rw [fetched program s7 (entry + 7) (.branchZero 6 (word width entry)) pc7 (by omega)
      (by simpa [rankCopyCode] using physical ⟨7, by decide⟩)]
    simp [step, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, zero, word, final]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3
      (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.refl final))))))))
    simpa only [final, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put,
      Array.size_set, Nat.max_self, Nat.reduceAdd] using trace
  · rfl
  · simp [final, s7, s6, s5, State.advance, State.put]
  · simp [final, s7, s6, State.advance, State.put]
  · intro register notCount notCursor notRank notTemporary
    simp [final, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put,
      notCount, notCursor, notRank, notTemporary]

private theorem rank_terminal_execution (program : Program width 8)
    (entry done : Nat) (state : State width 8)
    (physical : program[entry]? = some (.branchZero 0 (word width done)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry < 2 ^ width) (emptyCount : state.reg 0 = word width 0) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg = state.reg := by
  let final := { state with pc := word width done }
  have transition : programStep program state = some final := by
    rw [fetched program state entry (.branchZero 0 (word width done)) position codeFits physical]
    simp [step, running, emptyCount, word, final, State.advance]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, rfl⟩
  simpa only [final, State.liveWords, Nat.max_self, Nat.reduceAdd] using
    Execution.cons transition (Execution.refl final)

/-- Visit the stored original FIFO exactly once and write its ranks physically. -/
theorem rank_copy_execution (program : Program width 8) (entry done rankBase nodes : Nat)
    (physical : ∀ position : Fin 8,
      program[entry + position.val]? = (rankCopyCode width entry done)[position.val]?)
    (codeFits : entry + 8 < 2 ^ width) (queue : List Nat) :
    ∀ (bounded : ∀ old ∈ queue, old < nodes) (cursor rank : Nat) (state : State width 8),
    state.pc = word width entry → state.halted = false →
    state.reg 0 = word width queue.length → state.reg 1 = word width cursor →
    state.reg 2 = word width rank → state.reg 3 = word width 1 →
    state.reg 4 = word width rankBase → state.reg 6 = word width 0 →
    state.reg 7 = word width (2 ^ width - 1) →
    queue.length < 2 ^ width → cursor + queue.length ≤ rankBase →
    rank + queue.length < 2 ^ width → rankBase + nodes ≤ state.heap.size →
    rankBase + nodes ≤ 2 ^ width →
    (∀ index : Fin queue.length, state.heap[cursor + index.val]? = some (word width queue[index.val])) →
    ∃ final, Execution program state final (8 * queue.length + 1) state.liveWords ∧
      final.heap = actualRankHeap width rankBase rank queue state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width (cursor + queue.length) ∧
      final.reg 2 = word width (rank + queue.length) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 → register ≠ 5 →
        final.reg register = state.reg register) ∧
      (∀ address, address < rankBase → final.heap[address]? = state.heap[address]?) := by
  induction queue with
  | nil =>
    intro bounded cursor rank state position running countHeld cursorHeld rankHeld one baseHeld zero decrement
      countFits sourceBefore rankFits room destinationFits cells
    obtain ⟨final, trace, heap, stack, output, pc, active, registers⟩ :=
      rank_terminal_execution program entry done state
        (by simpa [rankCopyCode] using physical ⟨0, by decide⟩) position running (by omega) countHeld
    refine ⟨final, by simpa using trace, heap, stack, output, pc, active, ?_, ?_, ?_, ?_, ?_⟩
    · rw [registers]; exact countHeld
    · rw [registers]; simpa using cursorHeld
    · rw [registers]; simpa using rankHeld
    · intro register notCount notCursor notRank notTemp; rw [registers]
    · intro address valid; rw [heap]
  | cons old queue ih =>
    intro bounded cursor rank state position running countHeld cursorHeld rankHeld one baseHeld zero decrement
      countFits sourceBefore rankFits room destinationFits cells
    have oldBound : old < nodes := bounded old (by simp)
    have sourceOption : state.heap[cursor]? = some (word width old) := by simpa using cells ⟨0, by simp⟩
    obtain ⟨sourceBound, sourceCell⟩ := Array.getElem?_eq_some_iff.mp sourceOption
    have destinationBound : rankBase + old < state.heap.size := by omega
    obtain ⟨middle, first, heap, stack, output, pc, active, countNext, cursorNext, rankNext, frames⟩ :=
      rank_iteration_execution program entry done cursor rank rankBase (old :: queue).length old state physical
        codeFits (by simp) countFits
        (by simp only [List.length_cons] at sourceBefore; omega)
        (by simp only [List.length_cons] at rankFits; omega) (by omega)
        sourceBound destinationBound sourceCell position running countHeld cursorHeld rankHeld one baseHeld zero decrement
    have middleCells : ∀ index : Fin queue.length,
        middle.heap[(cursor + 1) + index.val]? = some (word width queue[index.val]) := by
      intro index
      rw [heap, Array.getElem?_set destinationBound]
      have before : cursor + 1 + index.val < rankBase := by
        have := index.isLt
        simp only [List.length_cons] at sourceBefore
        omega
      rw [ite_eq_right (by omega : rankBase + old ≠ cursor + 1 + index.val)]
      have actual := cells ⟨index.val + 1, by simp only [List.length_cons]; omega⟩
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using actual
    obtain ⟨final, rest, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      finalCount, finalCursor, finalRank, finalFrames, finalPrefix⟩ :=
      ih (by intro child member; exact bounded child (by simp [member])) (cursor + 1) (rank + 1) middle
        pc active (by simpa only [List.length_cons, Nat.add_sub_cancel] using countNext)
        cursorNext rankNext ((frames 3 (by decide) (by decide) (by decide) (by decide)).trans one)
        ((frames 4 (by decide) (by decide) (by decide) (by decide)).trans baseHeld)
        ((frames 6 (by decide) (by decide) (by decide) (by decide)).trans zero)
        ((frames 7 (by decide) (by decide) (by decide) (by decide)).trans decrement)
        (by simp only [List.length_cons] at countFits; omega)
        (by simp only [List.length_cons] at sourceBefore; omega)
        (by simp only [List.length_cons] at rankFits; omega)
        (by rw [heap]; simpa only [Array.size_set] using room) destinationFits middleCells
    have middleLive : middle.liveWords = state.liveWords := by
      unfold State.liveWords
      rw [heap, stack, output, Array.size_set]
    refine ⟨final, ?_, ?_, finalStack.trans stack, finalOutput.trans output,
      finalPC, finalRunning, finalCount, ?_, ?_, ?_, ?_⟩
    · have trace := first.append rest
      rw [middleLive] at trace
      convert trace using 1 <;> simp only [List.length_cons, Nat.max_self] <;> omega
    · rw [finalHeap, heap]
      simp only [actualRankHeap, Array.setIfInBounds_def, destinationBound, dite_true]
    · convert finalCursor using 1 <;> congr 1 <;> simp only [List.length_cons] <;> omega
    · convert finalRank using 1 <;> congr 1 <;> simp only [List.length_cons] <;> omega
    · intro register notCount notCursor notRank notTemp
      exact (finalFrames register notCount notCursor notRank notTemp).trans
        (frames register notCount notCursor notRank notTemp)
    · intro address before
      rw [finalPrefix address before, heap, Array.getElem?_set destinationBound,
        ite_eq_right (by omega : rankBase + old ≠ address)]

private theorem actualRankHeap_size (rankBase rank : Nat) (queue : List Nat) (heap : Array (Word width)) :
    (actualRankHeap width rankBase rank queue heap).size = heap.size := by
  induction queue generalizing rank heap with
  | nil => rfl
  | cons old queue ih => simpa only [actualRankHeap, Array.size_setIfInBounds] using ih (rank + 1) (heap.setIfInBounds (rankBase + old) (word width rank))

private theorem actualRankHeap_retains (rankBase rank nodes old : Nat)
    (queue : List Nat) (heap : Array (Word width))
    (bounded : ∀ child ∈ queue, child < nodes) (room : rankBase + nodes ≤ heap.size)
    (absent : old ∉ queue) :
    (actualRankHeap width rankBase rank queue heap)[rankBase + old]? = heap[rankBase + old]? := by
  induction queue generalizing rank heap with
  | nil => rfl
  | cons child queue ih =>
    have childBound := bounded child (by simp)
    have valid : rankBase + child < heap.size := by omega
    have distinct : child ≠ old := by intro equality; subst child; exact absent (by simp)
    have next := ih (rank + 1) (heap.set (rankBase + child) (word width rank))
      (by intro label member; exact bounded label (by simp [member]))
      (by simpa only [Array.size_set] using room) (by intro member; exact absent (by simp [member]))
    simp only [actualRankHeap, Array.setIfInBounds_def, valid, dite_true]
    rw [next, Array.getElem?_set valid, ite_eq_right (by omega : rankBase + child ≠ rankBase + old)]

/-- Each actual rank cell contains the occurrence position of its original FIFO
node. Distinctness is consumed to protect an earlier write from later stores. -/
theorem actual_rank_lookup (rankBase rank nodes : Nat) (queue : List Nat)
    (heap : Array (Word width)) (bounded : ∀ old ∈ queue, old < nodes)
    (room : rankBase + nodes ≤ heap.size) (distinct : queue.Nodup)
    (index : Fin queue.length) :
    (actualRankHeap width rankBase rank queue heap)[rankBase + queue[index.val]]? =
      some (word width (rank + index.val)) := by
  induction queue generalizing rank heap with
  | nil => exact Fin.elim0 index
  | cons old queue ih =>
    have oldBound := bounded old (by simp)
    have valid : rankBase + old < heap.size := by omega
    have headAbsent : old ∉ queue := (List.nodup_cons.mp distinct).1
    have tailDistinct : queue.Nodup := (List.nodup_cons.mp distinct).2
    have tailBound : ∀ child ∈ queue, child < nodes := by
      intro child member; exact bounded child (by simp [member])
    by_cases atHead : index.val = 0
    · simp only [atHead, List.getElem_cons_zero, Nat.add_zero, actualRankHeap,
        Array.setIfInBounds_def, valid, dite_true]
      rw [actualRankHeap_retains rankBase (rank + 1) nodes old queue
        (heap.set (rankBase + old) (word width rank)) tailBound
        (by simpa only [Array.size_set] using room) headAbsent,
        Array.getElem?_set valid, ite_eq_left rfl]
    · let tailIndex : Fin queue.length := ⟨index.val - 1, by have := index.isLt; simp only [List.length_cons] at this; omega⟩
      have indexValue : index.val = tailIndex.val + 1 := by simp only [tailIndex]; omega
      have selected : (old :: queue)[index.val] = queue[tailIndex.val] := by
        have indexEq : index = ⟨tailIndex.val + 1, by simp only [List.length_cons]; have := tailIndex.isLt; omega⟩ := Fin.ext indexValue
        change (old :: queue).get index = queue.get tailIndex
        rw [indexEq]
        exact List.get_cons_succ
      rw [selected, actualRankHeap]
      simp only [Array.setIfInBounds_def, valid, dite_true]
      have actual := ih (rank + 1) (heap.set (rankBase + old) (word width rank)) tailBound
        (by simpa only [Array.size_set] using room) tailDistinct tailIndex
      have rankValue : rank + index.val = rank + 1 + tailIndex.val := by omega
      simpa only [rankValue] using actual

def packetReleaseCode (width count : Nat) : Controller.Cost.GateProgram.Code width :=
  List.replicate count .release

@[simp] theorem packetReleaseCode_length (width count : Nat) :
    (packetReleaseCode width count).length = count := by simp [packetReleaseCode]

private def releasedPacketHeap (width : Nat) : Nat → Array (Word width) → Array (Word width)
  | 0, heap => heap
  | count + 1, heap => releasedPacketHeap width count heap.pop

private theorem releasedPacketHeap_size (count : Nat) (heap : Array (Word width))
    (inside : count ≤ heap.size) :
    (releasedPacketHeap width count heap).size = heap.size - count := by
  induction count generalizing heap with
  | zero => simp [releasedPacketHeap]
  | succ count ih =>
    rw [releasedPacketHeap, ih heap.pop (by simp only [Array.size_pop]; omega), Array.size_pop]
    omega

private theorem packet_release_cell (program : Program width 4) (state : State width 4)
    (entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (fits : entry + 1 < 2 ^ width) (nonempty : 0 < state.heap.size)
    (physical : program[entry]? = some .release) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      final.heap = state.heap.pop ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 1) ∧ final.halted = false ∧ final.reg = state.reg := by
  let final := { state.advance with heap := state.heap.pop }
  have active : state.heap.isEmpty = false := Array.isEmpty_eq_false_iff.mpr (by
    intro empty; rw [empty] at nonempty; simp at nonempty)
  have transition : programStep program state = some final := by
    rw [source_low_fetch program state entry .release position (by omega) physical]
    simp [step, running, active, final]
  have live : final.liveWords ≤ state.liveWords := by
    simp only [final, State.liveWords, State.advance, Array.size_pop]
    omega
  refine ⟨final, ?_, rfl, rfl, rfl, source_low_advance state entry position (by omega), running, rfl⟩
  simpa only [Nat.zero_add, Nat.max_eq_left live] using Execution.cons transition (Execution.refl final)

private theorem packet_release_low_execution (program : Program width 4) (count : Nat) :
    ∀ (state : State width 4) (entry : Nat), state.pc = word width entry → state.halted = false →
    entry + count < 2 ^ width → count ≤ state.heap.size →
    Controller.Cost.GateProgram.BlockAt program entry (packetReleaseCode width count) →
    ∃ final, Execution program state final count state.liveWords ∧
      final.heap = releasedPacketHeap width count state.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + count) ∧
      final.halted = false ∧ final.reg = state.reg := by
  induction count with
  | zero =>
    intro state entry position running fits inside physical
    exact ⟨state, Execution.refl state, rfl, rfl, rfl, by simpa using position, running, rfl⟩
  | succ count ih =>
    intro state entry position running fits inside physical
    have firstAt : program[entry]? = some .release := by
      simpa only [packetReleaseCode, List.replicate_succ, List.getElem?_cons_zero, Nat.add_zero] using
        physical 0 (by simp [packetReleaseCode])
    obtain ⟨middle, first, heap, stack, output, pc, active, regs⟩ :=
      packet_release_cell program state entry position running (by omega) (by omega) firstAt
    have tailAt : Controller.Cost.GateProgram.BlockAt program (entry + 1) (packetReleaseCode width count) := by
      have split : packetReleaseCode width (count + 1) = [.release] ++ packetReleaseCode width count := by
        simp [packetReleaseCode, List.replicate_succ]
      rw [split] at physical
      simpa using Controller.Cost.GateProgram.BlockAt.suffix program entry [.release]
        (packetReleaseCode width count) physical
    obtain ⟨final, rest, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalRegs⟩ :=
      ih middle (entry + 1) pc active (by omega) (by rw [heap, Array.size_pop]; omega) tailAt
    have live : middle.liveWords ≤ state.liveWords := by
      unfold State.liveWords
      rw [heap, stack, output, Array.size_pop]
      omega
    refine ⟨final, ?_, ?_, finalStack.trans stack, finalOutput.trans output, ?_, finalRunning, finalRegs.trans regs⟩
    · simpa only [Nat.add_comm count 1, Nat.max_eq_left live] using first.append rest
    · rw [finalHeap, heap]; rfl
    · convert finalPC using 1 <;> congr 1 <;> omega

/-- Empty the actual allocated heap by fetched releases, retaining the complete
saved dependency packet, original packet, and caller suffix on the stack. -/
theorem packet_release_execution (program : Program width 8) (entry : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (fits : entry + state.heap.size < 2 ^ width)
    (physical : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt program entry
      (packetReleaseCode width state.heap.size)) :
    ∃ final, Execution program state final state.heap.size state.liveWords ∧
      final.heap = #[] ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + state.heap.size) ∧ final.halted = false ∧ final.reg = state.reg := by
  let low := markerNarrow state
  let view := Controller.Cost.ForestZeroCallerWiden.lowerProgram program
  have block := Controller.Cost.ForestZeroCallerWiden.lower_block program entry
    (packetReleaseCode width state.heap.size) physical
  obtain ⟨last, trace, heap, stack, output, pc, active, regs⟩ :=
    packet_release_low_execution view state.heap.size low entry position running fits (Nat.le_refl _) block
  have lifted := Controller.Cost.ForestZeroCallerWiden.execution program low last state.heap.size
    low.liveWords trace active state.reg
  have sourceLive : low.liveWords + 4 = state.liveWords := by simp only [low, markerNarrow, State.liveWords]; omega
  let final := Controller.Cost.RegisterWiden.widenState last state.reg
  refine ⟨final, ?_, ?_, stack, output, pc, active, ?_⟩
  · rw [markerWidenNarrow] at lifted
    simpa only [sourceLive] using lifted
  · change last.heap = #[]
    apply Array.size_eq_zero_iff.mp
    rw [heap]
    change (releasedPacketHeap width state.heap.size state.heap).size = 0
    rw [releasedPacketHeap_size _ _ (Nat.le_refl _)]
    exact Nat.sub_self _
  · funext register
    by_cases small : register.val < 4
    · simp only [final, Controller.Cost.RegisterWiden.widenState, small, dite_true, regs, low, markerNarrow]
      congr 1
    · exact Controller.Cost.RegisterWiden.widenState_high last state.reg register (by omega)

/-- The cold entry is reached by two fetched instructions, including the zero
flag write. Relocation is a proof of this continuation, not a state reset. -/
theorem cold_handoff_execution (program : Program width 8) (entry target : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (fits : entry + 2 < 2 ^ width)
    (firstAt : program[entry]? = some (.constant 6 (word width 0)))
    (secondAt : program[entry + 1]? = some (.branchZero 6 (word width target))) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width target ∧ final.halted = false ∧ final.reg 6 = word width 0 ∧
      (∀ register : Fin 8, register ≠ 6 → final.reg register = state.reg register) := by
  let middle := state.advance.put 6 (word width 0)
  let final := { middle.advance with pc := word width target }
  have middlePC : middle.pc = word width (entry + 1) := referenceAdvancePC state entry position (by omega)
  have first : programStep program state = some middle := by
    rw [fetched program state entry (.constant 6 (word width 0)) position (by omega) firstAt]
    simp [step, running, middle]
  have second : programStep program middle = some final := by
    rw [fetched program middle (entry + 1) (.branchZero 6 (word width target)) middlePC (by omega) secondAt]
    simp [step, middle, final, State.advance, State.put, running, word]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, rfl, ?_⟩
  · simpa only [final, middle, State.liveWords, State.advance, State.put, Nat.max_self, Nat.reduceAdd] using
      Execution.cons first (Execution.cons second (Execution.refl final))
  · intro register notFlag
    simp only [final, middle, State.advance, State.put, ite_eq_right notFlag]

private theorem allocatedHeap_append (heap : Array (Word width)) (first second : Word width)
    (rest : List (Word width)) :
    (heap.push first).push second ++ rest.toArray = heap ++ (first :: second :: rest).toArray := by
  have expansion : (first :: second :: rest).toArray = #[first] ++ (#[second] ++ rest.toArray) := by
    rw [List.toArray_cons first (second :: rest), List.toArray_cons second rest]
  rw [expansion]
  simp only [Array.push_eq_append, Array.append_assoc]

private theorem literalWords_append (first second : Word width)
    (left right : List (Word width)) :
    (first :: second :: left).toArray ++ right.toArray =
      (first :: second :: (left ++ right)).toArray := by
  rw [List.append_toArray]
  rfl


def dependencyDirectoryCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 2 (word width done), .allocate 1, .load 0 4,
    .add 0 0 3, .add 0 0 0, .add 1 1 0, .allocate 1,
    .add 4 4 5, .add 2 2 7, .branchZero 6 (word width entry)]

def dependencyBoundaries (width pointer : Nat) : List Nat → List (Word width)
  | [] => []
  | arity :: rest => word width pointer :: word width (pointer + 2 * (arity + 1)) ::
      dependencyBoundaries width (pointer + 2 * (arity + 1)) rest

private theorem dependency_directory_iteration (program : Program width 8)
    (entry done pointer cursor count arity : Nat) (state : State width 8)
    (physical : ∀ position : Fin 10,
      program[entry + position.val]? = (dependencyDirectoryCode width entry done)[position.val]?)
    (codeFits : entry + 10 < 2 ^ width) (positive : 0 < count)
    (countFits : count < 2 ^ width) (cursorFits : cursor + 2 < 2 ^ width)
    (pointerFits : pointer + 2 * (arity + 1) < 2 ^ width)
    (room : state.heap.size + 2 ≤ 2 ^ width)
    (sourceBound : cursor < state.heap.size) (sourceCell : state.heap[cursor]'sourceBound = word width arity)
    (position : state.pc = word width entry) (running : state.halted = false)
    (pointerHeld : state.reg 1 = word width pointer) (countHeld : state.reg 2 = word width count)
    (one : state.reg 3 = word width 1) (cursorHeld : state.reg 4 = word width cursor)
    (two : state.reg 5 = word width 2) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final, Execution program state final 10 (state.liveWords + 2) ∧
      final.heap = (state.heap.push (word width pointer)).push (word width (pointer + 2 * (arity + 1))) ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width entry ∧
      final.halted = false ∧ final.reg 1 = word width (pointer + 2 * (arity + 1)) ∧
      final.reg 2 = word width (count - 1) ∧ final.reg 4 = word width (cursor + 2) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 → register ≠ 4 →
        final.reg register = state.reg register) := by
  let s1 := state.advance
  let s2 := { s1.advance with heap := state.heap.push (word width pointer) }
  let s3 := s2.advance.put 0 (word width arity)
  let s4 := s3.advance.put 0 (word width (arity + 1))
  let s5 := s4.advance.put 0 (word width (2 * (arity + 1)))
  let s6 := s5.advance.put 1 (word width (pointer + 2 * (arity + 1)))
  let s7 := { s6.advance with heap := (state.heap.push (word width pointer)).push (word width (pointer + 2 * (arity + 1))) }
  let s8 := s7.advance.put 4 (word width (cursor + 2))
  let s9 := s8.advance.put 2 (word width (count - 1))
  let final := { s9.advance with pc := word width entry }
  have pc1 : s1.pc = word width (entry + 1) := referenceAdvancePC state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    change s5.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5 (entry + 5) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 7) := by
    change s6.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6 (entry + 6) pc6 (by omega)
  have pc8 : s8.pc = word width (entry + 8) := by
    change s7.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7 (entry + 7) pc7 (by omega)
  have pc9 : s9.pc = word width (entry + 9) := by
    change s8.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8 (entry + 8) pc8 (by omega)
  have valuePointer : (word width pointer).val = pointer := Nat.mod_eq_of_lt (by omega)
  have valueCursor : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have valueArity : (word width arity).val = arity := Nat.mod_eq_of_lt (by omega)
  have valueNextArity : (word width (arity + 1)).val = arity + 1 := Nat.mod_eq_of_lt (by omega)
  have valueDouble : (word width (2 * (arity + 1))).val = 2 * (arity + 1) := Nat.mod_eq_of_lt (by omega)
  have valueOne : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have valueTwo : (word width 2).val = 2 := Nat.mod_eq_of_lt (by omega)
  have firstRoom : state.heap.size < 2 ^ width := by omega
  have secondRoom : state.heap.size + 1 < 2 ^ width := by omega
  have negativeFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have addCount : word width ((word width count).val + (word width (2 ^ width - 1)).val) = word width (count - 1) := by
    rw [show (word width count).val = count from Nat.mod_eq_of_lt countFits,
      show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt negativeFits]
    exact marker_word_decrement count positive countFits
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.branchZero 2 (word width done)) position (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨0, by decide⟩)]
    simp [step, running, countHeld, word, Nat.mod_eq_of_lt countFits, show count ≠ 0 by omega, s1]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.allocate 1) pc1 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨1, by decide⟩)]
    simp [step, s1, State.advance, running, firstRoom, pointerHeld, s2]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 0 4) pc2 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨2, by decide⟩)]
    simp [step, s2, s1, State.advance, running, cursorHeld, valueCursor, Array.size_push,
      show cursor < state.heap.size + 1 by omega, Array.getElem_push_lt sourceBound, sourceCell, s3]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.add 0 0 3) pc3 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.advance, State.put, running, one, valueArity, valueOne]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 0 0 0) pc4 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨4, by decide⟩)]
    have doubled : arity + 1 + (arity + 1) = 2 * (arity + 1) := by omega
    simp [step, s5, s4, s3, s2, s1, State.advance, State.put, running, valueNextArity, doubled]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.add 1 1 0) pc5 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨5, by decide⟩)]
    simp [step, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, pointerHeld, valuePointer, valueDouble]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) (.allocate 1) pc6 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨6, by decide⟩)]
    simp [step, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running,
      Array.size_push, secondRoom]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (entry + 7) (.add 4 4 5) pc7 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨7, by decide⟩)]
    simp [step, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running,
      cursorHeld, two, valueCursor, valueTwo]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (entry + 8) (.add 2 2 7) pc8 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨8, by decide⟩)]
    simp only [step, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, show (2 : Fin 8) ≠ 4 by decide, show (2 : Fin 8) ≠ 1 by decide, show (2 : Fin 8) ≠ 0 by decide,
      show (7 : Fin 8) ≠ 4 by decide, show (7 : Fin 8) ≠ 1 by decide, show (7 : Fin 8) ≠ 0 by decide,
      countHeld, decrement]
    rw [addCount]
    simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
  have t9 : programStep program s9 = some final := by
    rw [fetched program s9 (entry + 9) (.branchZero 6 (word width entry)) pc9 (by omega)
      (by simpa [dependencyDirectoryCode] using physical ⟨9, by decide⟩)]
    simp [step, final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, zero, word]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3
      (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7
      (Execution.cons t8 (Execution.cons t9 (Execution.refl final))))))))))
    convert trace using 1 <;>
      simp only [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords,
        State.advance, State.put, Array.size_push] <;> omega
  · simp [final, s9, s8, s7, s6, State.advance, State.put]
  · rfl
  · simp [final, s9, s8, State.advance, State.put]
  · intro register notTemp notPointer notCount notCursor
    simp [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put,
      notTemp, notPointer, notCount, notCursor]

private theorem dependencyBoundaries_length (pointer : Nat) (arities : List Nat) :
    (dependencyBoundaries width pointer arities).length = 2 * arities.length := by
  induction arities generalizing pointer with
  | nil => rfl
  | cons arity rest ih =>
    simp only [dependencyBoundaries, List.length_cons, ih]
    omega

def dependencySpan (arities : List Nat) : Nat :=
  2 * (arities.map (fun arity => arity + 1)).sum

private theorem dependencySpan_cons (arity : Nat) (rest : List Nat) :
    dependencySpan (arity :: rest) = 2 * (arity + 1) + dependencySpan rest := by
  simp [dependencySpan, Nat.mul_add]

-- The whole driver uses the same entry for every original row. Its source cells
-- remain at cursor+2*i while appended directory cells are charged separately.
-- Induction arguments are pointer,cursor,state; physical source-cell premises
-- are extracted from the original raw arity stream before this theorem is used.
-- For a nonempty suffix, directory_iteration supplies the ten fetched steps.
-- The recursive call uses heap.push(pointer).push(nextPointer), and the original
-- arity cells are preserved by two getElem_push_lt rewrites. No runtime row list
-- is allocated or substituted: the list below describes the original metadata.
theorem dependency_directory_execution (program : Program width 8)
    (entry done : Nat) (arities : List Nat) (pointer cursor : Nat) (state : State width 8)
    (physical : ∀ position : Fin 10,
      program[entry + position.val]? = (dependencyDirectoryCode width entry done)[position.val]?)
    (codeFits : entry + 10 < 2 ^ width)
    (countFits : arities.length < 2 ^ width)
    (cursorFits : cursor + 2 * arities.length < 2 ^ width)
    (pointerFits : pointer + dependencySpan arities < 2 ^ width)
    (room : state.heap.size + 2 * arities.length ≤ 2 ^ width)
    (stored : ∀ index : Fin arities.length,
      state.heap[cursor + 2 * index.val]? = some (word width arities[index]))
    (position : state.pc = word width entry) (running : state.halted = false)
    (pointerHeld : state.reg 1 = word width pointer)
    (countHeld : state.reg 2 = word width arities.length)
    (one : state.reg 3 = word width 1) (cursorHeld : state.reg 4 = word width cursor)
    (two : state.reg 5 = word width 2) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final, Execution program state final (10 * arities.length + 1)
        (state.liveWords + 2 * arities.length) ∧
      final.heap = state.heap ++ (dependencyBoundaries width pointer arities).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width done ∧
      final.halted = false ∧ final.reg 1 = word width (pointer + dependencySpan arities) ∧
      final.reg 2 = word width 0 ∧ final.reg 4 = word width (cursor + 2 * arities.length) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 → register ≠ 4 →
        final.reg register = state.reg register) := by
  induction arities generalizing pointer cursor state with
  | nil =>
    let final := { state.advance with pc := word width done }
    have first : programStep program state = some final := by
      rw [fetched program state entry (.branchZero 2 (word width done)) position (by omega)
        (by simpa [dependencyDirectoryCode] using physical ⟨0, by decide⟩)]
      simp [step, final, running, countHeld, word]
    refine ⟨final, ?_, ?_, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_⟩
    · simpa [final, State.liveWords, State.advance] using Execution.cons first (Execution.refl final)
    · simp [final, State.advance, dependencyBoundaries]
    · simpa [final, State.advance, dependencySpan] using pointerHeld
    · exact countHeld
    · simpa [final, State.advance] using cursorHeld
    · intro register _ _ _ _; rfl
  | cons arity rest ih =>
    have firstCell := stored ⟨0, by simp⟩
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at firstCell
    obtain ⟨sourceBound, sourceCell⟩ := Array.getElem?_eq_some_iff.mp firstCell
    obtain ⟨middle, firstTrace, middleHeap, middleStack, middleOutput, middlePC,
      middleRunning, middlePointer, middleCount, middleCursor, middleFrame⟩ :=
      dependency_directory_iteration program entry done pointer cursor (rest.length + 1) arity state
        physical codeFits (by omega) (by simpa using countFits)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [dependencySpan_cons] at pointerFits; omega)
        (by simp only [List.length_cons] at room; omega) sourceBound sourceCell position running
        pointerHeld (by simpa using countHeld) one cursorHeld two zero decrement
    have retained : ∀ index : Fin rest.length,
        middle.heap[(cursor + 2) + 2 * index.val]? = some (word width rest[index]) := by
      intro index
      have original := stored ⟨index.val + 1, by simpa using index.isLt⟩
      simp only [List.getElem_cons_succ] at original
      have addressEq : (cursor + 2) + 2 * index.val = cursor + 2 * (index.val + 1) := by omega
      rw [addressEq, middleHeap]
      obtain ⟨inside, cell⟩ := Array.getElem?_eq_some_iff.mp original
      apply Array.getElem?_eq_some_iff.mpr
      refine ⟨by simp only [Array.size_push]; omega, ?_⟩
      rw [Array.getElem_push_lt (by simpa only [Array.size_push] using Nat.lt_succ_of_lt inside),
        Array.getElem_push_lt inside]
      have selected : (arity :: rest).get (⟨index.val + 1, by simpa using index.isLt⟩ : Fin (arity :: rest).length) =
          rest.get index := List.get_cons_succ
      change state.heap[cursor + 2 * (index.val + 1)]'inside =
        word width ((arity :: rest).get (⟨index.val + 1, by simpa using index.isLt⟩ : Fin (arity :: rest).length)) at cell
      rw [selected] at cell
      exact cell
    have middleSize : middle.heap.size = state.heap.size + 2 := by simp [middleHeap]
    have middleLive : middle.liveWords = state.liveWords + 2 := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]; omega
    obtain ⟨final, restTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      finalPointer, finalCount, finalCursor, finalFrame⟩ :=
      ih (pointer + 2 * (arity + 1)) (cursor + 2) middle
        (by simp only [List.length_cons] at countFits; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simpa only [dependencySpan_cons, Nat.add_assoc] using pointerFits)
        (by simp only [middleSize, List.length_cons] at *; omega)
        retained middlePC middleRunning middlePointer (by simpa using middleCount)
        ((middleFrame 3 (by decide) (by decide) (by decide) (by decide)).trans one)
        middleCursor
        ((middleFrame 5 (by decide) (by decide) (by decide) (by decide)).trans two)
        ((middleFrame 6 (by decide) (by decide) (by decide) (by decide)).trans zero)
        ((middleFrame 7 (by decide) (by decide) (by decide) (by decide)).trans decrement)
    refine ⟨final, ?_, ?_, finalStack.trans middleStack, finalOutput.trans middleOutput,
      finalPC, finalRunning, ?_, finalCount, ?_, ?_⟩
    · convert firstTrace.append restTrace using 1 <;>
        simp only [middleLive, List.length_cons] <;> omega
    · rw [finalHeap, middleHeap]
      change _ = state.heap ++ (_ :: _ :: _).toArray
      exact allocatedHeap_append _ _ _ _
    · simpa only [dependencySpan_cons, Nat.add_assoc] using finalPointer
    · have scalar : (cursor + 2) + 2 * rest.length = cursor + 2 * (arity :: rest).length := by
        simp only [List.length_cons]; omega
      simpa only [scalar] using finalCursor
    · intro register a b c d
      exact (finalFrame register a b c d).trans (middleFrame register a b c d)

-- Physical inner slice of dependencyLiteralCode at entry+5..11.
-- The labels below are original child source words; neither sorting nor dedup
-- occurs during serialization. r4 is temporary, its old arity cursor is on stack.
def dependencyChildWords (width : Nat) : List Nat → List (Word width)
  | [] => []
  | child :: rest => word width child :: word width 1 :: dependencyChildWords width rest

private theorem dependency_child_iteration (program : Program width 8)
    (entry done cursor count child : Nat) (state : State width 8)
    (physical : ∀ position : Fin 7, program[entry + position.val]? =
      (#[.branchZero 0 (word width done), .load 4 5, .allocate 4, .allocate 3,
         .add 5 5 3, .add 0 0 7, .branchZero 6 (word width entry)] : Program width 8)[position.val]?)
    (codeFits : entry + 7 < 2 ^ width) (positive : 0 < count)
    (countFits : count < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (room : state.heap.size + 2 ≤ 2 ^ width)
    (sourceBound : cursor < state.heap.size) (sourceCell : state.heap[cursor]'sourceBound = word width child)
    (position : state.pc = word width entry) (running : state.halted = false)
    (countHeld : state.reg 0 = word width count) (one : state.reg 3 = word width 1)
    (cursorHeld : state.reg 5 = word width cursor) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final, Execution program state final 7 (state.liveWords + 2) ∧
      final.heap = (state.heap.push (word width child)).push (word width 1) ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width entry ∧
      final.halted = false ∧ final.reg 0 = word width (count - 1) ∧
      final.reg 5 = word width (cursor + 1) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 4 → register ≠ 5 →
        final.reg register = state.reg register) := by
  let s1 := state.advance
  let s2 := s1.advance.put 4 (word width child)
  let s3 := { s2.advance with heap := state.heap.push (word width child) }
  let s4 := { s3.advance with heap := (state.heap.push (word width child)).push (word width 1) }
  let s5 := s4.advance.put 5 (word width (cursor + 1))
  let s6 := s5.advance.put 0 (word width (count - 1))
  let final := { s6.advance with pc := word width entry }
  have pc1 : s1.pc = word width (entry + 1) := referenceAdvancePC state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    change s5.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5 (entry + 5) pc5 (by omega)
  have countNonzero : word width count ≠ word width 0 := by
    intro equal
    have scalar := congrArg Fin.val equal
    simp only [word, Nat.mod_eq_of_lt countFits, Nat.zero_mod] at scalar
    omega
  have valueCursor : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have valueOne : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have addCount : word width ((word width count).val + (word width (2 ^ width - 1)).val) =
      word width (count - 1) := by
    have countValue : (word width count).val = count := Nat.mod_eq_of_lt countFits
    have maskValue : (word width (2 ^ width - 1)).val = 2 ^ width - 1 := Nat.mod_eq_of_lt (by omega)
    rw [countValue, maskValue]
    exact marker_word_decrement count positive countFits
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.branchZero 0 (word width done)) position (by omega)
      (by simpa using physical ⟨0, by decide⟩)]
    have countNe : word width count ≠ (0 : Word width) := countNonzero
    simp [step, s1, running, countHeld, countNe]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.load 4 5) pc1 (by omega)
      (by simpa using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running, cursorHeld, valueCursor, sourceBound, sourceCell]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.allocate 4) pc2 (by omega)
      (by simpa using physical ⟨2, by decide⟩)]
    have firstRoom : state.heap.size < 2 ^ width := by omega
    simp [step, s3, s2, s1, State.advance, State.put, running, firstRoom]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.allocate 3) pc3 (by omega)
      (by simpa using physical ⟨3, by decide⟩)]
    have secondRoom : state.heap.size + 1 < 2 ^ width := by omega
    simp [step, s4, s3, s2, s1, State.advance, State.put, running, Array.size_push, secondRoom, one]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 5 5 3) pc4 (by omega)
      (by simpa using physical ⟨4, by decide⟩)]
    simp [step, s5, s4, s3, s2, s1, State.advance, State.put, running,
      cursorHeld, one, valueCursor, valueOne]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.add 0 0 7) pc5 (by omega)
      (by simpa using physical ⟨5, by decide⟩)]
    simp only [step, s5, s4, s3, s2, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, show (0 : Fin 8) ≠ 5 by decide, show (0 : Fin 8) ≠ 4 by decide,
      show (7 : Fin 8) ≠ 5 by decide, show (7 : Fin 8) ≠ 4 by decide, countHeld, decrement]
    rw [addCount]
    simp only [s6, s5, s4, s3, s2, s1, State.advance, State.put, running]
  have t6 : programStep program s6 = some final := by
    rw [fetched program s6 (entry + 6) (.branchZero 6 (word width entry)) pc6 (by omega)
      (by simpa using physical ⟨6, by decide⟩)]
    simp [step, final, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, zero, word]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3
      (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.refl final)))))))
    convert trace using 1 <;>
      simp only [final, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_push] <;> omega
  · simp [final, s6, State.advance, State.put]
  · simp [final, s6, s5, State.advance, State.put]
  · intro register a b c
    simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put, a, b, c]

theorem dependency_child_execution (program : Program width 8) (entry done : Nat)
    (children : List Nat) (cursor : Nat) (state : State width 8)
    (physical : ∀ position : Fin 7, program[entry + position.val]? =
      (#[.branchZero 0 (word width done), .load 4 5, .allocate 4, .allocate 3,
         .add 5 5 3, .add 0 0 7, .branchZero 6 (word width entry)] : Program width 8)[position.val]?)
    (codeFits : entry + 7 < 2 ^ width) (countFits : children.length < 2 ^ width)
    (cursorFits : cursor + children.length < 2 ^ width)
    (room : state.heap.size + 2 * children.length ≤ 2 ^ width)
    (stored : ∀ index : Fin children.length,
      state.heap[cursor + index.val]? = some (word width children[index]))
    (position : state.pc = word width entry) (running : state.halted = false)
    (countHeld : state.reg 0 = word width children.length) (one : state.reg 3 = word width 1)
    (cursorHeld : state.reg 5 = word width cursor) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final, Execution program state final (7 * children.length + 1)
        (state.liveWords + 2 * children.length) ∧
      final.heap = state.heap ++ (dependencyChildWords width children).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width done ∧
      final.halted = false ∧ final.reg 0 = word width 0 ∧
      final.reg 5 = word width (cursor + children.length) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 4 → register ≠ 5 →
        final.reg register = state.reg register) := by
  induction children generalizing cursor state with
  | nil =>
    let final := { state.advance with pc := word width done }
    have first : programStep program state = some final := by
      rw [fetched program state entry (.branchZero 0 (word width done)) position (by omega)
        (by simpa using physical ⟨0, by decide⟩)]
      simp [step, final, running, countHeld, word]
    refine ⟨final, ?_, ?_, rfl, rfl, rfl, running, countHeld, ?_, ?_⟩
    · simpa [final, State.liveWords, State.advance] using Execution.cons first (Execution.refl final)
    · simp [final, State.advance, dependencyChildWords]
    · simpa [final, State.advance] using cursorHeld
    · intro register _ _ _; rfl
  | cons child rest ih =>
    have firstCell := stored ⟨0, by simp⟩
    simp only [Nat.add_zero, List.getElem_cons_zero] at firstCell
    obtain ⟨sourceBound, sourceCell⟩ := Array.getElem?_eq_some_iff.mp firstCell
    obtain ⟨middle, firstTrace, middleHeap, middleStack, middleOutput, middlePC,
      middleRunning, middleCount, middleCursor, middleFrame⟩ :=
      dependency_child_iteration program entry done cursor (rest.length + 1) child state
        physical codeFits (by omega) (by simpa using countFits) (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at room; omega) sourceBound sourceCell position running
        (by simpa using countHeld) one cursorHeld zero decrement
    have retained : ∀ index : Fin rest.length,
        middle.heap[(cursor + 1) + index.val]? = some (word width rest[index]) := by
      intro index
      have original := stored ⟨index.val + 1, by simpa using index.isLt⟩
      simp only [List.getElem_cons_succ] at original
      have addressEq : (cursor + 1) + index.val = cursor + (index.val + 1) := by omega
      rw [addressEq, middleHeap]
      obtain ⟨inside, cell⟩ := Array.getElem?_eq_some_iff.mp original
      apply Array.getElem?_eq_some_iff.mpr
      refine ⟨by simp only [Array.size_push]; omega, ?_⟩
      rw [Array.getElem_push_lt (by simpa only [Array.size_push] using Nat.lt_succ_of_lt inside),
        Array.getElem_push_lt inside]
      have selected : (child :: rest).get (⟨index.val + 1, by simpa using index.isLt⟩ : Fin (child :: rest).length) =
          rest.get index := List.get_cons_succ
      change state.heap[cursor + (index.val + 1)]'inside =
        word width ((child :: rest).get (⟨index.val + 1, by simpa using index.isLt⟩ : Fin (child :: rest).length)) at cell
      rw [selected] at cell
      exact cell
    have middleSize : middle.heap.size = state.heap.size + 2 := by simp [middleHeap]
    have middleLive : middle.liveWords = state.liveWords + 2 := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]; omega
    obtain ⟨final, restTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      finalCount, finalCursor, finalFrame⟩ := ih (cursor + 1) middle
        (by simp only [List.length_cons] at countFits; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [middleSize, List.length_cons] at *; omega)
        retained middlePC middleRunning (by simpa using middleCount)
        ((middleFrame 3 (by decide) (by decide) (by decide)).trans one) middleCursor
        ((middleFrame 6 (by decide) (by decide) (by decide)).trans zero)
        ((middleFrame 7 (by decide) (by decide) (by decide)).trans decrement)
    refine ⟨final, ?_, ?_, finalStack.trans middleStack, finalOutput.trans middleOutput,
      finalPC, finalRunning, finalCount, ?_, ?_⟩
    · convert firstTrace.append restTrace using 1 <;> simp only [middleLive, List.length_cons] <;> omega
    · rw [finalHeap, middleHeap]
      change _ = state.heap ++ (_ :: _ :: _).toArray
      exact allocatedHeap_append _ _ _ _
    · have scalar : (cursor + 1) + rest.length = cursor + (child :: rest).length := by
        simp only [List.length_cons]; omega
      simpa only [scalar] using finalCursor
    · intro register a b c
      exact (finalFrame register a b c).trans (middleFrame register a b c)


/-- Original negative-parent and positive-child pairs are copied in source order. -/
def dependencyLiteralCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 2 (word width done), .allocate 1, .allocate 6, .load 0 4, .push 4,
    .branchZero 0 (word width (entry + 12)), .load 4 5, .allocate 4, .allocate 3,
    .add 5 5 3, .add 0 0 7, .branchZero 6 (word width (entry + 5)),
    .pop 4, .add 4 4 3, .add 4 4 3, .add 1 1 3, .add 2 2 7,
    .branchZero 6 (word width entry)]

private theorem dependency_literal_prefix (program : Program width 8)
    (entry done parent rows cursor arity : Nat) (state : State width 8)
    (physical : ∀ position : Fin 18,
      program[entry + position.val]? = (dependencyLiteralCode width entry done)[position.val]?)
    (codeFits : entry + 18 < 2 ^ width) (positive : 0 < rows)
    (rowsFits : rows < 2 ^ width) (room : state.heap.size + 2 ≤ 2 ^ width)
    (sourceBound : cursor < state.heap.size) (sourceCell : state.heap[cursor]'sourceBound = word width arity)
    (position : state.pc = word width entry) (running : state.halted = false)
    (parentHeld : state.reg 1 = word width parent) (rowsHeld : state.reg 2 = word width rows)
    (cursorHeld : state.reg 4 = word width cursor) (cursorFits : cursor < 2 ^ width)
    (zero : state.reg 6 = word width 0) :
    ∃ final, Execution program state final 5 (state.liveWords + 3) ∧
      final.heap = (state.heap.push (word width parent)).push (word width 0) ∧
      final.stack = word width cursor :: state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 5) ∧ final.halted = false ∧
      final.reg 0 = word width arity ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  let s1 := state.advance
  let s2 := { s1.advance with heap := state.heap.push (word width parent) }
  let s3 := { s2.advance with heap := (state.heap.push (word width parent)).push (word width 0) }
  let s4 := s3.advance.put 0 (word width arity)
  let final := { s4.advance with stack := word width cursor :: state.stack }
  have pc1 : s1.pc = word width (entry + 1) := referenceAdvancePC state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : final.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have rowsNonzero : word width rows ≠ word width 0 := by
    intro equal
    have scalar := congrArg Fin.val equal
    simp only [word, Nat.mod_eq_of_lt rowsFits, Nat.zero_mod] at scalar
    omega
  have nonzero : word width rows ≠ (0 : Word width) := rowsNonzero
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.branchZero 2 (word width done)) position (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨0, by decide⟩)]
    simp [step, s1, running, rowsHeld, nonzero]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.allocate 1) pc1 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨1, by decide⟩)]
    have firstRoom : state.heap.size < 2 ^ width := by omega
    simp [step, s2, s1, State.advance, running, parentHeld, firstRoom]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.allocate 6) pc2 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨2, by decide⟩)]
    have secondRoom : state.heap.size + 1 < 2 ^ width := by omega
    simp [step, s3, s2, s1, State.advance, running, zero, Array.size_push, secondRoom]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.load 0 4) pc3 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨3, by decide⟩)]
    have cursorValue : (word width cursor).val = cursor := Nat.mod_eq_of_lt cursorFits
    have valid : cursor < ((state.heap.push (word width parent)).push (word width 0)).size := by
      simp only [Array.size_push]; omega
    have retained : ((state.heap.push (word width parent)).push (word width 0))[cursor]'valid =
        word width arity := by
      rw [Array.getElem_push_lt (by simpa using Nat.lt_succ_of_lt sourceBound),
        Array.getElem_push_lt sourceBound]
      exact sourceCell
    simp only [step, s4, s3, s2, s1, State.advance, running, Bool.false_eq_true,
      ite_false, cursorHeld, cursorValue, dite_eq_left valid, retained]

  have t4 : programStep program s4 = some final := by
    rw [fetched program s4 (entry + 4) (.push 4) pc4 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨4, by decide⟩)]
    simp [step, final, s4, s3, s2, s1, State.advance, State.put, running, cursorHeld]
  refine ⟨final, ?_, rfl, rfl, rfl, pc5, running, ?_, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.refl final)))))
    convert trace using 1 <;>
      simp only [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put,
        Array.size_push, List.length_cons] <;> omega
  · simp [final, s4, State.advance, State.put]
  · intro register notTemp
    simp only [final, s4, s3, s2, s1, State.advance, State.put, ite_eq_right notTemp]

private theorem dependency_literal_return (program : Program width 8)
    (entry done parent rows cursor : Nat) (suffix : List (Word width)) (state : State width 8)
    (physical : ∀ position : Fin 18,
      program[entry + position.val]? = (dependencyLiteralCode width entry done)[position.val]?)
    (codeFits : entry + 18 < 2 ^ width) (positive : 0 < rows)
    (rowsFits : rows < 2 ^ width) (parentFits : parent + 1 < 2 ^ width)
    (cursorFits : cursor + 2 < 2 ^ width)
    (position : state.pc = word width (entry + 12)) (running : state.halted = false)
    (saved : state.stack = word width cursor :: suffix)
    (parentHeld : state.reg 1 = word width parent) (rowsHeld : state.reg 2 = word width rows)
    (one : state.reg 3 = word width 1) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 1 = word width (parent + 1) ∧ final.reg 2 = word width (rows - 1) ∧
      final.reg 4 = word width (cursor + 2) ∧
      (∀ register : Fin 8, register ≠ 1 → register ≠ 2 → register ≠ 4 →
        final.reg register = state.reg register) := by
  let s1 := { state.advance.put 4 (word width cursor) with stack := suffix }
  let s2 := s1.advance.put 4 (word width (cursor + 1))
  let s3 := s2.advance.put 4 (word width (cursor + 2))
  let s4 := s3.advance.put 1 (word width (parent + 1))
  let s5 := s4.advance.put 2 (word width (rows - 1))
  let final := { s5.advance with pc := word width entry }
  have pc1 : s1.pc = word width (entry + 13) := by
    change state.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state (entry + 12) position (by omega)
  have pc2 : s2.pc = word width (entry + 14) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 13) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 15) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 14) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 16) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 15) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 17) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 16) pc4 (by omega)
  have valueCursor : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have valueNext : (word width (cursor + 1)).val = cursor + 1 := Nat.mod_eq_of_lt (by omega)
  have valueParent : (word width parent).val = parent := Nat.mod_eq_of_lt (by omega)
  have valueOne : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have addCount : word width ((word width rows).val + (word width (2 ^ width - 1)).val) =
      word width (rows - 1) := by
    have rowsValue : (word width rows).val = rows := Nat.mod_eq_of_lt rowsFits
    have maskValue : (word width (2 ^ width - 1)).val = 2 ^ width - 1 :=
      Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
    rw [rowsValue, maskValue]
    exact marker_word_decrement rows positive rowsFits
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 12) (.pop 4) position (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨12, by decide⟩)]
    simp [step, s1, running, saved]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 13) (.add 4 4 3) pc1 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨13, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running, one, valueCursor, valueOne]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 14) (.add 4 4 3) pc2 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨14, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running, one, valueNext, valueOne, Nat.add_assoc]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 15) (.add 1 1 3) pc3 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨15, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.advance, State.put, running, parentHeld, one, valueParent, valueOne]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 16) (.add 2 2 7) pc4 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨16, by decide⟩)]
    simp only [step, s4, s3, s2, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, show (2 : Fin 8) ≠ 1 by decide, show (2 : Fin 8) ≠ 4 by decide,
      show (7 : Fin 8) ≠ 1 by decide, show (7 : Fin 8) ≠ 4 by decide, rowsHeld, decrement]
    rw [addCount]
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, running]
  have t5 : programStep program s5 = some final := by
    rw [fetched program s5 (entry + 17) (.branchZero 6 (word width entry)) pc5 (by omega)
      (by simpa [dependencyLiteralCode] using physical ⟨17, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.advance, State.put, running, zero, word]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
    convert trace using 1 <;>
      simp only [final, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put,
        saved, List.length_cons] <;> omega
  · simp [final, s5, s4, State.advance, State.put]
  · simp [final, s5, State.advance, State.put]
  · simp [final, s5, s4, s3, State.advance, State.put]
  · intro register a b c
    simp [final, s5, s4, s3, s2, s1, State.advance, State.put, a, b, c]

private theorem dependencyChildWords_length (children : List Nat) :
    (dependencyChildWords width children).length = 2 * children.length := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp only [dependencyChildWords, List.length_cons, ih]; omega

private theorem dependency_literal_row (program : Program width 8)
    (entry done parent rows rowCursor childCursor : Nat) (children : List Nat) (state : State width 8)
    (physical : ∀ position : Fin 18,
      program[entry + position.val]? = (dependencyLiteralCode width entry done)[position.val]?)
    (codeFits : entry + 18 < 2 ^ width) (positive : 0 < rows)
    (rowsFits : rows < 2 ^ width) (parentFits : parent + 1 < 2 ^ width)
    (rowCursorFits : rowCursor + 2 < 2 ^ width)
    (childCursorFits : childCursor + children.length < 2 ^ width)
    (childCountFits : children.length < 2 ^ width)
    (room : state.heap.size + 2 + 2 * children.length ≤ 2 ^ width)
    (arityCell : state.heap[rowCursor]? = some (word width children.length))
    (childCells : ∀ index : Fin children.length,
      state.heap[childCursor + index.val]? = some (word width children[index]))
    (position : state.pc = word width entry) (running : state.halted = false)
    (parentHeld : state.reg 1 = word width parent) (rowsHeld : state.reg 2 = word width rows)
    (one : state.reg 3 = word width 1) (rowCursorHeld : state.reg 4 = word width rowCursor)
    (childCursorHeld : state.reg 5 = word width childCursor) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final, Execution program state final (12 + 7 * children.length)
        (state.liveWords + 3 + 2 * children.length) ∧
      final.heap = state.heap ++ (word width parent :: word width 0 ::
        dependencyChildWords width children).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width entry ∧
      final.halted = false ∧ final.reg 1 = word width (parent + 1) ∧
      final.reg 2 = word width (rows - 1) ∧ final.reg 4 = word width (rowCursor + 2) ∧
      final.reg 5 = word width (childCursor + children.length) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        register ≠ 4 → register ≠ 5 → final.reg register = state.reg register) := by
  obtain ⟨arityBound, arityValue⟩ := Array.getElem?_eq_some_iff.mp arityCell
  obtain ⟨started, firstTrace, firstHeap, firstStack, firstOutput, firstPC, firstRunning,
    firstCount, firstFrame⟩ := dependency_literal_prefix program entry done parent rows rowCursor
      children.length state physical codeFits positive rowsFits (by omega) arityBound arityValue
      position running parentHeld rowsHeld rowCursorHeld (by omega) zero
  have innerPhysical : ∀ position : Fin 7, program[(entry + 5) + position.val]? =
      (#[.branchZero 0 (word width (entry + 12)), .load 4 5, .allocate 4, .allocate 3,
         .add 5 5 3, .add 0 0 7, .branchZero 6 (word width (entry + 5))] : Program width 8)[position.val]? := by
    intro position
    have cell := physical ⟨5 + position.val, by omega⟩
    fin_cases position <;> simpa [dependencyLiteralCode, Nat.add_assoc] using cell
  have retainedChildren : ∀ index : Fin children.length,
      started.heap[childCursor + index.val]? = some (word width children[index]) := by
    intro index
    have original := childCells index
    obtain ⟨inside, cell⟩ := Array.getElem?_eq_some_iff.mp original
    rw [firstHeap, Array.getElem?_push_lt (by simpa using Nat.lt_succ_of_lt inside)]
    rw [Array.getElem_push_lt inside]
    exact congrArg some cell
  have firstSize : started.heap.size = state.heap.size + 2 := by simp [firstHeap]
  have firstLive : started.liveWords = state.liveWords + 3 := by
    simp only [State.liveWords, firstSize, firstStack, firstOutput, List.length_cons]; omega
  obtain ⟨body, bodyTrace, bodyHeap, bodyStack, bodyOutput, bodyPC, bodyRunning,
    bodyCount, bodyCursor, bodyFrame⟩ := dependency_child_execution program (entry + 5) (entry + 12)
      children childCursor started innerPhysical (by omega) childCountFits childCursorFits
      (by rw [firstSize]; exact room) retainedChildren firstPC firstRunning firstCount
      ((firstFrame 3 (by decide)).trans one) ((firstFrame 5 (by decide)).trans childCursorHeld)
      ((firstFrame 6 (by decide)).trans zero) ((firstFrame 7 (by decide)).trans decrement)
  have bodyLive : body.liveWords = state.liveWords + 3 + 2 * children.length := by
    simp only [State.liveWords, bodyHeap, Array.size_append, List.size_toArray,
      dependencyChildWords_length, firstSize, bodyStack, firstStack, bodyOutput, firstOutput,
      List.length_cons]; omega
  obtain ⟨final, returnTrace, returnHeap, returnStack, returnOutput, returnPC, returnRunning,
    returnParent, returnRows, returnCursor, returnFrame⟩ := dependency_literal_return program entry done
      parent rows rowCursor state.stack body physical codeFits positive rowsFits parentFits rowCursorFits
      bodyPC bodyRunning (bodyStack.trans firstStack)
      ((bodyFrame 1 (by decide) (by decide) (by decide)).trans ((firstFrame 1 (by decide)).trans parentHeld))
      ((bodyFrame 2 (by decide) (by decide) (by decide)).trans ((firstFrame 2 (by decide)).trans rowsHeld))
      ((bodyFrame 3 (by decide) (by decide) (by decide)).trans ((firstFrame 3 (by decide)).trans one))
      ((bodyFrame 6 (by decide) (by decide) (by decide)).trans ((firstFrame 6 (by decide)).trans zero))
      ((bodyFrame 7 (by decide) (by decide) (by decide)).trans ((firstFrame 7 (by decide)).trans decrement))
  refine ⟨final, ?_, ?_, returnStack, returnOutput.trans (bodyOutput.trans firstOutput),
    returnPC, returnRunning, returnParent, returnRows, returnCursor, ?_, ?_⟩
  · convert (firstTrace.append bodyTrace).append returnTrace using 1 <;>
      (try simp only [firstLive, bodyLive]) <;> omega
  · rw [returnHeap, bodyHeap, firstHeap]
    exact allocatedHeap_append _ _ _ _
  · exact (returnFrame 5 (by decide) (by decide) (by decide)).trans bodyCursor
  · intro register a b c d e
    exact (returnFrame register b c d).trans
      ((bodyFrame register a d e).trans (firstFrame register a))

def dependencyLiteralWords (width parent : Nat) : List (List Nat) → List (Word width)
  | [] => []
  | children :: rows => word width parent :: word width 0 ::
      (dependencyChildWords width children ++ dependencyLiteralWords width (parent + 1) rows)

def childTotal (rows : List (List Nat)) : Nat := (rows.map List.length).sum

private theorem dependencyLiteralWords_length (parent : Nat) (rows : List (List Nat)) :
    (dependencyLiteralWords width parent rows).length = 2 * rows.length + 2 * childTotal rows := by
  induction rows generalizing parent with
  | nil => rfl
  | cons children rows ih =>
    simp only [dependencyLiteralWords, List.length_cons, List.length_append,
      dependencyChildWords_length, ih, childTotal, List.map_cons, List.sum_cons]
    omega

-- Whole physical original-row literal stream. The semantic source lists retain
-- order and multiplicities. Their cells are read from the immutable original
-- packet; recursive stored hypotheses are derived from actual append frames.
theorem dependency_literal_execution (program : Program width 8)
    (entry done parent rowCursor childCursor : Nat) (rows : List (List Nat)) (state : State width 8)
    (physical : ∀ position : Fin 18,
      program[entry + position.val]? = (dependencyLiteralCode width entry done)[position.val]?)
    (codeFits : entry + 18 < 2 ^ width) (rowsFits : rows.length < 2 ^ width)
    (parentFits : parent + rows.length < 2 ^ width)
    (rowCursorFits : rowCursor + 2 * rows.length < 2 ^ width)
    (childCursorFits : childCursor + childTotal rows < 2 ^ width)
    (childCountFits : childTotal rows < 2 ^ width)
    (room : state.heap.size + 2 * rows.length + 2 * childTotal rows ≤ 2 ^ width)
    (arities : ∀ index : Fin rows.length,
      state.heap[rowCursor + 2 * index.val]? = some (word width rows[index].length))
    (childrenStored : ∀ index : Fin rows.length, ∀ child : Fin rows[index].length,
      state.heap[childCursor + childTotal (rows.take index.val) + child.val]? = some (word width rows[index][child]))
    (position : state.pc = word width entry) (running : state.halted = false)
    (parentHeld : state.reg 1 = word width parent) (rowsHeld : state.reg 2 = word width rows.length)
    (one : state.reg 3 = word width 1) (rowCursorHeld : state.reg 4 = word width rowCursor)
    (childCursorHeld : state.reg 5 = word width childCursor) (zero : state.reg 6 = word width 0)
    (decrement : state.reg 7 = word width (2 ^ width - 1)) :
    ∃ final peak, Execution program state final (12 * rows.length + 7 * childTotal rows + 1) peak ∧
      peak ≤ state.liveWords + 2 * rows.length + 2 * childTotal rows + 1 ∧
      final.heap = state.heap ++ (dependencyLiteralWords width parent rows).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width done ∧
      final.halted = false ∧ final.reg 1 = word width (parent + rows.length) ∧
      final.reg 2 = word width 0 ∧ final.reg 4 = word width (rowCursor + 2 * rows.length) ∧
      final.reg 5 = word width (childCursor + childTotal rows) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        register ≠ 4 → register ≠ 5 → final.reg register = state.reg register) := by
  induction rows generalizing parent rowCursor childCursor state with
  | nil =>
    let final := { state.advance with pc := word width done }
    have first : programStep program state = some final := by
      rw [fetched program state entry (.branchZero 2 (word width done)) position (by omega)
        (by simpa [dependencyLiteralCode] using physical ⟨0, by decide⟩)]
      simp [step, final, running, rowsHeld, word]
    refine ⟨final, state.liveWords, ?_, by simp [childTotal], ?_, rfl, rfl, rfl,
      running, ?_, rowsHeld, ?_, ?_, ?_⟩
    · simpa [final, State.liveWords, State.advance, childTotal] using Execution.cons first (Execution.refl final)
    · simp [final, State.advance, dependencyLiteralWords]
    · simpa [final, State.advance] using parentHeld
    · simpa [final, State.advance] using rowCursorHeld
    · simpa [final, State.advance, childTotal] using childCursorHeld
    · intro register _ _ _ _ _; rfl
  | cons children rest ih =>
    have totalEq : childTotal (children :: rest) = children.length + childTotal rest := by
      simp [childTotal]
    have firstArity := arities ⟨0, by simp⟩
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at firstArity
    have firstChildren : ∀ child : Fin children.length,
        state.heap[childCursor + child.val]? = some (word width children[child]) := by
      intro child
      have original := childrenStored ⟨0, by simp⟩ child
      simp only [List.take_zero, childTotal, List.map_nil, List.sum_nil, Nat.add_zero] at original
      change state.heap[childCursor + child.val]? = some (word width (children.get child)) at original
      exact original

    obtain ⟨middle, firstTrace, middleHeap, middleStack, middleOutput, middlePC, middleRunning,
      middleParent, middleRows, middleRowCursor, middleChildCursor, middleFrame⟩ :=
      dependency_literal_row program entry done parent (rest.length + 1) rowCursor childCursor
        children state physical codeFits (by omega) (by simpa using rowsFits)
        (by simp only [List.length_cons] at parentFits; omega)
        (by simp only [List.length_cons] at rowCursorFits; omega)
        (by rw [totalEq] at childCursorFits; omega) (by rw [totalEq] at childCountFits; omega)
        (by simp only [List.length_cons] at room; rw [totalEq] at room; omega)
        firstArity firstChildren position running parentHeld (by simpa using rowsHeld)
        one rowCursorHeld childCursorHeld zero decrement
    have retain : ∀ (address : Nat) (value : Word width), state.heap[address]? = some value → middle.heap[address]? = some value := by
      intro address value original
      obtain ⟨inside, cell⟩ := Array.getElem?_eq_some_iff.mp original
      rw [middleHeap, Array.getElem?_append_left inside]
      exact original
    have restArities : ∀ index : Fin rest.length,
        middle.heap[(rowCursor + 2) + 2 * index.val]? = some (word width rest[index].length) := by
      intro index
      have original := arities ⟨index.val + 1, by simpa using index.isLt⟩
      simp only [List.getElem_cons_succ] at original
      have addressEq : (rowCursor + 2) + 2 * index.val = rowCursor + 2 * (index.val + 1) := by omega
      rw [addressEq]
      exact retain _ _ original
    have restChildren : ∀ index : Fin rest.length, ∀ child : Fin rest[index].length,
        middle.heap[(childCursor + children.length) + childTotal (rest.take index.val) + child.val]? =
          some (word width rest[index][child]) := by
      intro index child
      have original := childrenStored ⟨index.val + 1, by simpa using index.isLt⟩ child
      simp only [List.getElem_cons_succ, List.take_succ_cons, childTotal, List.map_cons, List.sum_cons] at original
      have addressEq : (childCursor + children.length) + childTotal (rest.take index.val) + child.val =
          childCursor + (children.length + childTotal (rest.take index.val)) + child.val := by omega
      rw [addressEq]
      exact retain _ _ original
    have middleSize : middle.heap.size = state.heap.size + 2 + 2 * children.length := by
      simp [middleHeap, dependencyChildWords_length]; omega
    have middleLive : middle.liveWords = state.liveWords + 2 + 2 * children.length := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]; omega
    obtain ⟨final, restPeak, restTrace, restPeakBound, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalParent, finalRows, finalRowCursor, finalChildCursor, finalFrame⟩ :=
      ih (parent + 1) (rowCursor + 2) (childCursor + children.length) middle
        (by simp only [List.length_cons] at rowsFits; omega)
        (by simp only [List.length_cons] at parentFits; omega)
        (by simp only [List.length_cons] at rowCursorFits; omega)
        (by rw [totalEq] at childCursorFits; omega)
        (by rw [totalEq] at childCountFits; omega)
        (by rw [middleSize]; simp only [List.length_cons] at room; rw [totalEq] at room; omega)
        restArities restChildren middlePC middleRunning middleParent (by simpa using middleRows)
        ((middleFrame 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans one)
        middleRowCursor middleChildCursor
        ((middleFrame 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans zero)
        ((middleFrame 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans decrement)
    refine ⟨final, max (state.liveWords + 3 + 2 * children.length) restPeak,
      ?_, ?_, ?_, finalStack.trans middleStack, finalOutput.trans middleOutput,
      finalPC, finalRunning, ?_, finalRows, ?_, ?_, ?_⟩
    · convert firstTrace.append restTrace using 1 <;>
        simp only [List.length_cons, totalEq] <;> omega
    · simp only [List.length_cons, totalEq]
      rw [middleLive] at restPeakBound
      omega
    · rw [finalHeap, middleHeap, Array.append_assoc]
      change state.heap ++ ((_ :: _ :: _).toArray ++ _) = state.heap ++ _
      rw [literalWords_append]
      rfl
    · have parentEq : (parent + 1) + rest.length = parent + (children :: rest).length := by
        simp only [List.length_cons]; omega
      rw [parentEq] at finalParent
      exact finalParent
    · have cursorEq : (rowCursor + 2) + 2 * rest.length = rowCursor + 2 * (children :: rest).length := by
        simp only [List.length_cons]; omega
      rw [cursorEq] at finalRowCursor
      exact finalRowCursor
    · simpa only [totalEq, Nat.add_assoc] using finalChildCursor
    · intro register a b c d e
      exact (finalFrame register a b c d e).trans (middleFrame register a b c d e)

-- Exact comparison with the frozen physical source encoder, retaining the
-- original literal order and duplicate occurrences.
private def originalLiteralWords (width : Nat) : Controller.CNF.Clause (Fin n) → List (Word width)
  | [] => []
  | (label, sign) :: rest => word width label.val :: Controller.Horn.MarkStorage.encode width sign ::
      originalLiteralWords width rest

private theorem clauseWords_cons (literal : Fin n × Bool) (rest : Controller.CNF.Clause (Fin n)) :
    Controller.Horn.SourceSerialize.clauseWords (width := width) (literal :: rest) =
      #[word width literal.1.val, Controller.Horn.MarkStorage.encode width literal.2] ++
        Controller.Horn.SourceSerialize.clauseWords rest := by
  apply Array.ext
  · simp only [Controller.Horn.SourceSerialize.clauseWords_size, List.length_cons, Array.size_append]
    simp
    omega
  · intro position leftBound rightBound
    by_cases first : position < 2
    · interval_cases position <;>
        simp [Controller.Horn.SourceSerialize.clauseWords]
    · have tailBound : position - 2 < 2 * rest.length := by
        simp only [Controller.Horn.SourceSerialize.clauseWords_size, List.length_cons] at leftBound
        omega
      have quotient : position / 2 = (position - 2) / 2 + 1 := by omega
      have remainder : position % 2 = (position - 2) % 2 := by omega
      rw [Array.getElem_append_right (by simp; omega)]
      simp only [Controller.Horn.SourceSerialize.clauseWords, Array.getElem_ofFn,
        show (#[word width literal.1.val, Controller.Horn.MarkStorage.encode width literal.2]).size = 2 by rfl,
        quotient, List.getElem_cons_succ, remainder]

private theorem clauseWords_originalLiteralWords (clause : Controller.CNF.Clause (Fin n)) :
    Controller.Horn.SourceSerialize.clauseWords (width := width) clause =
      (originalLiteralWords width clause).toArray := by
  induction clause with
  | nil => apply Array.ext <;> simp [Controller.Horn.SourceSerialize.clauseWords, originalLiteralWords]
  | cons literal rest ih =>
    rw [clauseWords_cons, ih]
    change ([word width literal.1.val, Controller.Horn.MarkStorage.encode width literal.2]).toArray ++
      (originalLiteralWords width rest).toArray =
      (word width literal.1.val :: Controller.Horn.MarkStorage.encode width literal.2 ::
        originalLiteralWords width rest).toArray
    rw [List.append_toArray]
    rfl

private theorem original_positive_words (children : List (Fin n)) :
    originalLiteralWords width (children.map (fun child => (child, true))) =
      dependencyChildWords width (children.map Fin.val) := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp [originalLiteralWords, dependencyChildWords, ih, Controller.Horn.MarkStorage.encode]

private theorem dependency_clause_words (parent : Fin n) (children : List (Fin n)) :
    Controller.Horn.SourceSerialize.clauseWords (width := width)
      (RawDependencyOrder.dependencyClause parent children) =
      (word width parent.val :: word width 0 :: dependencyChildWords width (children.map Fin.val)).toArray := by
  rw [clauseWords_originalLiteralWords]
  simp only [RawDependencyOrder.dependencyClause, originalLiteralWords, original_positive_words,
    Controller.Horn.MarkStorage.encode, Bool.false_eq_true, ite_false]

private theorem sourceWords_literal_rows (parent : Nat)
    (rows : List (List Nat)) (clauses : List (Controller.CNF.Clause (Fin n)))
    (sameLength : clauses.length = rows.length)
    (rowWords : ∀ index (inside : index < rows.length),
      Controller.Horn.SourceSerialize.clauseWords (width := width)
        (clauses[index]'(by omega)) =
      (word width (parent + index) :: word width 0 :: dependencyChildWords width rows[index]).toArray) :
    Controller.Horn.SourceSerialize.sourceWords (width := width) clauses =
      (dependencyLiteralWords width parent rows).toArray := by
  induction rows generalizing parent clauses with
  | nil =>
    have empty : clauses = [] := List.length_eq_zero_iff.mp sameLength
    rw [empty]
    rfl
  | cons children rest ih =>
    cases clauses with
    | nil => simp only [List.length_nil, List.length_cons] at sameLength; omega
    | cons clause clauses =>
      have first := rowWords 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at first
      have tailsLength : clauses.length = rest.length := by
        simp only [List.length_cons] at sameLength; omega
      have tailWords : ∀ index (inside : index < rest.length),
          Controller.Horn.SourceSerialize.clauseWords (width := width) (clauses[index]'(by omega)) =
          (word width ((parent + 1) + index) :: word width 0 :: dependencyChildWords width rest[index]).toArray := by
        intro index inside
        have next := rowWords (index + 1) (by simp only [List.length_cons]; omega)
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 index] using next
      rw [Controller.Horn.SourceSerialize.sourceWords, first, ih (parent + 1) clauses tailsLength tailWords]
      change (_ :: _ :: _).toArray ++ _ = (_ :: _ :: (_ ++ _)).toArray
      exact literalWords_append _ _ _ _

theorem dependency_source_words_exact (graph : UnorderedDAG n) :
    Controller.Horn.SourceSerialize.sourceWords (width := width)
      (RawDependencyOrder.dependencyClauses graph) =
      (dependencyLiteralWords width 0 (List.ofFn (fun parent : Fin graph.nodeCount =>
        (graph.node parent).children.map Fin.val))).toArray := by
  refine sourceWords_literal_rows 0 _ _ ?_ ?_
  · simp [RawDependencyOrder.dependencyClauses]
  · intro index inside
    have bound : index < graph.nodeCount := by simpa only [List.length_ofFn] using inside
    let parent : Fin graph.nodeCount := ⟨index, bound⟩
    simp only [RawDependencyOrder.dependencyClauses, List.getElem_ofFn, Nat.zero_add]
    exact dependency_clause_words parent (graph.node parent).children

-- Counted dependency headers are formed by actual fetched arithmetic.
def dependencyHeaderCode (width : Nat) : Program width 8 :=
  #[.add 1 2 2, .constant 0 (word width 5), .add 1 1 0,
    .constant 0 (word width 0), .allocate 0, .allocate 1, .allocate 1,
    .constant 0 (word width 5), .allocate 0, .allocate 1]



-- Private draft for the released-next full serializer integration.
-- rawSource header 0 is the original row count; header 5 is the relative
-- original child-arity column address. Both come from counted source encoding.
def dependencySetupCode (width sourceBase : Nat) : Program width 8 :=
  #[.constant 2 (word width sourceBase), .load 2 2,
    .constant 4 (word width (sourceBase + 5)), .load 4 4,
    .constant 0 (word width sourceBase), .add 4 4 0,
    .constant 3 (word width 1), .constant 5 (word width 2),
    .constant 6 (word width 0), .constant 7 (word width (2 ^ width - 1))]

-- The directory cursor has reached the original child stream. Save that real
-- cursor in r5, then reload original V and the original arity cursor.
def dependencyTransitionCode (width sourceBase : Nat) : Program width 8 :=
  #[.copy 5 4, .constant 4 (word width (sourceBase + 5)), .load 4 4,
    .constant 0 (word width sourceBase), .add 4 4 0,
    .constant 2 (word width sourceBase), .load 2 2,
    .constant 1 (word width 0)]

def dependencySerializerCode (width entry sourceBase : Nat) : Program width 8 :=
  dependencySetupCode width sourceBase ++ dependencyHeaderCode width ++
    dependencyDirectoryCode width (entry + 20) (entry + 30) ++
    dependencyTransitionCode width sourceBase ++
    dependencyLiteralCode width (entry + 38) (entry + 56)

theorem dependencySerializerCode_size :
    (dependencySerializerCode width entry sourceBase).size = 56 := by
  simp only [dependencySerializerCode, dependencySetupCode, dependencyHeaderCode,
    dependencyDirectoryCode, dependencyTransitionCode, dependencyLiteralCode,
    Array.size_append]
  rfl

-- Required concrete input cells:
-- heap[sourceBase] = word V
-- heap[sourceBase+5] = word(9+4V)
-- heap[sourceBase+9+4V+2i] = word(originalChildren[i].length)
-- heap[sourceBase+9+6V+sum(prefix arities)+j] = word(originalChildren[i][j])
-- These are derived from rawSourcePacket and original constructor lists.
-- Setup10 -> header10 -> directory(10V+1) -> transition8 -> literals(12V+7E+1).
-- Total 22V+7E+30 actual fetched ticks, allocation5+4V+2E,
-- peak initial.liveWords+6+4V+2E (five headers plus at most one temporary word).
-- Final pc=entry+56, caller stack/output unchanged, original heap prefix unchanged.
-- The allocated suffix equals SourceSerialize.heap(dependencyClauses graph),
-- with all directory offsets relative to that suffix, not original heap base.


private theorem dependency_setup_execution (program : Program width 8)
    (entry sourceBase rows arityOffset : Nat) (state : State width 8)
    (physical : ∀ position : Fin 10, program[entry + position.val]? =
      (dependencySetupCode width sourceBase)[position.val]?)
    (codeFits : entry + 10 < 2 ^ width)
    (baseFits : sourceBase + 5 < 2 ^ width)
    (pointerFits : sourceBase + arityOffset < 2 ^ width)
    (sourceBound : sourceBase < state.heap.size)
    (headerBound : sourceBase + 5 < state.heap.size)
    (sourceCell : state.heap[sourceBase]'sourceBound = word width rows)
    (headerCell : state.heap[sourceBase + 5]'headerBound = word width arityOffset)
    (position : state.pc = word width entry) (running : state.halted = false) :
    ∃ final, Execution program state final 10 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 10) ∧ final.halted = false ∧
      final.reg 2 = word width rows ∧
      final.reg 4 = word width (sourceBase + arityOffset) ∧
      final.reg 3 = word width 1 ∧ final.reg 5 = word width 2 ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) ∧
      final.reg 1 = state.reg 1 := by
  let s1 := state.advance.put 2 (word width sourceBase)
  let s2 := s1.advance.put 2 (word width rows)
  let s3 := s2.advance.put 4 (word width (sourceBase + 5))
  let s4 := s3.advance.put 4 (word width arityOffset)
  let s5 := s4.advance.put 0 (word width sourceBase)
  let s6 := s5.advance.put 4 (word width (sourceBase + arityOffset))
  let s7 := s6.advance.put 3 (word width 1)
  let s8 := s7.advance.put 5 (word width 2)
  let s9 := s8.advance.put 6 (word width 0)
  let final := s9.advance.put 7 (word width (2 ^ width - 1))
  have baseValue : (word width sourceBase).val = sourceBase := Nat.mod_eq_of_lt (by omega)
  have headerValue : (word width (sourceBase + 5)).val = sourceBase + 5 := Nat.mod_eq_of_lt baseFits
  have offsetValue : (word width arityOffset).val = arityOffset := Nat.mod_eq_of_lt (by omega)
  have pc1 : s1.pc = word width (entry + 1) := by
    change state.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    change s5.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5 (entry + 5) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 7) := by
    change s6.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6 (entry + 6) pc6 (by omega)
  have pc8 : s8.pc = word width (entry + 8) := by
    change s7.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7 (entry + 7) pc7 (by omega)
  have pc9 : s9.pc = word width (entry + 9) := by
    change s8.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8 (entry + 8) pc8 (by omega)
  have pc10 : final.pc = word width (entry + 10) := by
    change s9.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9 (entry + 9) pc9 (by omega)
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.constant 2 (word width sourceBase)) position (by omega)
      (by simpa [dependencySetupCode] using physical ⟨0, by decide⟩)]
    simp [step, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.load 2 2) pc1 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.constant 4 (word width (sourceBase + 5))) pc2 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.load 4 4) pc3 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.constant 0 (word width sourceBase)) pc4 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨4, by decide⟩)]
    simp [step, s5, s4, s3, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.add 4 4 0) pc5 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨5, by decide⟩)]
    simp [step, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) (.constant 3 (word width 1)) pc6 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨6, by decide⟩)]
    simp [step, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (entry + 7) (.constant 5 (word width 2)) pc7 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨7, by decide⟩)]
    simp [step, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (entry + 8) (.constant 6 (word width 0)) pc8 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨8, by decide⟩)]
    simp [step, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t9 : programStep program s9 = some final := by
    rw [fetched program s9 (entry + 9) (.constant 7 (word width (2 ^ width - 1))) pc9 (by omega)
      (by simpa [dependencySetupCode] using physical ⟨9, by decide⟩)]
    simp [step, final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  refine ⟨final, ?_, rfl, rfl, rfl, pc10, running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Nat.max_self, Nat.reduceAdd] using
      Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.refl final))))))))))
  all_goals simp only [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]; rfl


private theorem dependency_header_execution (program : Program width 8)
    (entry rows : Nat) (state : State width 8)
    (physical : ∀ position : Fin 10, program[entry + position.val]? =
      (dependencyHeaderCode width)[position.val]?)
    (codeFits : entry + 10 < 2 ^ width) (pointerFits : 5 + 2 * rows < 2 ^ width)
    (room : state.heap.size + 5 ≤ 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (rowsHeld : state.reg 2 = word width rows) :
    ∃ final, Execution program state final 10 (state.liveWords + 5) ∧
      final.heap = state.heap ++ #[word width 0, word width (5 + 2 * rows),
        word width (5 + 2 * rows), word width 5, word width (5 + 2 * rows)] ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 10) ∧ final.halted = false ∧
      final.reg 1 = word width (5 + 2 * rows) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → final.reg register = state.reg register) := by
  let s1 := state.advance.put 1 (word width (2 * rows))
  let s2 := s1.advance.put 0 (word width 5)
  let s3 := s2.advance.put 1 (word width (5 + 2 * rows))
  let s4 := s3.advance.put 0 (word width 0)
  let s5 := { s4.advance with heap := state.heap.push (word width 0) }
  let s6 := { s5.advance with heap := s5.heap.push (word width (5 + 2 * rows)) }
  let s7 := { s6.advance with heap := s6.heap.push (word width (5 + 2 * rows)) }
  let s8 := s7.advance.put 0 (word width 5)
  let s9 := { s8.advance with heap := s8.heap.push (word width 5) }
  let final := { s9.advance with heap := s9.heap.push (word width (5 + 2 * rows)) }
  have doubleEq : rows + rows = 2 * rows := by omega
  have rowsValue : (word width rows).val = rows := Nat.mod_eq_of_lt (by omega)
  have doubledValue : (word width (2 * rows)).val = 2 * rows := Nat.mod_eq_of_lt (by omega)
  have fiveValue : (word width 5).val = 5 := Nat.mod_eq_of_lt (by omega)
  have pc1 : s1.pc = word width (entry + 1) := by
    change state.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    change s5.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5 (entry + 5) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 7) := by
    change s6.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6 (entry + 6) pc6 (by omega)
  have pc8 : s8.pc = word width (entry + 8) := by
    change s7.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7 (entry + 7) pc7 (by omega)
  have pc9 : s9.pc = word width (entry + 9) := by
    change s8.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8 (entry + 8) pc8 (by omega)
  have pc10 : final.pc = word width (entry + 10) := by
    change s9.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9 (entry + 9) pc9 (by omega)
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.add 1 2 2) position (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨0, by decide⟩)]
    simp [step, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq] <;> omega
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 0 (word width 5)) pc1 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq] <;> omega
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 1 1 0) pc2 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq] <;> omega
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.constant 0 (word width 0)) pc3 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq] <;> omega
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.allocate 0) pc4 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨4, by decide⟩)]
    have available : s4.heap.size < 2 ^ width := by
      simp only [s5, s4, s3, s2, s1, State.advance, State.put, Array.size_push]; omega
    simp [step, s5, s4, s3, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq, available] <;> omega
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.allocate 1) pc5 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨5, by decide⟩)]
    have available : s5.heap.size < 2 ^ width := by
      simp only [s6, s5, s4, s3, s2, s1, State.advance, State.put, Array.size_push]; omega
    simp [step, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq, available] <;> omega
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) (.allocate 1) pc6 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨6, by decide⟩)]
    have available : s6.heap.size < 2 ^ width := by
      simp only [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, Array.size_push]; omega
    simp [step, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq, available] <;> omega
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (entry + 7) (.constant 0 (word width 5)) pc7 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨7, by decide⟩)]
    simp [step, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq] <;> omega
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (entry + 8) (.allocate 0) pc8 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨8, by decide⟩)]
    have available : s8.heap.size < 2 ^ width := by
      simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, Array.size_push]; omega
    simp [step, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq, available] <;> omega
  have t9 : programStep program s9 = some final := by
    rw [fetched program s9 (entry + 9) (.allocate 1) pc9 (by omega)
      (by simpa [dependencyHeaderCode] using physical ⟨9, by decide⟩)]
    have available : s9.heap.size < 2 ^ width := by
      simp only [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, Array.size_push]; omega
    simp [step, final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, rowsHeld, rowsValue, doubledValue, fiveValue,
      Nat.add_comm, doubleEq, available] <;> omega
  refine ⟨final, ?_, ?_, rfl, rfl, pc10, running, ?_, ?_⟩
  · convert Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.refl final)))))))))) using 1 <;>
      simp only [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_push] <;> omega
  · simp only [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, Array.push_eq_append, Array.append_assoc]
    rfl
  · simp only [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]; rfl
  · intro register notZero notOne
    simp only [final, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, ite_eq_right notZero, ite_eq_right notOne]


private theorem dependency_transition_execution (program : Program width 8)
    (entry sourceBase rows arityOffset childCursor : Nat) (state : State width 8)
    (physical : ∀ position : Fin 8, program[entry + position.val]? =
      (dependencyTransitionCode width sourceBase)[position.val]?)
    (codeFits : entry + 8 < 2 ^ width)
    (baseFits : sourceBase + 5 < 2 ^ width)
    (pointerFits : sourceBase + arityOffset < 2 ^ width)
    (sourceBound : sourceBase < state.heap.size)
    (headerBound : sourceBase + 5 < state.heap.size)
    (sourceCell : state.heap[sourceBase]'sourceBound = word width rows)
    (headerCell : state.heap[sourceBase + 5]'headerBound = word width arityOffset)
    (position : state.pc = word width entry) (running : state.halted = false)
    (childCursorHeld : state.reg 4 = word width childCursor) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 8) ∧ final.halted = false ∧
      final.reg 1 = word width 0 ∧ final.reg 2 = word width rows ∧
      final.reg 4 = word width (sourceBase + arityOffset) ∧
      final.reg 5 = word width childCursor ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        register ≠ 4 → register ≠ 5 → final.reg register = state.reg register) := by
  let s1 := state.advance.put 5 (word width childCursor)
  let s2 := s1.advance.put 4 (word width (sourceBase + 5))
  let s3 := s2.advance.put 4 (word width arityOffset)
  let s4 := s3.advance.put 0 (word width sourceBase)
  let s5 := s4.advance.put 4 (word width (sourceBase + arityOffset))
  let s6 := s5.advance.put 2 (word width sourceBase)
  let s7 := s6.advance.put 2 (word width rows)
  let final := s7.advance.put 1 (word width 0)
  have baseValue : (word width sourceBase).val = sourceBase := Nat.mod_eq_of_lt (by omega)
  have headerValue : (word width (sourceBase + 5)).val = sourceBase + 5 := Nat.mod_eq_of_lt baseFits
  have offsetValue : (word width arityOffset).val = arityOffset := Nat.mod_eq_of_lt (by omega)
  have pc1 : s1.pc = word width (entry + 1) := by
    change state.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    change s5.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5 (entry + 5) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 7) := by
    change s6.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6 (entry + 6) pc6 (by omega)
  have pc8 : final.pc = word width (entry + 8) := by
    change s7.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7 (entry + 7) pc7 (by omega)
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.copy 5 4) position (by omega)
      (by simpa [dependencyTransitionCode] using physical ⟨0, by decide⟩)]
    simp [step, s1, State.advance, State.put, running, childCursorHeld, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 4 (word width (sourceBase + 5))) pc1 (by omega)
      (by simpa [dependencyTransitionCode] using physical ⟨1, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running, childCursorHeld, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 4 4) pc2 (by omega)
      (by simpa [dependencyTransitionCode] using physical ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.advance, State.put, running, childCursorHeld, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.constant 0 (word width sourceBase)) pc3 (by omega)
      (by simpa [dependencyTransitionCode] using physical ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.advance, State.put, running, childCursorHeld, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 4 4 0) pc4 (by omega)
      (by simpa [dependencyTransitionCode] using physical ⟨4, by decide⟩)]
    simp [step, s5, s4, s3, s2, s1, State.advance, State.put, running, childCursorHeld, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.constant 2 (word width sourceBase)) pc5 (by omega)
      (by simpa [dependencyTransitionCode] using physical ⟨5, by decide⟩)]
    simp [step, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, childCursorHeld, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) (.load 2 2) pc6 (by omega)
      (by simpa [dependencyTransitionCode] using physical ⟨6, by decide⟩)]
    simp [step, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, childCursorHeld, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  have t7 : programStep program s7 = some final := by
    rw [fetched program s7 (entry + 7) (.constant 1 (word width 0)) pc7 (by omega)
      (by simpa [dependencyTransitionCode] using physical ⟨7, by decide⟩)]
    simp [step, final, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, running, childCursorHeld, baseValue, headerValue, offsetValue,
      sourceBound, headerBound, sourceCell, headerCell, Nat.add_comm]
  refine ⟨final, ?_, rfl, rfl, rfl, pc8, running, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [final, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Nat.max_self, Nat.reduceAdd] using
      Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.refl final))))))))
  all_goals first
    | (intro register a b c d e; simp only [final, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, ite_eq_right a, ite_eq_right b, ite_eq_right c, ite_eq_right d, ite_eq_right e])
    | (simp only [final, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]; rfl)


private theorem dependencyBoundaries_start (arities : List Nat) (pointer index : Nat)
    (inside : index < arities.length) :
    (dependencyBoundaries width pointer arities)[2 * index]? =
      some (word width (pointer + dependencySpan (arities.take index))) := by
  induction arities generalizing pointer index with
  | nil => simp at inside
  | cons arity rest ih =>
    cases index with
    | zero => simp [dependencyBoundaries, dependencySpan]
    | succ index =>
      have tailInside : index < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside
      have addressEq : 2 * (index + 1) = 2 * index + 2 := by omega
      rw [addressEq]
      simp only [dependencyBoundaries, List.getElem?_cons_succ, List.take_succ_cons]
      rw [ih (pointer + 2 * (arity + 1)) index tailInside]
      congr 2
      simp only [dependencySpan_cons]
      omega

private theorem dependencyBoundaries_end (arities : List Nat) (pointer index : Nat)
    (inside : index < arities.length) :
    (dependencyBoundaries width pointer arities)[2 * index + 1]? =
      some (word width (pointer + dependencySpan (arities.take (index + 1)))) := by
  induction arities generalizing pointer index with
  | nil => simp at inside
  | cons arity rest ih =>
    cases index with
    | zero => simp [dependencyBoundaries, dependencySpan]
    | succ index =>
      have tailInside : index < rest.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside
      have addressEq : 2 * (index + 1) + 1 = (2 * index + 1) + 2 := by omega
      rw [addressEq]
      simp only [dependencyBoundaries, List.getElem?_cons_succ, List.take_succ_cons]
      rw [ih (pointer + 2 * (arity + 1)) index tailInside]
      congr 2
      simp only [dependencySpan_cons]
      omega

-- Apply these to actual original arities after the physical directory loop.
-- Each original dependency clause has one negative parent plus all original
-- child occurrences. Therefore the spans are exactly frozen sourceOffset;
-- equality of arrays follows by slot quotient/parity, retaining duplicate rows.
private theorem dependency_clause_lengths (graph : UnorderedDAG n) :
    (RawDependencyOrder.dependencyClauses graph).map List.length =
      (List.ofFn (fun parent : Fin graph.nodeCount => (graph.node parent).children.length)).map
        (fun arity => arity + 1) := by
  simp only [RawDependencyOrder.dependencyClauses, List.map_ofFn]
  congr 1
  funext parent
  simp [RawDependencyOrder.dependencyClause]

private theorem dependency_sourceOffset (clauses : List (Controller.CNF.Clause (Fin n)))
    (arities : List Nat) (pointer index : Nat)
    (lengths : clauses.map List.length = arities.map (fun arity => arity + 1)) :
    Controller.Horn.SourceDirectory.sourceOffset clauses pointer index =
      pointer + dependencySpan (arities.take index) := by
  have prefixLengths := congrArg (List.take index) lengths
  rw [← List.map_take, ← List.map_take] at prefixLengths
  simp only [Controller.Horn.SourceDirectory.sourceOffset, dependencySpan, prefixLengths]

private theorem dependency_directory_words_exact
    (clauses : List (Controller.CNF.Clause (Fin n))) (arities : List Nat)
    (sameLength : clauses.length = arities.length)
    (lengths : clauses.map List.length = arities.map (fun arity => arity + 1)) :
    (dependencyBoundaries width (Controller.Horn.SourceSerialize.source clauses) arities).toArray =
      Controller.Horn.SourceSerialize.directoryWords (width := width) clauses := by
  apply Array.ext_getElem?
  intro position
  by_cases inside : position < 2 * arities.length
  · have rowInside : position / 2 < arities.length := by omega
    let row : Fin clauses.length := ⟨position / 2, by omega⟩
    have either : position % 2 = 0 ∨ position % 2 = 1 := by omega
    rcases either with even | odd
    · have address : position = 2 * (position / 2) := by omega
      rw [address]
      rw [Controller.Horn.SourceSerialize.directoryWords_start clauses row]
      simp only [List.getElem?_toArray]
      rw [dependencyBoundaries_start arities _ _ rowInside]
      rw [dependency_sourceOffset clauses arities _ _ lengths]
    · have address : position = 2 * (position / 2) + 1 := by omega
      rw [address]
      rw [Controller.Horn.SourceSerialize.directoryWords_end clauses row]
      simp only [List.getElem?_toArray]
      rw [dependencyBoundaries_end arities _ _ rowInside]
      rw [dependency_sourceOffset clauses arities _ _ lengths]
  · have leftSize : (dependencyBoundaries width (Controller.Horn.SourceSerialize.source clauses) arities).toArray.size =
        2 * arities.length := by simp only [List.size_toArray, dependencyBoundaries_length]
    have rightSize : (Controller.Horn.SourceSerialize.directoryWords (width := width) clauses).size =
        2 * arities.length := by rw [Controller.Horn.SourceSerialize.directoryWords_size, sameLength]
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

theorem dependency_packet_exact (graph : UnorderedDAG n) :
    #[word width 0, word width (5 + 2 * graph.nodeCount), word width (5 + 2 * graph.nodeCount),
      word width 5, word width (5 + 2 * graph.nodeCount)] ++
      ((dependencyBoundaries width (5 + 2 * graph.nodeCount)
        (List.ofFn (fun parent : Fin graph.nodeCount => (graph.node parent).children.length))).toArray ++
        (dependencyLiteralWords width 0 (List.ofFn (fun parent : Fin graph.nodeCount =>
          (graph.node parent).children.map Fin.val))).toArray) =
      Controller.Horn.SourceSerialize.heap (width := width) (RawDependencyOrder.dependencyClauses graph) := by
  have count : (RawDependencyOrder.dependencyClauses graph).length = graph.nodeCount := by
    simp [RawDependencyOrder.dependencyClauses]
  have directory := dependency_directory_words_exact (width := width)
    (RawDependencyOrder.dependencyClauses graph)
    (List.ofFn (fun parent : Fin graph.nodeCount => (graph.node parent).children.length))
    (by simp [RawDependencyOrder.dependencyClauses]) (dependency_clause_lengths graph)
  simp only [Controller.Horn.SourceSerialize.source, count] at directory
  rw [directory, ← dependency_source_words_exact graph]
  change _ = Controller.Horn.SourceSerialize.headers (RawDependencyOrder.dependencyClauses graph) ++ _
  have headers : Controller.Horn.SourceSerialize.headers (width := width)
      (RawDependencyOrder.dependencyClauses graph) =
      #[word width 0, word width (5 + 2 * graph.nodeCount), word width (5 + 2 * graph.nodeCount),
        word width 5, word width (5 + 2 * graph.nodeCount)] := by
    simp only [Controller.Horn.SourceSerialize.headers, Controller.Horn.SourceSerialize.source,
      Controller.Horn.SourceSerialize.directory, count]
  rw [headers]


private theorem stored_after_append (original final : Array (Word width))
    (added : Array (Word width)) (same : final = original ++ added)
    (address : Nat) (value : Word width) (cell : original[address]? = some value) :
    final[address]? = some value := by
  obtain ⟨inside, actual⟩ := Array.getElem?_eq_some_iff.mp cell
  rw [same, Array.getElem?_append_left inside]
  exact cell

private theorem dependencySpan_lengths (rows : List (List Nat)) :
    dependencySpan (rows.map List.length) = 2 * rows.length + 2 * childTotal rows := by
  induction rows with
  | nil => simp [dependencySpan, childTotal]
  | cons children rest ih =>
    simp only [List.map_cons, dependencySpan_cons, List.length_cons, childTotal,
      List.map_cons, List.sum_cons] at *
    omega

-- Original rows are a semantic description of the immutable original source
-- cells; the raw-source consumer derives each premise from its counted encoder.
theorem dependency_serializer_execution (program : Program width 8)
    (entry sourceBase : Nat) (rows : List (List Nat)) (state : State width 8)
    (physical : ∀ position : Fin 56, program[entry + position.val]? =
      (dependencySerializerCode width entry sourceBase)[position.val]?)
    (codeFits : entry + 56 < 2 ^ width)
    (sourceFits : sourceBase + 9 + 6 * rows.length + childTotal rows < 2 ^ width)
    (packetFits : 5 + 4 * rows.length + 2 * childTotal rows < 2 ^ width)
    (room : state.heap.size + 5 + 4 * rows.length + 2 * childTotal rows ≤ 2 ^ width)
    (rowHeaderBound : sourceBase < state.heap.size)
    (arityHeaderBound : sourceBase + 5 < state.heap.size)
    (rowHeader : state.heap[sourceBase]'rowHeaderBound = word width rows.length)
    (arityHeader : state.heap[sourceBase + 5]'arityHeaderBound = word width (9 + 4 * rows.length))
    (arities : ∀ index : Fin rows.length,
      state.heap[(sourceBase + 9 + 4 * rows.length) + 2 * index.val]? =
        some (word width rows[index].length))
    (children : ∀ index : Fin rows.length, ∀ child : Fin rows[index].length,
      state.heap[(sourceBase + 9 + 6 * rows.length) + childTotal (rows.take index.val) + child.val]? =
        some (word width rows[index][child]))
    (position : state.pc = word width entry) (running : state.halted = false) :
    ∃ final peak, Execution program state final (22 * rows.length + 7 * childTotal rows + 30) peak ∧
      peak ≤ state.liveWords + 6 + 4 * rows.length + 2 * childTotal rows ∧
      final.heap = state.heap ++
        (#[word width 0, word width (5 + 2 * rows.length), word width (5 + 2 * rows.length),
          word width 5, word width (5 + 2 * rows.length)] ++
          ((dependencyBoundaries width (5 + 2 * rows.length) (rows.map List.length)).toArray ++
            (dependencyLiteralWords width 0 rows).toArray)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 56) ∧ final.halted = false := by
  have setupPhysical : ∀ position : Fin 10, program[entry + position.val]? =
      (dependencySetupCode width sourceBase)[position.val]? := by
    intro position
    have cell := physical ⟨position.val, by omega⟩
    fin_cases position <;>
      simpa [dependencySerializerCode, dependencySetupCode, dependencyHeaderCode,
        dependencyDirectoryCode, dependencyTransitionCode, dependencyLiteralCode] using cell
  have headerPhysical : ∀ position : Fin 10, program[(entry + 10) + position.val]? =
      (dependencyHeaderCode width)[position.val]? := by
    intro position
    have cell := physical ⟨10 + position.val, by omega⟩
    fin_cases position <;>
      simpa [dependencySerializerCode, dependencySetupCode, dependencyHeaderCode,
        dependencyDirectoryCode, dependencyTransitionCode, dependencyLiteralCode, Nat.add_assoc] using cell
  have directoryPhysical : ∀ position : Fin 10, program[(entry + 20) + position.val]? =
      (dependencyDirectoryCode width (entry + 20) (entry + 30))[position.val]? := by
    intro position
    have cell := physical ⟨20 + position.val, by omega⟩
    fin_cases position <;>
      simpa [dependencySerializerCode, dependencySetupCode, dependencyHeaderCode,
        dependencyDirectoryCode, dependencyTransitionCode, dependencyLiteralCode, Nat.add_assoc] using cell
  have transitionPhysical : ∀ position : Fin 8, program[(entry + 30) + position.val]? =
      (dependencyTransitionCode width sourceBase)[position.val]? := by
    intro position
    have cell := physical ⟨30 + position.val, by omega⟩
    fin_cases position <;>
      simpa [dependencySerializerCode, dependencySetupCode, dependencyHeaderCode,
        dependencyDirectoryCode, dependencyTransitionCode, dependencyLiteralCode, Nat.add_assoc] using cell
  have literalPhysical : ∀ position : Fin 18, program[(entry + 38) + position.val]? =
      (dependencyLiteralCode width (entry + 38) (entry + 56))[position.val]? := by
    intro position
    have cell := physical ⟨38 + position.val, by omega⟩
    fin_cases position <;>
      simpa [dependencySerializerCode, dependencySetupCode, dependencyHeaderCode,
        dependencyDirectoryCode, dependencyTransitionCode, dependencyLiteralCode, Nat.add_assoc] using cell
  obtain ⟨setup, setupTrace, setupHeap, setupStack, setupOutput, setupPC, setupRunning,
    setupRows, setupCursor, setupOne, setupTwo, setupZero, setupMinus, setupParent⟩ :=
      dependency_setup_execution program entry sourceBase rows.length (9 + 4 * rows.length) state
        setupPhysical (by omega) (by omega) (by omega) rowHeaderBound arityHeaderBound
        rowHeader arityHeader position running
  obtain ⟨header, headerTrace, headerHeap, headerStack, headerOutput, headerPC, headerRunning,
    headerPointer, headerFrame⟩ := dependency_header_execution program (entry + 10) rows.length setup
      headerPhysical (by omega) (by omega) (by rw [setupHeap]; omega) setupPC setupRunning setupRows
  have headerSize : header.heap.size = state.heap.size + 5 := by
    rw [headerHeap, setupHeap]; simp
  have arityStored : ∀ index : Fin (rows.map List.length).length,
      header.heap[(sourceBase + 9 + 4 * rows.length) + 2 * index.val]? =
        some (word width (rows.map List.length)[index]) := by
    intro index
    have cell := arities ⟨index.val, by simpa using index.isLt⟩
    have retained := stored_after_append state.heap header.heap _
      (by rw [headerHeap, setupHeap]) _ _ cell
    have selected : (rows.map List.length).get index =
        (rows.get ⟨index.val, by simpa using index.isLt⟩).length := by
      simp only [List.get_eq_getElem, List.getElem_map]
    change header.heap[(sourceBase + 9 + 4 * rows.length) + 2 * index.val]? =
      some (word width ((rows.map List.length).get index))
    rw [selected]
    exact retained
  have spanEq := dependencySpan_lengths rows
  obtain ⟨directory, directoryTrace, directoryHeap, directoryStack, directoryOutput,
    directoryPC, directoryRunning, directoryPointer, directoryRows, directoryCursor, directoryFrame⟩ :=
      dependency_directory_execution program (entry + 20) (entry + 30)
        (rows.map List.length) (5 + 2 * rows.length) (sourceBase + 9 + 4 * rows.length) header
        directoryPhysical (by omega) (by simpa using (show rows.length < 2 ^ width by omega))
        (by simp only [List.length_map]; omega) (by rw [spanEq]; omega)
        (by rw [headerSize]; simp only [List.length_map]; omega) arityStored
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using headerPC) headerRunning headerPointer
        (by simpa only [List.length_map] using (headerFrame 2 (by decide) (by decide)).trans setupRows)
        ((headerFrame 3 (by decide) (by decide)).trans setupOne)
        (by simpa only [Nat.add_assoc] using (headerFrame 4 (by decide) (by decide)).trans setupCursor)
        ((headerFrame 5 (by decide) (by decide)).trans setupTwo)
        ((headerFrame 6 (by decide) (by decide)).trans setupZero)
        ((headerFrame 7 (by decide) (by decide)).trans setupMinus)
  have directoryOriginal : directory.heap = state.heap ++
      (#[word width 0, word width (5 + 2 * rows.length), word width (5 + 2 * rows.length),
        word width 5, word width (5 + 2 * rows.length)] ++
        (dependencyBoundaries width (5 + 2 * rows.length) (rows.map List.length)).toArray) := by
    rw [directoryHeap, headerHeap, setupHeap, Array.append_assoc]
  have originalFrame : ∀ (address : Nat) (value : Word width),
      state.heap[address]? = some value → directory.heap[address]? = some value := by
    intro address value cell
    exact stored_after_append state.heap directory.heap _ directoryOriginal address value cell
  have rowCell := originalFrame sourceBase (word width rows.length)
    (Array.getElem?_eq_some_iff.mpr ⟨rowHeaderBound, rowHeader⟩)
  have arityCell := originalFrame (sourceBase + 5) (word width (9 + 4 * rows.length))
    (Array.getElem?_eq_some_iff.mpr ⟨arityHeaderBound, arityHeader⟩)
  obtain ⟨rowBound, rowActual⟩ := Array.getElem?_eq_some_iff.mp rowCell
  obtain ⟨arityBound, arityActual⟩ := Array.getElem?_eq_some_iff.mp arityCell
  have childCursorEq : (sourceBase + 9 + 4 * rows.length) + 2 * (rows.map List.length).length =
      sourceBase + 9 + 6 * rows.length := by simp only [List.length_map]; omega
  rw [childCursorEq] at directoryCursor
  obtain ⟨transition, transitionTrace, transitionHeap, transitionStack, transitionOutput,
    transitionPC, transitionRunning, transitionParent, transitionRows, transitionCursor,
    transitionChildCursor, transitionFrame⟩ := dependency_transition_execution program (entry + 30)
      sourceBase rows.length (9 + 4 * rows.length) (sourceBase + 9 + 6 * rows.length) directory
      transitionPhysical (by omega) (by omega) (by omega) rowBound arityBound rowActual arityActual
      directoryPC directoryRunning directoryCursor
  have transitionOriginal : transition.heap = state.heap ++
      (#[word width 0, word width (5 + 2 * rows.length), word width (5 + 2 * rows.length),
        word width 5, word width (5 + 2 * rows.length)] ++
        (dependencyBoundaries width (5 + 2 * rows.length) (rows.map List.length)).toArray) :=
    transitionHeap.trans directoryOriginal
  have transitionSize : transition.heap.size = state.heap.size + 5 + 2 * rows.length := by
    rw [transitionOriginal]
    simp only [Array.size_append, List.size_toArray, dependencyBoundaries_length, List.length_map,
      List.length_cons, List.length_nil]
    omega
  have literalArities : ∀ index : Fin rows.length,
      transition.heap[(sourceBase + 9 + 4 * rows.length) + 2 * index.val]? =
        some (word width rows[index].length) := by
    intro index
    rw [transitionHeap]
    exact originalFrame _ _ (arities index)
  have literalChildren : ∀ index : Fin rows.length, ∀ child : Fin rows[index].length,
      transition.heap[(sourceBase + 9 + 6 * rows.length) + childTotal (rows.take index.val) + child.val]? =
        some (word width rows[index][child]) := by
    intro index child
    rw [transitionHeap]
    exact originalFrame _ _ (children index child)
  have literalOne : transition.reg 3 = word width 1 :=
    (transitionFrame 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((directoryFrame 3 (by decide) (by decide) (by decide) (by decide)).trans
        ((headerFrame 3 (by decide) (by decide)).trans setupOne))
  have literalZero : transition.reg 6 = word width 0 :=
    (transitionFrame 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((directoryFrame 6 (by decide) (by decide) (by decide) (by decide)).trans
        ((headerFrame 6 (by decide) (by decide)).trans setupZero))
  have literalMinus : transition.reg 7 = word width (2 ^ width - 1) :=
    (transitionFrame 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((directoryFrame 7 (by decide) (by decide) (by decide) (by decide)).trans
        ((headerFrame 7 (by decide) (by decide)).trans setupMinus))
  obtain ⟨final, literalPeak, literalTrace, literalPeakBound, finalHeap, finalStack,
    finalOutput, finalPC, finalRunning, finalParent, finalRows, finalRowCursor, finalChildCursor,
    finalFrame⟩ := dependency_literal_execution program (entry + 38) (entry + 56) 0
      (sourceBase + 9 + 4 * rows.length) (sourceBase + 9 + 6 * rows.length) rows transition
      literalPhysical (by omega) (by omega) (by omega) (by omega) sourceFits (by omega)
      (by rw [transitionSize]; omega) literalArities literalChildren
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using transitionPC) transitionRunning
      transitionParent transitionRows literalOne
      (by simpa only [Nat.add_assoc] using transitionCursor) transitionChildCursor literalZero literalMinus
  have setupLive : setup.liveWords = state.liveWords := by
    simp only [State.liveWords, setupHeap, setupStack, setupOutput]
  have headerLive : header.liveWords = state.liveWords + 5 := by
    simp only [State.liveWords, headerSize, headerStack, setupStack, headerOutput, setupOutput]; omega
  have directorySize : directory.heap.size = state.heap.size + 5 + 2 * rows.length := by
    rw [← transitionHeap]; exact transitionSize
  have directoryLive : directory.liveWords = state.liveWords + 5 + 2 * rows.length := by
    simp only [State.liveWords, directorySize, directoryStack, headerStack, setupStack,
      directoryOutput, headerOutput, setupOutput]; omega
  have transitionLive : transition.liveWords = directory.liveWords := by
    simp only [State.liveWords, transitionHeap, transitionStack, transitionOutput]
  refine ⟨final,
    max (max (max (max state.liveWords (setup.liveWords + 5))
      (header.liveWords + 2 * (rows.map List.length).length)) directory.liveWords) literalPeak,
    ?_, ?_, ?_, ?_, ?_, finalPC, finalRunning⟩
  · convert (((setupTrace.append headerTrace).append directoryTrace).append transitionTrace).append literalTrace using 1 <;>
      simp only [List.length_map] <;> omega
  · rw [transitionLive, directoryLive] at literalPeakBound
    simp only [setupLive, headerLive, directoryLive, List.length_map]
    omega
  · simp only [finalHeap, transitionOriginal, Array.append_assoc]
  · exact finalStack.trans (transitionStack.trans (directoryStack.trans (headerStack.trans setupStack)))
  · exact finalOutput.trans (transitionOutput.trans (directoryOutput.trans (headerOutput.trans setupOutput)))

private theorem dependency_save_handoff_execution (program : Program width 8)
    (entry target : Nat) (originalHeap : Array (Word width)) (packet : List (Word width))
    (state : State width 8) (heap : state.heap = originalHeap ++ packet.toArray)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 3 * packet.length + state.heap.size + 2 < 2 ^ width)
    (sourceFits : originalHeap.size + packet.length ≤ 2 ^ width)
    (saveAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt program entry
      (sourceSaveCode width originalHeap.size packet.length))
    (releaseAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt program
      (entry + 3 * packet.length) (packetReleaseCode width state.heap.size))
    (handoff0 : program[entry + 3 * packet.length + state.heap.size]? =
      some (.constant 6 (word width 0)))
    (handoff1 : program[entry + 3 * packet.length + state.heap.size + 1]? =
      some (.branchZero 6 (word width target))) :
    ∃ final, Execution program state final (3 * packet.length + state.heap.size + 2)
        (state.liveWords + packet.length) ∧
      final.heap = #[] ∧ final.stack = packet ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width target ∧ final.halted = false := by
  have cells : ∀ index : Fin packet.length,
      state.heap[originalHeap.size + index.val]? = some packet[index.val] := by
    intro index
    rw [heap, Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_toArray, List.getElem?_eq_getElem index.isLt]
  obtain ⟨saved, saveTrace, saveHeap, saveStack, saveOutput, savePC, saveRunning, saveRegisters⟩ :=
    source_save_execution program entry originalHeap.size state packet position running (by omega)
      sourceFits cells saveAt
  have savedSize : saved.heap.size = state.heap.size := congrArg Array.size saveHeap
  obtain ⟨released, releaseTrace, releasedHeap, releasedStack, releasedOutput,
    releasedPC, releasedRunning, releasedRegisters⟩ := packet_release_execution program
      (entry + 3 * packet.length) saved savePC saveRunning (by rw [savedSize]; omega)
      (by simpa only [savedSize] using releaseAt)
  have transferredPC : released.pc = word width (entry + 3 * packet.length + state.heap.size) := by
    simpa only [savedSize] using releasedPC
  obtain ⟨final, handoffTrace, handoffHeap, handoffStack, handoffOutput,
    handoffPC, handoffRunning, handoffZero, handoffRegisters⟩ :=
    cold_handoff_execution program (entry + 3 * packet.length + state.heap.size) target released
      transferredPC releasedRunning (by omega) handoff0 handoff1
  have savedLive : saved.liveWords = state.liveWords + packet.length := by
    simp only [State.liveWords, saveHeap, saveStack, saveOutput, List.length_append]; omega
  have releasedLive : released.liveWords ≤ saved.liveWords := by
    simp only [State.liveWords, releasedHeap, Array.size_empty, releasedStack, releasedOutput]; omega
  have releasedBound : released.liveWords ≤ state.liveWords + packet.length := by
    rw [← savedLive]
    exact releasedLive
  refine ⟨final, ?_, handoffHeap.trans releasedHeap,
    handoffStack.trans (releasedStack.trans saveStack),
    handoffOutput.trans (releasedOutput.trans saveOutput), handoffPC, handoffRunning⟩
  simpa only [savedSize, savedLive, Nat.max_self, Nat.max_eq_left releasedBound] using
    (saveTrace.append releaseTrace).append handoffTrace

private theorem relocated_zero_view (delta : Nat) (state : State width 8)
    (position : state.pc = word width delta) :
    relocatedState delta { state with pc := word width 0 } = state := by
  have translated : word width ((word width 0).val + delta) = word width delta := by
    simp only [word, Nat.zero_mod, Nat.zero_add]
  change { state with pc := word width ((word width 0).val + delta) } = state
  rw [translated, ← position]

private theorem relocated_seed_invariant (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry index delta : Nat)
    (queue : List (Fin n)) (fired : Fin clauses.length → Bool) (state : State width 8)
    (entryFits : entry < 2 ^ width)
    (seed : ScanInvariant clauses recordStart recordEnd base entry index queue fired state) :
    ScanInvariant clauses recordStart recordEnd base (delta + entry) index queue fired
      (relocatedState delta state) := by
  refine { seed with position := ?_ }
  change word width (state.pc.val + delta) = word width (delta + entry)
  rw [seed.position]
  have scalar : (word width entry).val = entry := Nat.mod_eq_of_lt entryFits
  rw [scalar, Nat.add_comm]

def RelocatedCodeAt (resident sourceProgram : Program width 8) (delta : Nat) : Prop :=
  ∀ index : Nat, ∀ inside : index < sourceProgram.size,
    resident[delta + index]? = some (relocatedInstruction delta (sourceProgram[index]'inside))

theorem saved_dependency_cold_execution (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (resident : Program width 8) (saveEntry coldDelta conflict : Nat)
    (originalHeap : Array (Word width)) (state : State width 8)
    (heap : state.heap = originalHeap ++ Controller.Horn.SourceSerialize.heap (width := width) clauses)
    (position : state.pc = word width saveEntry) (running : state.halted = false)
    (transferCapacity : saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size + 2 < 2 ^ width)
    (sourceFits : originalHeap.size + (Controller.Horn.SourceSerialize.heap (width := width) clauses).size ≤ 2 ^ width)
    (saveAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident saveEntry
      (sourceSaveCode width originalHeap.size (Controller.Horn.SourceSerialize.heap (width := width) clauses).size))
    (releaseAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size)
      (packetReleaseCode width state.heap.size))
    (handoff0 : resident[saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size]? = some (.constant 6 (word width 0)))
    (handoff1 : resident[saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size + 1]? = some (.branchZero 6 (word width coldDelta)))
    (coldAt : RelocatedCodeAt resident
      (Controller.Horn.WorklistSeedRun.program width clauses conflict) coldDelta)
    (coldCapacity : coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ recordEnd queue fired final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size + state.heap.size +
        28 * graph.nodeCount + 83 * (clauses.map List.length).sum + 131 * clauses.length + 81 ∧
      peak ≤ state.liveWords + (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
        5 * graph.nodeCount + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      ScanInvariant clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses)
        (coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size)
        clauses.length queue fired final ∧ RawDependencyOrder.DependencyOrder graph queue := by
  let packet := (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList
  have packetLength : packet.length = (Controller.Horn.SourceSerialize.heap (width := width) clauses).size := rfl
  obtain ⟨handoff, transfer, handoffHeap, handoffStack, handoffOutput, handoffPC, handoffRunning⟩ :=
    dependency_save_handoff_execution resident saveEntry coldDelta originalHeap packet state
      (by simpa only [packet, Array.toArray_toList] using heap) position running
      (by simpa only [packetLength] using transferCapacity)
      (by simpa only [packetLength] using sourceFits)
      (by simpa only [packetLength] using saveAt)
      (by simpa only [packetLength] using releaseAt)
      (by simpa only [packetLength] using handoff0)
      (by simpa only [packetLength] using handoff1)
  let coldState := { handoff with pc := word width 0 }
  obtain ⟨recordEnd, queue, fired, last, coldTicks, coldPeak, result, ordered⟩ :=
    ordered_cold_seed_execution graph clauses source conflict coldState state.stack handoffHeap
      handoffStack rfl handoffRunning (by omega) heapFits
  rcases result with ⟨coldTrace, lastStack, lastOutput, lengthBound, coldCost, coldSpace, codeSpace, outcome⟩
  have sourceState : relocatedState coldDelta coldState = handoff := relocated_zero_view coldDelta handoff handoffPC
  have actualCold := relocated_execution resident (Controller.Horn.WorklistSeedRun.program width clauses conflict)
    coldDelta coldAt coldCapacity coldTrace
  rw [sourceState] at actualCold
  have seed : ScanInvariant clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses)
      (Controller.Horn.WorklistSeedRun.program width clauses conflict).size clauses.length queue fired last := by
    rcases outcome with conflictResult | invariant
    · exact False.elim (conflictResult.2.2 ⟨fun _ => false, encoded_false_model graph clauses source⟩)
    · exact invariant
  have handoffLiveBound : handoff.liveWords ≤ state.liveWords + packet.length := by
    simp only [State.liveWords, handoffHeap, Array.size_empty, handoffStack, handoffOutput,
      List.length_append]
    omega
  have coldInitialLive : coldState.liveWords = handoff.liveWords := rfl
  refine ⟨recordEnd, queue, fired, relocatedState coldDelta last,
    3 * packet.length + state.heap.size + 2 + coldTicks,
    max (state.liveWords + packet.length) coldPeak, transfer.append actualCold, ?_, ?_,
    lastStack, lastOutput.trans handoffOutput, ?_, ordered⟩
  · rw [packetLength]
    omega
  · rw [coldInitialLive] at coldSpace
    rw [packetLength] at handoffLiveBound ⊢
    omega
  · exact relocated_seed_invariant clauses _ _ _ _ _ coldDelta queue fired last (by omega) seed

def dependencyRuntimeCode (width nodes base entry conflict : Nat) : Program width 8 :=
  Controller.Horn.WorklistAccept.headSetupCode (n := nodes) width base (entry + 4) ++
  Controller.Horn.WorklistFIFO.fetchCode (n := nodes) width base (entry + 4) (entry + 61) (entry + 18) ++
  Controller.Horn.WorklistBucketLoop.code width (entry + 18) (entry + 56) (entry + 30) ++
  Controller.Horn.WorklistBucketReady.code (n := nodes) width base (entry + 30)
    (entry + 56) conflict (entry + 18) ++
  Controller.Horn.WorklistFIFO.advanceCode (n := nodes) width base (entry + 4)

private theorem dependencyRuntimeCode_size (width nodes base entry conflict : Nat) :
    (dependencyRuntimeCode width nodes base entry conflict).size = 61 := by
  simp only [dependencyRuntimeCode, Array.size_append,
    Controller.Horn.WorklistAccept.head_setup_size, Controller.Horn.WorklistFIFO.fetch_size,
    Controller.Horn.WorklistBucketLoop.code_size, Controller.Horn.WorklistBucketReady.code_size,
    Controller.Horn.WorklistFIFO.advance_size]

-- Runtime code uses absolute target PCs and source heap addresses from the actual
-- cold endpoint. Only the cold prefix is relocated. This avoids translating data
-- constants while retaining each branch target's original machine semantics.

private theorem dependency_fifo_after_seed (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (resident : Program width 8) (recordStart recordEnd base entry conflict : Nat)
    (queue : List (Fin graph.nodeCount)) (fired : Fin clauses.length → Bool)
    (state : State width 8)
    (seed : ScanInvariant clauses recordStart recordEnd base entry clauses.length queue fired state)
    (ordered : RawDependencyOrder.DependencyOrder graph queue)
    (separated : base + 5 * graph.nodeCount + 4 ≤ recordStart)
    (headAt : ∀ phase : Fin 4, resident[entry + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := graph.nodeCount)
        width base (entry + 4))[phase.val]?)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := graph.nodeCount)
      resident base (entry + 4) (entry + 61) (entry + 18))
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := graph.nodeCount)
      resident base (entry + 56) (entry + 4))
    (loopAt : Controller.Horn.WorklistBucketLoop.At resident (entry + 18) (entry + 56) (entry + 30))
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := graph.nodeCount)
      resident base (entry + 30) (entry + 56) conflict (entry + 18))
    (capacity : entry + 61 < 2 ^ width) :
    ∃ finalQueue finalFired final ticks,
      RawDependencyOrder.DependencyOrder graph finalQueue ∧ finalQueue.Nodup ∧
      Execution resident state final ticks state.liveWords ∧
      ticks ≤ 32 * (Controller.Horn.IndexScan.occurrences clauses recordStart).length +
        23 * graph.nodeCount + 10 ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      Controller.Horn.WorklistFIFORun.Done clauses recordStart recordEnd base (entry + 61)
        finalQueue finalFired final ∧
      Controller.Horn.WorklistOutcome.EnabledComplete clauses finalQueue finalFired ∧
      Controller.Horn.WorklistOutcome.FiredMeaning clauses finalQueue finalFired ∧
      Controller.Horn.WorklistSeed.QueueForced clauses finalQueue := by
  obtain ⟨prepared, setup, initial, complete, meaning, forced, setupSize, setupStack, setupOutput⟩ :=
    Controller.Horn.WorklistAccept.seed_to_fifo clauses recordStart recordEnd base entry (entry + 4)
      resident queue fired state seed separated headAt (by omega)
  obtain ⟨finalQueue, finalFired, final, ticks, growth, unique, finalOrder, charged, trace,
    finalSize, finalStack, finalOutput, finalRunning, outcome⟩ :=
    RawDependencyOrder.ordered_semantic_runtime graph clauses recordStart recordEnd base
      (entry + 4) (entry + 61) (entry + 18) (entry + 56) (entry + 30) (entry + 56)
      conflict resident separated fetchAt advanceAt loopAt readyAt (by omega) (by omega)
      (by omega) (by omega) graph.nodeCount 0 queue fired prepared (by omega)
      initial complete meaning forced (encoded_dependencies graph clauses source) ordered
  have preparedLive : prepared.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [setupSize, setupStack, setupOutput]
  have incidenceBound := Controller.Horn.WorklistFIFORun.incidence_bound
    (Controller.Horn.IndexScan.occurrences clauses recordStart) (queue.take 0)
  have queueBound := Controller.Horn.WorklistMark.enqueue_bound finalQueue unique
  rcases outcome with impossible | ⟨done, enabled, finalMeaning, finalForced⟩
  · exact False.elim (impossible.2 ⟨fun _ => false, encoded_false_model graph clauses source⟩)
  · refine ⟨finalQueue, finalFired, final, 4 + ticks, finalOrder, unique, ?_, by omega,
      finalSize.trans setupSize, finalStack.trans setupStack, finalOutput.trans setupOutput,
      done, enabled, finalMeaning, finalForced⟩
    simpa only [preparedLive, Nat.max_self] using setup.append trace

private theorem dependencyRuntime_at (resident : Program width 8)
    (base entry conflict : Nat)
    (present : ∀ phase : Fin 61, resident[entry + phase.val]? =
      (dependencyRuntimeCode width n base entry conflict)[phase.val]?) :
    (∀ phase : Fin 4, resident[entry + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := n) width base (entry + 4))[phase.val]?) ∧
    Controller.Horn.WorklistFIFO.FetchAt (n := n) resident base (entry + 4) (entry + 61) (entry + 18) ∧
    Controller.Horn.WorklistBucketLoop.At resident (entry + 18) (entry + 56) (entry + 30) ∧
    Controller.Horn.WorklistBucketReady.At (n := n) resident base (entry + 30) (entry + 56) conflict (entry + 18) ∧
    Controller.Horn.WorklistFIFO.AdvanceAt (n := n) resident base (entry + 56) (entry + 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro phase
    have cell := present ⟨phase.val, by omega⟩
    fin_cases phase <;> simpa [dependencyRuntimeCode,
      Controller.Horn.WorklistAccept.headSetupCode,
      Controller.Horn.WorklistFIFO.fetchCode, Controller.Horn.WorklistBucketLoop.code,
      Controller.Horn.WorklistBucketReady.code, Controller.Horn.WorklistFIFO.advanceCode] using cell
  · intro phase
    have cell := present ⟨4 + phase.val, by omega⟩
    fin_cases phase <;> simpa [dependencyRuntimeCode,
      Controller.Horn.WorklistAccept.headSetupCode,
      Controller.Horn.WorklistFIFO.fetchCode, Controller.Horn.WorklistBucketLoop.code,
      Controller.Horn.WorklistBucketReady.code, Controller.Horn.WorklistFIFO.advanceCode,
      Nat.add_assoc] using cell
  · intro phase
    have cell := present ⟨18 + phase.val, by omega⟩
    fin_cases phase <;> simpa [dependencyRuntimeCode,
      Controller.Horn.WorklistAccept.headSetupCode,
      Controller.Horn.WorklistFIFO.fetchCode, Controller.Horn.WorklistBucketLoop.code,
      Controller.Horn.WorklistBucketReady.code, Controller.Horn.WorklistFIFO.advanceCode,
      Nat.add_assoc] using cell
  · intro phase
    have cell := present ⟨30 + phase.val, by omega⟩
    fin_cases phase <;> simpa [dependencyRuntimeCode,
      Controller.Horn.WorklistAccept.headSetupCode,
      Controller.Horn.WorklistFIFO.fetchCode, Controller.Horn.WorklistBucketLoop.code,
      Controller.Horn.WorklistBucketReady.code, Controller.Horn.WorklistFIFO.advanceCode,
      Nat.add_assoc] using cell
  · intro phase
    have cell := present ⟨56 + phase.val, by omega⟩
    fin_cases phase <;> simpa [dependencyRuntimeCode,
      Controller.Horn.WorklistAccept.headSetupCode,
      Controller.Horn.WorklistFIFO.fetchCode, Controller.Horn.WorklistBucketLoop.code,
      Controller.Horn.WorklistBucketReady.code, Controller.Horn.WorklistFIFO.advanceCode,
      Nat.add_assoc] using cell

private theorem execution_final_live (resident : Program width 8)
    {initial final : State width 8} {ticks peak : Nat}
    (trace : Execution resident initial final ticks peak) : final.liveWords ≤ peak := by
  induction trace with
  | refl => exact Nat.le_refl _
  | cons transition rest ih => exact ih.trans (Nat.le_max_right _ _)

theorem saved_dependency_fifo_execution (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (resident : Program width 8) (saveEntry coldDelta conflict : Nat)
    (originalHeap : Array (Word width)) (state : State width 8)
    (heap : state.heap = originalHeap ++ Controller.Horn.SourceSerialize.heap (width := width) clauses)
    (position : state.pc = word width saveEntry) (running : state.halted = false)
    (transferCapacity : saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size + 2 < 2 ^ width)
    (sourceFits : originalHeap.size + (Controller.Horn.SourceSerialize.heap (width := width) clauses).size ≤ 2 ^ width)
    (saveAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident saveEntry
      (sourceSaveCode width originalHeap.size (Controller.Horn.SourceSerialize.heap (width := width) clauses).size))
    (releaseAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size)
      (packetReleaseCode width state.heap.size))
    (handoff0 : resident[saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size]? = some (.constant 6 (word width 0)))
    (handoff1 : resident[saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size + 1]? = some (.branchZero 6 (word width coldDelta)))
    (coldAt : RelocatedCodeAt resident
      (Controller.Horn.WorklistSeedRun.program width clauses conflict) coldDelta)
    (coldCapacity : coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width)
    (runtimeAt : ∀ phase : Fin 61,
      resident[(coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size) + phase.val]? =
        (dependencyRuntimeCode width graph.nodeCount (Controller.Horn.SourceSerialize.base clauses)
          (coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size) conflict)[phase.val]?)
    (runtimeCapacity : coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size + 61 < 2 ^ width) :
    ∃ recordEnd finalQueue finalFired final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size + state.heap.size +
        51 * graph.nodeCount + 115 * (clauses.map List.length).sum + 131 * clauses.length + 91 ∧
      peak ≤ state.liveWords + (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
        5 * graph.nodeCount + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      Controller.Horn.WorklistFIFORun.Done clauses (Controller.Horn.IndexScanCold.recordStart width clauses)
        recordEnd (Controller.Horn.SourceSerialize.base clauses)
        (coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size + 61)
        finalQueue finalFired final ∧
      Controller.Horn.WorklistOutcome.EnabledComplete clauses finalQueue finalFired ∧
      Controller.Horn.WorklistOutcome.FiredMeaning clauses finalQueue finalFired ∧
      Controller.Horn.WorklistSeed.QueueForced clauses finalQueue ∧
      RawDependencyOrder.DependencyOrder graph finalQueue ∧ finalQueue.Nodup := by
  obtain ⟨recordEnd, queue, fired, seeded, coldTicks, coldPeak, coldTrace, coldCost,
    coldSpace, seededStack, seededOutput, seed, ordered⟩ :=
    saved_dependency_cold_execution graph clauses source resident saveEntry coldDelta conflict originalHeap
      state heap position running transferCapacity sourceFits saveAt releaseAt handoff0 handoff1
      coldAt coldCapacity heapFits
  obtain ⟨headAt, fetchAt, loopAt, readyAt, advanceAt⟩ := dependencyRuntime_at resident
    (Controller.Horn.SourceSerialize.base clauses)
    (coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size) conflict runtimeAt
  have separated : Controller.Horn.SourceSerialize.base clauses + 5 * graph.nodeCount + 4 ≤
      Controller.Horn.IndexScanCold.recordStart width clauses := by
    simp [Controller.Horn.IndexScanCold.recordStart, Controller.Horn.NormalizeCold.words]
  obtain ⟨finalQueue, finalFired, final, fifoTicks, finalOrder, distinct, fifoTrace, fifoCost,
    finalSize, finalStack, finalOutput, done, enabled, meaning, forced⟩ :=
    dependency_fifo_after_seed graph clauses source resident
      (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses)
      (coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size)
      conflict queue fired seeded seed ordered separated headAt fetchAt advanceAt loopAt readyAt runtimeCapacity
  have finalLive : seeded.liveWords ≤ coldPeak := execution_final_live resident coldTrace
  have incidenceCost := Controller.Horn.IndexScanCold.occurrences_length_le clauses
    (Controller.Horn.IndexScanCold.recordStart width clauses)
  refine ⟨recordEnd, finalQueue, finalFired, final, coldTicks + fifoTicks, coldPeak,
    ?_, by omega, coldSpace, finalStack.trans seededStack,
    finalOutput.trans seededOutput, done, enabled, meaning, forced, finalOrder, distinct⟩
  simpa only [Nat.max_eq_left finalLive] using coldTrace.append fifoTrace

-- Compare the actual stored tail with queueStart+V directly; no count oracle or
-- modular subtraction is needed. Scratch-room guarantees both pointers fit.
def terminalCycleCode (width tail expected accept tag : Nat) : Program width 8 :=
  #[.constant 2 (word width tail), .load 0 2,
    .constant 1 (word width expected), .xor 0 0 1,
    .branchZero 0 (word width accept), .constant 0 (word width tag), .emit 0, .halt]

private theorem tail_difference_zero (start count nodes : Nat)
    (countFits : start + count < 2 ^ width) (nodesFits : start + nodes < 2 ^ width) :
    (word width (Nat.xor (start + count) (start + nodes))).val = 0 ↔ count = nodes := by
  have small := Nat.xor_lt_two_pow countFits nodesFits
  rw [show (word width (Nat.xor (start + count) (start + nodes))).val =
    Nat.xor (start + count) (start + nodes) from Nat.mod_eq_of_lt small]
  constructor
  · intro zero
    change (start + count) ^^^ (start + nodes) = 0 at zero
    have same := congrArg (fun value => value ^^^ (start + nodes)) zero
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at same
    omega
  · intro same
    change (start + count) ^^^ (start + nodes) = 0
    rw [same, Nat.xor_self]

private theorem terminal_tail_test_execution (resident : Program width 8)
    (entry accept tail start count nodes tag : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 8 < 2 ^ width)
    (tailFits : tail < 2 ^ width)
    (actualTail : state.heap[tail]? = some (word width (start + count)))
    (countFits : start + count < 2 ^ width) (nodesFits : start + nodes < 2 ^ width)
    (present : ∀ phase : Fin 8, resident[entry + phase.val]? =
      (terminalCycleCode width tail (start + nodes) accept tag)[phase.val]?) :
    ∃ tested, Execution resident state tested 5 state.liveWords ∧
      tested.heap = state.heap ∧ tested.stack = state.stack ∧ tested.output = state.output ∧
      tested.halted = false ∧
      tested.pc = word width (if count = nodes then accept else entry + 5) := by
  let s1 := state.advance.put 2 (word width tail)
  let s2 := s1.advance.put 0 (word width (start + count))
  let s3 := s2.advance.put 1 (word width (start + nodes))
  let s4 := s3.advance.put 0 (word width (Nat.xor (start + count) (start + nodes)))
  let tested := { s4.advance with pc := word width (if count = nodes then accept else entry + 5) }
  have pc1 : s1.pc = word width (entry + 1) := by
    simpa only [s1, State.put] using referenceAdvancePC state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    simpa only [s4, State.put, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state entry (.constant 2 (word width tail)) position (by omega)
      (by simpa [terminalCycleCode] using present ⟨0, by decide⟩)]
    simp [step, running, s1]
  obtain ⟨tailBound, tailCell⟩ := Array.getElem?_eq_some_iff.mp actualTail
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.load 0 2) pc1 (by omega)
      (by simpa [terminalCycleCode] using present ⟨1, by decide⟩)]
    simp only [step, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, ite_true, word, Nat.mod_eq_of_lt tailFits]
    simp only [dite_eq_left tailBound, tailCell, s2, s1, State.advance, State.put, word, running, Nat.mod_eq_of_lt tailFits]
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.constant 1 (word width (start + nodes))) pc2 (by omega)
      (by simpa [terminalCycleCode] using present ⟨2, by decide⟩)]
    simp [step, s2, s1, State.advance, State.put, running, s3]
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.xor 0 0 1) pc3 (by omega)
      (by simpa [terminalCycleCode] using present ⟨3, by decide⟩)]
    simp only [step, s3, s2, s1, State.advance, State.put, running, Bool.false_eq_true,
      ite_false, ite_true, show (0 : Fin 8) ≠ 1 by decide,
      show (1 : Fin 8) ≠ 0 by decide,
      show (word width (start + count)).val = start + count from Nat.mod_eq_of_lt countFits,
      show (word width (start + nodes)).val = start + nodes from Nat.mod_eq_of_lt nodesFits]
    simp only [s4, s3, s2, s1, State.advance, State.put, running]
  have t4 : programStep resident s4 = some tested := by
    rw [fetched resident s4 (entry + 4) (.branchZero 0 (word width accept)) pc4 (by omega)
      (by simpa [terminalCycleCode] using present ⟨4, by decide⟩)]
    have nextPC : s4.advance.pc = word width (entry + 5) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
    have s4Running : s4.halted = false := running
    have selected : s4.reg 0 = word width (Nat.xor (start + count) (start + nodes)) := by
      simp only [s4, State.put, ite_true]
    simp only [step, s4Running, Bool.false_eq_true, ite_false, selected]
    have zeroTest := tail_difference_zero start count nodes countFits nodesFits
    by_cases complete : count = nodes
    · have zero := zeroTest.mpr complete
      simp only [ite_eq_left zero, tested, ite_eq_left complete]
    · have nonzero : (word width (Nat.xor (start + count) (start + nodes))).val ≠ 0 :=
        fun zero => complete (zeroTest.mp zero)
      simp only [ite_eq_right nonzero, tested, ite_eq_right complete]
      rw [← nextPC]
  refine ⟨tested, ?_, rfl, rfl, rfl, running, rfl⟩
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.cons t4 (Execution.refl tested)))))
  simpa only [tested, s4, s3, s2, s1, State.liveWords, State.advance, State.put,
    Nat.max_self, Nat.reduceAdd] using trace

private theorem terminal_tail_classification (resident : Program width 8)
    (entry accept tail start count nodes tag : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 8 < 2 ^ width) (tailFits : tail < 2 ^ width)
    (actualTail : state.heap[tail]? = some (word width (start + count)))
    (countFits : start + count < 2 ^ width) (nodesFits : start + nodes < 2 ^ width)
    (present : ∀ phase : Fin 8, resident[entry + phase.val]? =
      (terminalCycleCode width tail (start + nodes) accept tag)[phase.val]?) :
    (count = nodes ∧ ∃ final, Execution resident state final 5 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width accept ∧ final.halted = false) ∨
    (count ≠ nodes ∧ ∃ final, Execution resident state final 8 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = word width tag :: state.output ∧ final.halted = true) := by
  obtain ⟨tested, testTrace, testHeap, testStack, testOutput, testRunning, testPC⟩ :=
    terminal_tail_test_execution resident entry accept tail start count nodes tag state
      position running room tailFits actualTail countFits nodesFits present
  by_cases complete : count = nodes
  · exact Or.inl ⟨complete, tested, testTrace, testHeap, testStack, testOutput,
      by simpa only [ite_eq_left complete] using testPC, testRunning⟩
  · have tagAt : resident[(entry + 5)]? = some (.constant 0 (word width tag)) := by
      simpa [terminalCycleCode] using present ⟨5, by decide⟩
    have emitAt : resident[(entry + 5) + 1]? = some (.emit 0) := by
      simpa [terminalCycleCode, Nat.add_assoc] using present ⟨6, by decide⟩
    have haltAt : resident[(entry + 5) + 2]? = some .halt := by
      simpa [terminalCycleCode, Nat.add_assoc] using present ⟨7, by decide⟩
    obtain ⟨emitted, emission, emitHeap, emitStack, emitOutput, _, emitPC, emitRunning⟩ :=
      Controller.Horn.WorklistAccept.tag_execution resident (entry + 5) tag tested tagAt emitAt
        (by simpa only [ite_eq_right complete] using testPC) testRunning (by omega)
    obtain ⟨final, terminal, finalHeap, finalStack, finalOutput, finalHalted⟩ :=
      Controller.Horn.WorklistAccept.halt_execution resident ((entry + 5) + 2) emitted
        haltAt emitPC emitRunning (by omega)
    have testedLive : tested.liveWords = state.liveWords := by
      unfold State.liveWords
      rw [testHeap, testStack, testOutput]
    have emittedLive : emitted.liveWords = state.liveWords + 1 := by
      unfold State.liveWords
      rw [emitHeap, emitStack, emitOutput, testHeap, testStack, testOutput]
      simp only [List.length_cons]
      omega
    refine Or.inr ⟨complete, final, ?_, finalHeap.trans (emitHeap.trans testHeap),
      finalStack.trans (emitStack.trans testStack), ?_, finalHalted⟩
    · simpa only [testedLive, emittedLive, Nat.reduceAdd,
        show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega,
        Nat.max_self] using (testTrace.append emission).append terminal
    · rw [finalOutput, emitOutput, testOutput]

-- Private consumer of actual ordered runtime terminal postconditions.
private theorem terminal_queue_complete (graph : UnorderedDAG n)
    (queue : List (Fin graph.nodeCount)) (distinct : queue.Nodup)
    (length : queue.length = graph.nodeCount) : ∀ node, node ∈ queue := by
  have card : queue.toFinset.card = graph.nodeCount :=
    (List.toFinset_card_of_nodup distinct).trans length
  have universal : queue.toFinset = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by simpa only [Finset.card_univ, Fintype.card_fin, card] using Nat.le_refl graph.nodeCount)
  intro node
  have member : node ∈ queue.toFinset := by rw [universal]; simp
  exact List.mem_toFinset.mp member

private theorem terminal_queue_cycle_iff (graph : UnorderedDAG n)
    (queue : List (Fin graph.nodeCount))
    (fired : Fin (RawDependencyOrder.dependencyClauses graph).length → Bool)
    (complete : Controller.Horn.WorklistOutcome.EnabledComplete
      (RawDependencyOrder.dependencyClauses graph) queue fired)
    (meaning : Controller.Horn.WorklistOutcome.FiredMeaning
      (RawDependencyOrder.dependencyClauses graph) queue fired)
    (distinct : queue.Nodup) (ordered : RawDependencyOrder.DependencyOrder graph queue) :
    queue.length = graph.nodeCount ↔ graph.Acyclic := by
  constructor
  · intro length
    exact (RawDependencyOrder.numbering graph queue distinct
      (terminal_queue_complete graph queue distinct length) ordered).acyclic
  · intro acyclic
    exact (RawDependencyOrder.terminal_numbering graph acyclic queue fired complete meaning
      distinct ordered).length_eq_nodeCount

private theorem encoded_cycle_iff (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (queue : List (Fin graph.nodeCount)) (fired : Fin clauses.length → Bool)
    (complete : Controller.Horn.WorklistOutcome.EnabledComplete clauses queue fired)
    (meaning : Controller.Horn.WorklistOutcome.FiredMeaning clauses queue fired)
    (distinct : queue.Nodup) (ordered : RawDependencyOrder.DependencyOrder graph queue) :
    queue.length = graph.nodeCount ↔ graph.Acyclic := by
  cases source
  exact terminal_queue_cycle_iff graph queue fired complete meaning distinct ordered


theorem saved_dependency_classified_execution (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (resident : Program width 8) (saveEntry coldDelta conflict : Nat)
    (originalHeap : Array (Word width)) (state : State width 8)
    (heap : state.heap = originalHeap ++ Controller.Horn.SourceSerialize.heap (width := width) clauses)
    (position : state.pc = word width saveEntry) (running : state.halted = false)
    (transferCapacity : saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size + 2 < 2 ^ width)
    (sourceFits : originalHeap.size + (Controller.Horn.SourceSerialize.heap (width := width) clauses).size ≤ 2 ^ width)
    (saveAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident saveEntry
      (sourceSaveCode width originalHeap.size (Controller.Horn.SourceSerialize.heap (width := width) clauses).size))
    (releaseAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size)
      (packetReleaseCode width state.heap.size))
    (handoff0 : resident[saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size]? = some (.constant 6 (word width 0)))
    (handoff1 : resident[saveEntry + 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
      state.heap.size + 1]? = some (.branchZero 6 (word width coldDelta)))
    (coldAt : RelocatedCodeAt resident
      (Controller.Horn.WorklistSeedRun.program width clauses conflict) coldDelta)
    (coldCapacity : coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width)
    (runtimeAt : ∀ phase : Fin 61,
      resident[(coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size) + phase.val]? =
        (dependencyRuntimeCode width graph.nodeCount (Controller.Horn.SourceSerialize.base clauses)
          (coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size) conflict)[phase.val]?)
    (runtimeCapacity : coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size + 61 < 2 ^ width)
    (accept tag : Nat)
    (cycleAt : ∀ phase : Fin 8,
      resident[(coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size + 61) + phase.val]? =
        (terminalCycleCode width
          (Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses))
          (Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses) + graph.nodeCount)
          accept tag)[phase.val]?)
    (cycleCapacity : coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size + 61 + 8 < 2 ^ width) :
    ∃ queue final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ 3 * (Controller.Horn.SourceSerialize.heap (width := width) clauses).size + state.heap.size +
        51 * graph.nodeCount + 115 * (clauses.map List.length).sum + 131 * clauses.length + 99 ∧
      peak ≤ state.liveWords + (Controller.Horn.SourceSerialize.heap (width := width) clauses).size +
        5 * graph.nodeCount + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum + 1 ∧
      Controller.Horn.WorklistMark.Stored queue (Controller.Horn.SourceSerialize.base clauses) final.heap ∧
      RawDependencyOrder.DependencyOrder graph queue ∧ queue.Nodup ∧
      final.stack = state.stack ∧
      ((graph.Acyclic ∧ queue.length = graph.nodeCount ∧ final.pc = word width accept ∧ final.halted = false ∧ final.output = state.output) ∨
       (¬graph.Acyclic ∧ final.halted = true ∧ final.output = word width tag :: state.output)) := by
  obtain ⟨recordEnd, queue, fired, finished, fifoTicks, fifoPeak, fifoTrace, fifoCost,
    fifoSpace, fifoStack, fifoOutput, done, enabled, meaning, forced, ordered, distinct⟩ :=
    saved_dependency_fifo_execution graph clauses source resident saveEntry coldDelta conflict originalHeap
      state heap position running transferCapacity sourceFits saveAt releaseAt handoff0 handoff1
      coldAt coldCapacity heapFits runtimeAt runtimeCapacity
  have queueBound := Controller.Horn.WorklistMark.enqueue_bound queue distinct
  have scratchRoom := done.fifo.fits
  have heapRoom := done.room
  have tailFits : Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount)
      (Controller.Horn.SourceSerialize.base clauses) < 2 ^ width := by
    unfold Controller.Horn.WorklistBucketReady.tailSlot
    omega
  have actualFits : Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount)
      (Controller.Horn.SourceSerialize.base clauses) + queue.length < 2 ^ width := by
    unfold Controller.Horn.WorklistMark.queueStart
    omega
  have expectedFits : Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount)
      (Controller.Horn.SourceSerialize.base clauses) + graph.nodeCount < 2 ^ width := by
    unfold Controller.Horn.WorklistMark.queueStart
    omega
  have semantic := encoded_cycle_iff graph clauses source queue fired enabled meaning distinct ordered
  have finishedLive : finished.liveWords ≤ fifoPeak := execution_final_live resident fifoTrace
  rcases terminal_tail_classification resident
    (coldDelta + (Controller.Horn.WorklistSeedRun.program width clauses conflict).size + 61) accept
    (Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses))
    (Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses))
    queue.length graph.nodeCount tag finished done.position done.running cycleCapacity tailFits
    done.tailValue actualFits expectedFits cycleAt with accepted | rejected
  · rcases accepted with ⟨complete, final, testTrace, testHeap, testStack, testOutput, testPC, testRunning⟩
    refine ⟨queue, final, fifoTicks + 5, fifoPeak, ?_, by omega, by omega, ?_, ordered, distinct,
      testStack.trans fifoStack, Or.inl ⟨semantic.mp complete, complete, testPC, testRunning, testOutput.trans fifoOutput⟩⟩
    · simpa only [Nat.max_eq_left finishedLive] using fifoTrace.append testTrace
    · simpa only [testHeap] using done.fifo
  · rcases rejected with ⟨incomplete, final, testTrace, testHeap, testStack, testOutput, testHalted⟩
    refine ⟨queue, final, fifoTicks + 8, max fifoPeak (finished.liveWords + 1), fifoTrace.append testTrace,
      by omega, by omega, ?_, ordered, distinct, testStack.trans fifoStack, Or.inr ⟨?_, testHalted, ?_⟩⟩
    · simpa only [testHeap] using done.fifo
    · exact fun acyclic => incomplete (semantic.mpr acyclic)
    · rw [testOutput, fifoOutput]

open Controller.Horn.IndexScanCold Controller.Horn.IndexScanWhole in
private theorem cold_index_with_end (clauses : List (Controller.CNF.Clause (Fin n)))
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (codeFits : (Controller.Horn.IndexScanCold.program width clauses).size < 2 ^ width)
    (heapFits : recordStart width clauses + 3 * clauses.length + 3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ final : State width 8, ∃ recordEnd ticks peak : Nat,
      Execution (Controller.Horn.IndexScanCold.program width clauses) state final ticks peak ∧
      Controller.Horn.IndexScan.PhysicalIndex clauses (recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses)
        (Controller.Horn.IndexScan.occurrences clauses (recordStart width clauses)).length final.heap ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap ∧
      Stored ([] : List (Fin n)) (Controller.Horn.SourceSerialize.base clauses) final.heap ∧
      final.reg 7 = word width final.heap.size ∧
      final.pc = word width (Controller.Horn.IndexScanCold.program width clauses).size ∧ final.halted = false ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.heap.size < 2 ^ width ∧ final.stack = suffix ∧ final.output = state.output ∧
      ticks ≤ 25 * n + 83 * (clauses.map List.length).sum + 95 * clauses.length + 66 ∧
      peak ≤ state.liveWords + 5 * n + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum := by
  obtain ⟨normalized, marks, normalizeTicks, normalizePeak, normalizeTrace, invariant,
      normalizePosition, normalizeStack, normalizeOutput, normalizeCost, normalizeStorage⟩ :=
    Controller.Horn.NormalizeCold.execution clauses state suffix emptyHeap input position running dual
      (by have := Controller.Horn.IndexScanCold.program_size (width := width) clauses; unfold entry at this; omega)
      (by unfold recordStart at heapFits; omega)
  have physical := Controller.Horn.IndexScan.initial clauses (Controller.Horn.SourceSerialize.layout clauses)
    (recordStart width clauses) marks normalized invariant
  have header : Controller.Horn.SourceScan.CursorStored normalized.heap.size 0 normalized.heap := by
    simpa [Controller.Horn.SourceSerialize.layout] using invariant.recordCursor
  have endpoints := invariant.records.endpoint
  have packed := packed_endpoint clauses (recordStart width clauses)
  have incidences := occurrences_length_le clauses (recordStart width clauses)
  have scanRoom : normalized.heap.size +
      2 * (Controller.Horn.IndexScan.occurrences clauses (recordStart width clauses)).length < 2 ^ width := by
    change normalized.heap.size = Controller.Horn.NormalizeLoop.recordOffset clauses (recordStart width clauses) clauses.length at endpoints
    omega
  obtain ⟨final, scanTrace, result, finalClean⟩ := Controller.Horn.WorklistEnqueue.all_rows_clean
    (Controller.Horn.IndexScanCold.program width clauses) clauses (recordStart width clauses) normalized.heap.size
    (Controller.Horn.SourceSerialize.base clauses) (entry width clauses) normalized
    (index_at clauses) physical header (cold_base_positive clauses) normalizePosition
    invariant.input.running invariant.input.zero invariant.input.one
    (Controller.Horn.WorklistEnqueue.normalized_clean_off clauses (Controller.Horn.SourceSerialize.layout clauses)
      (recordStart width clauses) clauses.length marks normalized invariant)
    (by simpa only [Controller.Horn.IndexScanCold.program_size] using codeFits) scanRoom
  let full := (append_execution _ _ normalizeTrace).append scanTrace
  refine ⟨final, normalized.heap.size, normalizeTicks +
    (16 * (Controller.Horn.IndexScan.occurrences clauses (recordStart width clauses)).length + 18 * clauses.length + 6),
    max normalizePeak (normalized.liveWords + 2 * (Controller.Horn.IndexScan.occurrences clauses (recordStart width clauses)).length),
    full, result.physical, result.header, empty_fifo_of_cold clauses _ _ result.physical finalClean, result.allocationHeld,
    ?_, result.running, result.zero.trans invariant.input.zero, result.one.trans invariant.input.one,
    ?_, result.stack.trans normalizeStack, result.output.trans normalizeOutput, ?_, ?_⟩
  · simpa only [Controller.Horn.IndexScanCold.program_size] using result.position
  · have growth := result.growth
    omega
  · omega
  · have resident := normalizeTrace.final_storage_le
    omega


theorem end_saved_seed_execution (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (resident : Program width 8) (delta conflict : Nat)
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width delta) (running : state.halted = false)
    (coldAt : RelocatedCodeAt resident (Controller.Horn.IndexScanCold.program width clauses) delta)
    (pushAt : resident[delta + (Controller.Horn.IndexScanCold.program width clauses).size]? = some (.push 7))
    (setupAt : ∀ phase : Fin 9,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1) + phase.val]? =
        (coldSetupCode (n := graph.nodeCount) width (Controller.Horn.SourceSerialize.base clauses)
          (Controller.Horn.IndexScanCold.recordStart width clauses)
          (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10))[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := graph.nodeCount) resident
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)
    (capacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57 < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ recordEnd queue fired final ticks peak,
      Execution resident state final ticks peak ∧
      final.stack = word width final.heap.size :: suffix ∧ final.output = state.output ∧
      ticks ≤ 28 * graph.nodeCount + 83 * (clauses.map List.length).sum + 131 * clauses.length + 80 ∧
      peak ≤ state.liveWords + 5 * graph.nodeCount + 5 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      ScanInvariant clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses)
        (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57)
        clauses.length queue fired final ∧ RawDependencyOrder.DependencyOrder graph queue := by
  let low := { state with pc := word width 0 }
  obtain ⟨indexed, recordEnd, coldTicks, coldPeak, coldTrace, physical, header, fifo, allocation,
    indexedPC, indexedRunning, indexedZero, indexedOne, indexedRoom, indexedStack, indexedOutput,
    coldCost, coldSpace⟩ := cold_index_with_end clauses low suffix emptyHeap input rfl running
      (encoded_dual graph clauses source) (by omega) heapFits
  let actual := relocatedState delta indexed
  have residentCold := relocated_execution resident (Controller.Horn.IndexScanCold.program width clauses)
    delta coldAt (by omega) coldTrace
  have sourceView : relocatedState delta low = state := relocated_zero_view delta state position
  rw [sourceView] at residentCold
  have actualPC : actual.pc = word width (delta + (Controller.Horn.IndexScanCold.program width clauses).size) := by
    change word width (indexed.pc.val + delta) = _
    rw [indexedPC, show (word width (Controller.Horn.IndexScanCold.program width clauses).size).val =
      (Controller.Horn.IndexScanCold.program width clauses).size from Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  let pushed : State width 8 := { actual.advance with stack := actual.reg 7 :: actual.stack }
  have pushTransition : programStep resident actual = some pushed := by
    rw [fetched resident actual (delta + (Controller.Horn.IndexScanCold.program width clauses).size)
      (.push 7) actualPC (by omega) pushAt]
    simp only [step, show actual.halted = false from indexedRunning, Bool.false_eq_true,
      ite_false, pushed]
  have pushedLiveScalar : pushed.liveWords = actual.liveWords + 1 := by
    simp only [pushed, State.liveWords, State.advance, List.length_cons]
    omega
  have pushTrace : Execution resident actual pushed 1 (actual.liveWords + 1) := by
    have trace := Execution.cons pushTransition (Execution.refl pushed)
    simpa only [pushedLiveScalar,
      Nat.max_eq_right (show actual.liveWords ≤ actual.liveWords + 1 by omega),
      Nat.reduceAdd] using trace
  have pushedPC : pushed.pc = word width (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1) := by
    exact referenceAdvancePC actual _ actualPC (by omega)
  have separated : Controller.Horn.SourceSerialize.base clauses + 5 * graph.nodeCount + 4 ≤
      Controller.Horn.IndexScanCold.recordStart width clauses := by
    simp [Controller.Horn.IndexScanCold.recordStart, Controller.Horn.NormalizeCold.words]
  obtain ⟨started, setupTrace, initial, setupSize, setupStack, setupOutput⟩ :=
    initial_scan_execution clauses (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
      pushed resident physical header fifo separated setupAt pushedPC indexedRunning indexedZero
      indexedOne indexedRoom (by omega)
  obtain ⟨queue, fired, final, seedTicks, growth, queueBound, seedCost, seedTrace,
    seedSize, seedStack, seedOutput, outcome⟩ := ordered_seed_scan graph clauses
      (encoded_dependencies graph clauses source) (Controller.Horn.IndexScanCold.recordStart width clauses)
      recordEnd (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57)
      conflict resident scanAt separated (by omega) clauses.length 0 [] (fun _ => false) started
      (by omega) initial (RawDependencyOrder.empty_order graph)
  have pushedLive : pushed.liveWords = indexed.liveWords + 1 := by
    simp only [pushed, actual, relocatedState, State.liveWords, State.advance, List.length_cons]
    omega
  have startedLive : started.liveWords = indexed.liveWords + 1 := by
    unfold State.liveWords at pushedLive ⊢
    rw [setupSize, setupStack, setupOutput]
    exact pushedLive
  have finalSize : final.heap.size = indexed.heap.size := seedSize.trans setupSize
  have indexedLive : indexed.liveWords ≤ coldPeak := execution_final_live _ coldTrace
  rcases outcome with impossible | ⟨seed, ordered⟩
  · exact False.elim (impossible.2.2 ⟨fun _ => false, encoded_false_model graph clauses source⟩)
  · refine ⟨recordEnd, queue, fired, final, coldTicks + 1 + 9 + seedTicks,
      max coldPeak (indexed.liveWords + 1), ?_, ?_, seedOutput.trans (setupOutput.trans indexedOutput),
      ?_, ?_, seed, ordered⟩
    · have trace := ((residentCold.append pushTrace).append setupTrace).append seedTrace
      simpa only [actual, relocatedState_live, pushedLive, startedLive, Nat.max_self,
        Nat.max_assoc] using trace
    · rw [seedStack, setupStack]
      change indexed.reg 7 :: indexed.stack = word width final.heap.size :: suffix
      rw [allocation, indexedStack, finalSize]
    · simp only [List.length_nil, Nat.sub_zero] at seedCost
      omega
    · have lowLive : low.liveWords = state.liveWords := rfl
      rw [lowLive] at coldSpace
      omega



theorem end_saved_fifo_execution (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (resident : Program width 8) (delta conflict : Nat)
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width delta) (running : state.halted = false)
    (coldAt : RelocatedCodeAt resident (Controller.Horn.IndexScanCold.program width clauses) delta)
    (pushAt : resident[delta + (Controller.Horn.IndexScanCold.program width clauses).size]? = some (.push 7))
    (setupAt : ∀ phase : Fin 9,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1) + phase.val]? =
        (coldSetupCode (n := graph.nodeCount) width (Controller.Horn.SourceSerialize.base clauses)
          (Controller.Horn.IndexScanCold.recordStart width clauses)
          (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10))[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := graph.nodeCount) resident
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)
    (capacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57 < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width)
    (runtimeAt : ∀ phase : Fin 61,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) + phase.val]? =
        (dependencyRuntimeCode width graph.nodeCount (Controller.Horn.SourceSerialize.base clauses)
          (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)[phase.val]?)
    (runtimeCapacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118 < 2 ^ width) :
    ∃ recordEnd queue fired final ticks peak,
      Execution resident state final ticks peak ∧
      final.stack = word width final.heap.size :: suffix ∧ final.output = state.output ∧
      ticks ≤ 51 * graph.nodeCount + 115 * (clauses.map List.length).sum + 131 * clauses.length + 90 ∧
      peak ≤ state.liveWords + 5 * graph.nodeCount + 5 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      Controller.Horn.WorklistFIFORun.Done clauses (Controller.Horn.IndexScanCold.recordStart width clauses)
        recordEnd (Controller.Horn.SourceSerialize.base clauses)
        (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118) queue fired final ∧
      Controller.Horn.WorklistOutcome.EnabledComplete clauses queue fired ∧
      Controller.Horn.WorklistOutcome.FiredMeaning clauses queue fired ∧
      Controller.Horn.WorklistSeed.QueueForced clauses queue ∧
      RawDependencyOrder.DependencyOrder graph queue ∧ queue.Nodup := by
  obtain ⟨recordEnd, seededQueue, seededFired, seeded, seedTicks, seedPeak, seedTrace,
    seedStack, seedOutput, seedCost, seedSpace, seed, seededOrder⟩ :=
    end_saved_seed_execution graph clauses source resident delta conflict state suffix emptyHeap input
      position running coldAt pushAt setupAt scanAt capacity heapFits
  obtain ⟨headAt, fetchAt, loopAt, readyAt, advanceAt⟩ := dependencyRuntime_at resident
    (Controller.Horn.SourceSerialize.base clauses)
    (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict runtimeAt
  have separated : Controller.Horn.SourceSerialize.base clauses + 5 * graph.nodeCount + 4 ≤
      Controller.Horn.IndexScanCold.recordStart width clauses := by
    simp [Controller.Horn.IndexScanCold.recordStart, Controller.Horn.NormalizeCold.words]
  obtain ⟨queue, fired, final, fifoTicks, ordered, distinct, fifoTrace, fifoCost,
    finalSize, finalStack, finalOutput, done, enabled, meaning, forced⟩ :=
    dependency_fifo_after_seed graph clauses source resident
      (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict
      seededQueue seededFired seeded seed seededOrder separated headAt fetchAt advanceAt loopAt readyAt
      (by omega)
  have finalLive := execution_final_live resident seedTrace
  have incidences := Controller.Horn.IndexScanCold.occurrences_length_le clauses
    (Controller.Horn.IndexScanCold.recordStart width clauses)
  refine ⟨recordEnd, queue, fired, final, seedTicks + fifoTicks, seedPeak, ?_, ?_,
    finalOutput.trans seedOutput, by omega, seedSpace, ?_, enabled, meaning, forced, ordered, distinct⟩
  · simpa only [Nat.max_eq_left finalLive] using seedTrace.append fifoTrace
  · rw [finalStack, seedStack, finalSize]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using done

private theorem actual_index_heap_bound
    (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (heap : Array (Word width))
    (spine : Controller.Horn.WorklistPropagation.Spine clauses recordStart recordEnd base heap) :
    heap.size ≤ recordStart + 3 * clauses.length + 3 * (clauses.map List.length).sum := by
  have actual := spine.endpoint
  rw [spine.originalEnd, Controller.Horn.IndexScanCold.packed_endpoint] at actual
  have incidenceBound := Controller.Horn.IndexScanCold.occurrences_length_le clauses recordStart
  omega


theorem end_saved_classified_execution (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (resident : Program width 8) (delta conflict : Nat)
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width delta) (running : state.halted = false)
    (coldAt : RelocatedCodeAt resident (Controller.Horn.IndexScanCold.program width clauses) delta)
    (pushAt : resident[delta + (Controller.Horn.IndexScanCold.program width clauses).size]? = some (.push 7))
    (setupAt : ∀ phase : Fin 9,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1) + phase.val]? =
        (coldSetupCode (n := graph.nodeCount) width (Controller.Horn.SourceSerialize.base clauses)
          (Controller.Horn.IndexScanCold.recordStart width clauses)
          (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10))[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := graph.nodeCount) resident
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)
    (capacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57 < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width)
    (runtimeAt : ∀ phase : Fin 61,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) + phase.val]? =
        (dependencyRuntimeCode width graph.nodeCount (Controller.Horn.SourceSerialize.base clauses)
          (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)[phase.val]?)
    (runtimeCapacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118 < 2 ^ width)
    (accept tag : Nat)
    (cycleAt : ∀ phase : Fin 8,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118) + phase.val]? =
        (terminalCycleCode width
          (Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses))
          (Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses) + graph.nodeCount)
          accept tag)[phase.val]?)
    (cycleCapacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 126 < 2 ^ width) :
    ∃ queue final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ 51 * graph.nodeCount + 115 * (clauses.map List.length).sum + 131 * clauses.length + 98 ∧
      peak ≤ state.liveWords + 5 * graph.nodeCount + 6 + 3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      Controller.Horn.WorklistMark.Stored queue (Controller.Horn.SourceSerialize.base clauses) final.heap ∧
      RawDependencyOrder.DependencyOrder graph queue ∧ queue.Nodup ∧
      final.stack = word width final.heap.size :: suffix ∧
      final.heap.size ≤ Controller.Horn.IndexScanCold.recordStart width clauses +
        3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      ((graph.Acyclic ∧ queue.length = graph.nodeCount ∧ final.pc = word width accept ∧ final.halted = false ∧ final.output = state.output) ∨
       (¬graph.Acyclic ∧ final.halted = true ∧ final.output = word width tag :: state.output)) := by
  obtain ⟨recordEnd, queue, fired, finished, fifoTicks, fifoPeak, fifoTrace, fifoStack,
    fifoOutput, fifoCost, fifoSpace, done, enabled, meaning, forced, ordered, distinct⟩ :=
    end_saved_fifo_execution graph clauses source resident delta conflict state suffix emptyHeap input
      position running coldAt pushAt setupAt scanAt capacity heapFits runtimeAt runtimeCapacity
  have actualHeapBound := actual_index_heap_bound clauses
    (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
    (Controller.Horn.SourceSerialize.base clauses) finished.heap done.spine
  have queueBound := Controller.Horn.WorklistMark.enqueue_bound queue distinct
  have scratchRoom := done.fifo.fits
  have heapRoom := done.room
  have tailFits : Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount)
      (Controller.Horn.SourceSerialize.base clauses) < 2 ^ width := by
    unfold Controller.Horn.WorklistBucketReady.tailSlot
    omega
  have actualFits : Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount)
      (Controller.Horn.SourceSerialize.base clauses) + queue.length < 2 ^ width := by
    unfold Controller.Horn.WorklistMark.queueStart
    omega
  have expectedFits : Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount)
      (Controller.Horn.SourceSerialize.base clauses) + graph.nodeCount < 2 ^ width := by
    unfold Controller.Horn.WorklistMark.queueStart
    omega
  have semantic := encoded_cycle_iff graph clauses source queue fired enabled meaning distinct ordered
  have finishedLive : finished.liveWords ≤ fifoPeak := execution_final_live resident fifoTrace
  rcases terminal_tail_classification resident
    (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118) accept
    (Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses))
    (Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses))
    queue.length graph.nodeCount tag finished done.position done.running cycleCapacity tailFits
    done.tailValue actualFits expectedFits cycleAt with accepted | rejected
  · rcases accepted with ⟨complete, final, testTrace, testHeap, testStack, testOutput, testPC, testRunning⟩
    refine ⟨queue, final, fifoTicks + 5, fifoPeak, ?_, by omega, by omega, ?_, ordered, distinct,
      by rw [testStack, fifoStack, testHeap], by simpa only [testHeap] using actualHeapBound, Or.inl ⟨semantic.mp complete, complete, testPC, testRunning, testOutput.trans fifoOutput⟩⟩
    · simpa only [Nat.max_eq_left finishedLive] using fifoTrace.append testTrace
    · simpa only [testHeap] using done.fifo
  · rcases rejected with ⟨incomplete, final, testTrace, testHeap, testStack, testOutput, testHalted⟩
    refine ⟨queue, final, fifoTicks + 8, max fifoPeak (finished.liveWords + 1), fifoTrace.append testTrace,
      by omega, by omega, ?_, ordered, distinct, by rw [testStack, fifoStack, testHeap], by simpa only [testHeap] using actualHeapBound, Or.inr ⟨?_, testHalted, ?_⟩⟩
    · simpa only [testHeap] using done.fifo
    · exact fun acyclic => incomplete (semantic.mpr acyclic)
    · rw [testOutput, fifoOutput]

private theorem restore_end_reload_execution (resident : Program width 8) (entry : Nat)
    (state : State width 8) (packet suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = word width state.heap.size :: (packet ++ suffix))
    (popAt : resident[entry]? = some (.pop 4))
    (reloadAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident (entry + 1)
      (Controller.Cost.InputLoad.code (width := width) packet.length))
    (capacity : entry + 1 + 2 * packet.length < 2 ^ width)
    (room : state.heap.size + packet.length ≤ 2 ^ width) :
    ∃ final, Execution resident state final (1 + 2 * packet.length) state.liveWords ∧
      final.heap = state.heap ++ packet.toArray ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.reg 4 = word width state.heap.size ∧
      final.pc = word width (entry + 1 + 2 * packet.length) ∧ final.halted = false ∧
      (∀ address, address < state.heap.size → final.heap[address]? = state.heap[address]?) := by
  let restored : State width 8 := { state.advance.put 4 (word width state.heap.size)
    with stack := packet ++ suffix }
  have transition : programStep resident state = some restored := by
    rw [fetched resident state entry (.pop 4) position (by omega) popAt]
    simp only [step, running, Bool.false_eq_true, ite_false, saved, restored]
  have restoredPC : restored.pc = word width (entry + 1) :=
    referenceAdvancePC state entry position (by omega)
  have restoredLive : restored.liveWords + 1 = state.liveWords := by
    simp only [restored, State.liveWords, State.advance, State.put, saved,
      List.length_cons, List.length_append]
    omega
  have popTrace : Execution resident state restored 1 state.liveWords := by
    have trace := Execution.cons transition (Execution.refl restored)
    simpa only [show max state.liveWords restored.liveWords = state.liveWords from
      Nat.max_eq_left (by omega), Nat.reduceAdd] using trace
  obtain ⟨final, reloadTrace, heap, stack, output, pc, active, registers, retained⟩ :=
    source_reload_execution resident (entry + 1) restored packet suffix restoredPC running rfl
      (by omega) room reloadAt
  refine ⟨final, ?_, heap, stack, output, ?_, pc, active, retained⟩
  · simpa only [show max state.liveWords restored.liveWords = state.liveWords from
      Nat.max_eq_left (by omega)] using popTrace.append reloadTrace
  · exact registers 4 (by decide)

private theorem rank_zero_append_execution (resident : Program width 8) (entry nodes : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (codeFits : entry + 2 * nodes < 2 ^ width)
    (room : state.heap.size + nodes ≤ 2 ^ width)
    (present : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident entry
      (Controller.Cost.Initialize.code (word width 0) nodes)) :
    ∃ final, Execution resident state final (2 * nodes) (state.liveWords + nodes) ∧
      final.heap = state.heap ++ (List.replicate nodes (word width 0)).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2 * nodes) ∧ final.halted = false ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let low := markerNarrow state
  let view := Controller.Cost.ForestZeroCallerWiden.lowerProgram resident
  have lowBlock := Controller.Cost.ForestZeroCallerWiden.lower_block resident entry
    (Controller.Cost.Initialize.code (word width 0) nodes) present
  obtain ⟨last, trace, heap, stack, output, pc, active⟩ :=
    Controller.Cost.Initialize.code_execution view low (word width 0) entry nodes
      position running codeFits room lowBlock
  have lifted := Controller.Cost.ForestZeroCallerWiden.execution resident low last
    (2 * nodes) (low.liveWords + nodes) trace active state.reg
  have sourceLive : low.liveWords + 4 = state.liveWords := by
    simp only [low, markerNarrow, State.liveWords]
    omega
  let final := Controller.Cost.RegisterWiden.widenState last state.reg
  refine ⟨final, ?_, heap, stack, output, pc, active, ?_⟩
  · rw [markerWidenNarrow] at lifted
    simpa only [show low.liveWords + nodes + 4 = state.liveWords + nodes by omega] using lifted
  · intro register high
    exact Controller.Cost.RegisterWiden.widenState_high last state.reg register high

-- Private draft: consumed after restore_end_reload_execution and the actual V-zero append.
-- Register 4 is the popped, runtime-derived original index heap end H.
-- The raw source begins at H; its counted encoder size W is known before numbering.
-- The dead FIFO active header stores H while rankCopy uses register 4 for H+W.
def dynamicRankSetupCode (width nodes base rawWords rankEntry : Nat) : Program width 8 :=
  #[.constant 5 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)),
    .store 5 4,
    .constant 5 (word width rawWords),
    .add 4 4 5,
    .constant 0 (word width nodes),
    .constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)),
    .constant 2 (word width 0),
    .constant 3 (word width 1),
    .constant 6 (word width 0),
    .constant 7 (word width (2 ^ width - 1)),
    .branchZero 6 (word width rankEntry)]

-- Required consumer postcondition, derived by the eleven fetched instructions:
-- actual heap = (finished.heap ++ rawPacket.toArray ++ replicate V zero).setIfInBounds activeSlot (word H)
-- actual reg4 = word(H+W), reg1 = queueStart, reg2=0, reg0=V, reg3=1, reg6=0, reg7=mask.
-- rankBase+V=heap.size and prefix Q cells unchanged because activeSlot<queueStart.
-- Source cells [H,H+W) and new rank zero cells [H+W,H+W+V) remain exact.
-- Cost 11 ticks, no allocation, liveWords unchanged. Followed by existing rank_copy_execution:
-- 8V+1 ticks after actual accepted Q.length=V; old rank and original numbering derived from QStored.
-- No supplied rank oracle and no program immediate depending on H or deduplicated occurrence count.

private theorem dynamic_rank_setup_execution (resident : Program width 8)
    (entry nodes base rawWords rankEntry heapEnd : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 11 < 2 ^ width)
    (rankFits : heapEnd + rawWords < 2 ^ width)
    (headerFits : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < 2 ^ width)
    (headerBound : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < state.heap.size)
    (held : state.reg 4 = word width heapEnd)
    (physical : ∀ phase : Fin 11, resident[entry + phase.val]? =
      (dynamicRankSetupCode width nodes base rawWords rankEntry)[phase.val]?) :
    ∃ final, Execution resident state final 11 state.liveWords ∧
      final.heap = state.heap.set
        (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width heapEnd) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width rankEntry ∧ final.halted = false ∧
      final.reg 0 = word width nodes ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base) ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧
      final.reg 4 = word width (heapEnd + rawWords) ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) := by
  let s1 := state.advance.put 5 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))
  let s2 : State width 8 := { s1.advance with heap :=
    (state.heap.set (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width heapEnd)) }
  let s3 := s2.advance.put 5 (word width rawWords)
  let s4 := s3.advance.put 4 (word width (heapEnd + rawWords))
  let s5 := s4.advance.put 0 (word width nodes)
  let s6 := s5.advance.put 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))
  let s7 := s6.advance.put 2 (word width 0)
  let s8 := s7.advance.put 3 (word width 1)
  let s9 := s8.advance.put 6 (word width 0)
  let s10 := s9.advance.put 7 (word width (2 ^ width - 1))
  let final : State width 8 := { s10.advance with pc := word width rankEntry }
  have headerValue : (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)).val =
      Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base := Nat.mod_eq_of_lt headerFits
  have heapEndValue : (word width heapEnd).val = heapEnd := Nat.mod_eq_of_lt (by omega)
  have rawValue : (word width rawWords).val = rawWords := Nat.mod_eq_of_lt (by omega)
  have pc1 : s1.pc = word width (entry + 1) := by
    change state.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC state (entry + 0) position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    change s5.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s5 (entry + 5) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 7) := by
    change s6.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s6 (entry + 6) pc6 (by omega)
  have pc8 : s8.pc = word width (entry + 8) := by
    change s7.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s7 (entry + 7) pc7 (by omega)
  have pc9 : s9.pc = word width (entry + 9) := by
    change s8.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s8 (entry + 8) pc8 (by omega)
  have pc10 : s10.pc = word width (entry + 10) := by
    change s9.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s9 (entry + 9) pc9 (by omega)
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 5 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) position (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨0, by decide⟩)]
    simp [s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.store 5 4) pc1 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨1, by decide⟩)]
    simp [s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.constant 5 (word width rawWords)) pc2 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨2, by decide⟩)]
    simp [s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.add 4 4 5) pc3 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨3, by decide⟩)]
    simp [s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.constant 0 (word width nodes)) pc4 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨4, by decide⟩)]
    simp [s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))) pc5 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨5, by decide⟩)]
    simp [s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 2 (word width 0)) pc6 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨6, by decide⟩)]
    simp [s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.constant 3 (word width 1)) pc7 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨7, by decide⟩)]
    simp [s8, s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.constant 6 (word width 0)) pc8 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨8, by decide⟩)]
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.constant 7 (word width (2 ^ width - 1))) pc9 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨9, by decide⟩)]
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t10 : programStep resident s10 = some final := by
    rw [fetched resident s10 (entry + 10) (.branchZero 6 (word width rankEntry)) pc10 (by omega)
      (by simpa [dynamicRankSetupCode] using physical ⟨10, by decide⟩)]
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue, word]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.refl final)))))))))))
  have heapSize : (state.heap.set (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)
      (word width heapEnd)).size = state.heap.size := by simp
  have live1 : s1.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live2 : s2.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live3 : s3.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live4 : s4.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live5 : s5.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live6 : s6.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live7 : s7.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live8 : s8.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live9 : s9.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live10 : s10.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have finalLive : final.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, finalLive, Nat.max_self,
      Nat.reduceAdd] using trace
  all_goals simp [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]

-- Consumer separation facts used after actual source reload and rank zero append.
private theorem active_header_source_separated (nodes base heapEnd : Nat)
    (scratch : base + 4 * nodes + 4 ≤ heapEnd) :
    Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < heapEnd ∧
    Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base <
      Controller.Horn.WorklistMark.queueStart (n := nodes) base := by
  unfold Controller.Horn.WorklistFIFO.activeSlot Controller.Horn.WorklistMark.queueStart
  omega

private theorem dynamic_header_queue_cell (heap : Array (Word width))
    (nodes base index : Nat) (value saved : Word width)
    (cell : heap[Controller.Horn.WorklistMark.queueStart (n := nodes) base + index]? = some value) :
    (heap.setIfInBounds (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) saved)[Controller.Horn.WorklistMark.queueStart (n := nodes) base + index]? = some value := by
  have different : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base ≠
      Controller.Horn.WorklistMark.queueStart (n := nodes) base + index := by
    unfold Controller.Horn.WorklistFIFO.activeSlot Controller.Horn.WorklistMark.queueStart
    omega
  by_cases valid : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < heap.size
  · simpa only [Array.setIfInBounds_def, dite_eq_left valid, Array.getElem?_set valid,
      ite_eq_right different] using cell
  · simpa only [Array.setIfInBounds_def, dite_eq_right valid] using cell

private theorem dynamic_header_original_cell (heap : Array (Word width))
    (nodes base heapEnd address : Nat) (value saved : Word width)
    (scratch : base + 4 * nodes + 4 ≤ heapEnd) (source : heapEnd ≤ address)
    (cell : heap[address]? = some value) :
    (heap.setIfInBounds (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) saved)[address]? = some value := by
  have different : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base ≠ address := by
    have := (active_header_source_separated nodes base heapEnd scratch).1
    omega
  by_cases valid : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < heap.size
  · simpa only [Array.setIfInBounds_def, dite_eq_left valid, Array.getElem?_set valid,
      ite_eq_right different] using cell
  · simpa only [Array.setIfInBounds_def, dite_eq_right valid] using cell


theorem accepted_rank_execution (resident : Program width 8)
    (entry nodes base rankDone : Nat) (state : State width 8)
    (packet suffix : List (Word width)) (queue : List (Fin nodes))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = word width state.heap.size :: (packet ++ suffix))
    (complete : queue.length = nodes) (distinct : queue.Nodup)
    (scratch : base + 4 * nodes + 4 ≤ state.heap.size)
    (cells : ∀ index : Fin queue.length,
      state.heap[Controller.Horn.WorklistMark.queueStart (n := nodes) base + index.val]? =
        some (word width queue[index.val].val))
    (capacity : entry + 1 + 2 * packet.length + 2 * nodes + 11 + 8 < 2 ^ width)
    (room : state.heap.size + packet.length + nodes < 2 ^ width)
    (popAt : resident[entry]? = some (.pop 4))
    (reloadAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident (entry + 1)
      (Controller.Cost.InputLoad.code (width := width) packet.length))
    (zeroAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (entry + 1 + 2 * packet.length) (Controller.Cost.Initialize.code (word width 0) nodes))
    (setupAt : ∀ phase : Fin 11,
      resident[(entry + 1 + 2 * packet.length + 2 * nodes) + phase.val]? =
        (dynamicRankSetupCode width nodes base packet.length
          (entry + 1 + 2 * packet.length + 2 * nodes + 11))[phase.val]?)
    (rankAt : ∀ phase : Fin 8,
      resident[(entry + 1 + 2 * packet.length + 2 * nodes + 11) + phase.val]? =
        (rankCopyCode width (entry + 1 + 2 * packet.length + 2 * nodes + 11) rankDone)[phase.val]?) :
    ∃ final peak, Execution resident state final (2 * packet.length + 10 * nodes + 13) peak ∧
      peak ≤ state.liveWords + nodes ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width rankDone ∧ final.halted = false ∧
      final.reg 4 = word width (state.heap.size + packet.length) ∧
      final.heap.size = state.heap.size + packet.length + nodes ∧
      (∀ index : Fin queue.length,
        final.heap[Controller.Horn.WorklistMark.queueStart (n := nodes) base + index.val]? =
          some (word width queue[index.val].val)) ∧
      (∀ index : Fin packet.length,
        final.heap[state.heap.size + index.val]? = some packet[index.val]) ∧
      (∀ index : Fin queue.length,
        final.heap[state.heap.size + packet.length + queue[index.val].val]? = some (word width index.val)) := by
  obtain ⟨loaded, loadTrace, loadedHeap, loadedStack, loadedOutput, loadedBase,
    loadedPC, loadedRunning, loadRetained⟩ := restore_end_reload_execution resident entry state packet suffix
      position running saved popAt reloadAt (by omega) (by omega)
  have loadedSize : loaded.heap.size = state.heap.size + packet.length := by
    rw [loadedHeap]; simp
  obtain ⟨zeroed, zeroTrace, zeroHeap, zeroStack, zeroOutput, zeroPC, zeroRunning, zeroRegisters⟩ :=
    rank_zero_append_execution resident (entry + 1 + 2 * packet.length) nodes loaded
      loadedPC loadedRunning (by omega) (by omega) zeroAt
  have zeroSize : zeroed.heap.size = state.heap.size + packet.length + nodes := by
    rw [zeroHeap]
    simp only [Array.size_append, List.size_toArray, List.length_replicate, loadedSize]
  have zeroBase : zeroed.reg 4 = word width state.heap.size :=
    (zeroRegisters 4 (by decide)).trans loadedBase
  have activeFits : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < 2 ^ width := by
    have := (active_header_source_separated nodes base state.heap.size scratch).1
    omega
  have activeBound : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < zeroed.heap.size := by
    have := (active_header_source_separated nodes base state.heap.size scratch).1
    omega
  obtain ⟨started, setupTrace, setupHeap, setupStack, setupOutput, setupPC, setupRunning,
    countReg, cursorReg, rankReg, oneReg, baseReg, zeroReg, maskReg⟩ := dynamic_rank_setup_execution
      resident (entry + 1 + 2 * packet.length + 2 * nodes) nodes base packet.length
      (entry + 1 + 2 * packet.length + 2 * nodes + 11) state.heap.size zeroed
      zeroPC zeroRunning (by omega) (by omega) activeFits activeBound zeroBase setupAt
  have startedSize : started.heap.size = state.heap.size + packet.length + nodes := by
    rw [setupHeap]; simpa using zeroSize
  have sourceCell : ∀ address value, state.heap[address]? = some value →
      address ≠ Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base → started.heap[address]? = some value := by
    intro address value original different
    have first := stored_after_append state.heap loaded.heap packet.toArray loadedHeap address value original
    have second := stored_after_append loaded.heap zeroed.heap
      (List.replicate nodes (word width 0)).toArray zeroHeap address value first
    rw [setupHeap, Array.getElem?_set activeBound, ite_eq_right (Ne.symm different)]
    exact second
  have queueCells : ∀ index : Fin (queue.map Fin.val).length,
      started.heap[Controller.Horn.WorklistMark.queueStart (n := nodes) base + index.val]? =
        some (word width (queue.map Fin.val)[index.val]) := by
    intro index
    have bound : index.val < queue.length := by simpa using index.isLt
    have cell := cells ⟨index.val, bound⟩
    have different : Controller.Horn.WorklistMark.queueStart (n := nodes) base + index.val ≠
        Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base := by
      have := (active_header_source_separated nodes base state.heap.size scratch).2
      omega
    simpa using sourceCell _ _ cell different
  obtain ⟨final, rankTrace, rankHeap, rankStack, rankOutput, rankPC, rankRunning,
    finalCount, finalCursor, finalRank, rankRegisters, rankRetained⟩ := rank_copy_execution
      resident (entry + 1 + 2 * packet.length + 2 * nodes + 11) rankDone
      (state.heap.size + packet.length) nodes rankAt (by omega) (queue.map Fin.val)
      (by intro old member; obtain ⟨label, _, rfl⟩ := List.mem_map.mp member; exact label.isLt)
      (Controller.Horn.WorklistMark.queueStart (n := nodes) base) 0 started
      setupPC setupRunning (by simpa [complete] using countReg) cursorReg rankReg oneReg baseReg zeroReg maskReg
      (by simp only [List.length_map, complete]; omega)
      (by simp only [List.length_map, complete]; unfold Controller.Horn.WorklistMark.queueStart; omega)
      (by simp only [List.length_map, complete]; omega) (by omega) (by omega) queueCells
  have loadedLive : loaded.liveWords + 1 = state.liveWords := by
    unfold State.liveWords
    rw [loadedHeap, loadedStack, loadedOutput, saved]
    simp only [Array.size_append, List.size_toArray, List.length_append, List.length_cons]
    omega
  have zeroLive : zeroed.liveWords = loaded.liveWords + nodes := by
    unfold State.liveWords
    rw [zeroHeap, zeroStack, zeroOutput]
    simp <;> omega
  have startedLive : started.liveWords = zeroed.liveWords := by
    unfold State.liveWords
    rw [setupHeap, setupStack, setupOutput]
    simp
  have full := ((loadTrace.append zeroTrace).append setupTrace).append rankTrace
  refine ⟨final, max (max (max state.liveWords (loaded.liveWords + nodes)) zeroed.liveWords) started.liveWords,
    ?_, by rw [zeroLive, startedLive]; omega, ?_, ?_, rankPC, rankRunning, ?_, ?_, ?_, ?_, ?_⟩
  · convert full using 1 <;> simp only [List.length_map, complete] <;> omega
  · rw [rankStack, setupStack, zeroStack, loadedStack]
  · rw [rankOutput, setupOutput, zeroOutput, loadedOutput]
  · exact (rankRegisters 4 (by decide) (by decide) (by decide) (by decide)).trans baseReg
  · rw [rankHeap, actualRankHeap_size, startedSize]
  · intro index
    rw [rankRetained _ (by have := index.isLt; unfold Controller.Horn.WorklistMark.queueStart; omega)]
    simpa using queueCells ⟨index.val, by simpa using index.isLt⟩
  · intro index
    have rawBound : state.heap.size + index.val < loaded.heap.size := by omega
    have loadedCell : loaded.heap[state.heap.size + index.val]? = some packet[index.val] := by
      rw [loadedHeap]
      rw [Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      simp only [List.getElem?_toArray, List.getElem?_eq_getElem index.isLt]
    have zeroCell := stored_after_append loaded.heap zeroed.heap
      (List.replicate nodes (word width 0)).toArray zeroHeap _ _ loadedCell
    have different : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base ≠ state.heap.size + index.val := by
      have := (active_header_source_separated nodes base state.heap.size scratch).1; omega
    rw [rankRetained _ (by omega), setupHeap, Array.getElem?_set activeBound, ite_eq_right different]
    exact zeroCell
  · intro index
    have bounded : ∀ old ∈ queue.map Fin.val, old < nodes := by
      intro old member; obtain ⟨label, _, rfl⟩ := List.mem_map.mp member; exact label.isLt
    have queueDistinct : (queue.map Fin.val).Nodup := distinct.map (by intro a b equal; exact Fin.ext equal)
    have lookup := actual_rank_lookup (state.heap.size + packet.length) 0 nodes
      (queue.map Fin.val) started.heap bounded (by omega) queueDistinct ⟨index.val, by simpa using index.isLt⟩
    rw [rankHeap]
    simpa using lookup


theorem classified_rank_execution (graph : UnorderedDAG channels)
    (clauses : List (Controller.CNF.Clause (Fin graph.nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses graph)
    (resident : Program width 8) (delta conflict : Nat)
    (state : State width 8) (packet suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ (packet ++ suffix))
    (position : state.pc = word width delta) (running : state.halted = false)
    (coldAt : RelocatedCodeAt resident (Controller.Horn.IndexScanCold.program width clauses) delta)
    (pushAt : resident[delta + (Controller.Horn.IndexScanCold.program width clauses).size]? = some (.push 7))
    (setupAt : ∀ phase : Fin 9,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1) + phase.val]? =
        (coldSetupCode (n := graph.nodeCount) width (Controller.Horn.SourceSerialize.base clauses)
          (Controller.Horn.IndexScanCold.recordStart width clauses)
          (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10))[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := graph.nodeCount) resident
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)
    (capacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57 < 2 ^ width)
    (heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ width)
    (runtimeAt : ∀ phase : Fin 61,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) + phase.val]? =
        (dependencyRuntimeCode width graph.nodeCount (Controller.Horn.SourceSerialize.base clauses)
          (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)[phase.val]?)
    (runtimeCapacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118 < 2 ^ width)
    (accept tag : Nat)
    (cycleAt : ∀ phase : Fin 8,
      resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118) + phase.val]? =
        (terminalCycleCode width
          (Controller.Horn.WorklistBucketReady.tailSlot (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses))
          (Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount) (Controller.Horn.SourceSerialize.base clauses) + graph.nodeCount)
          accept tag)[phase.val]?)
    (cycleCapacity : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 126 < 2 ^ width)
    (rankDone : Nat)
    (rankCapacity : accept + 1 + 2 * packet.length + 2 * graph.nodeCount + 19 < 2 ^ width)
    (rankRoom : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum + packet.length + graph.nodeCount < 2 ^ width)
    (popAt : resident[accept]? = some (.pop 4))
    (reloadAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1)
      (Controller.Cost.InputLoad.code (width := width) packet.length))
    (zeroAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (accept + 1 + 2 * packet.length) (Controller.Cost.Initialize.code (word width 0) graph.nodeCount))
    (rankSetupAt : ∀ phase : Fin 11,
      resident[(accept + 1 + 2 * packet.length + 2 * graph.nodeCount) + phase.val]? =
        (dynamicRankSetupCode width graph.nodeCount (Controller.Horn.SourceSerialize.base clauses) packet.length
          (accept + 1 + 2 * packet.length + 2 * graph.nodeCount + 11))[phase.val]?)
    (rankAt : ∀ phase : Fin 8,
      resident[(accept + 1 + 2 * packet.length + 2 * graph.nodeCount + 11) + phase.val]? =
        (rankCopyCode width (accept + 1 + 2 * packet.length + 2 * graph.nodeCount + 11) rankDone)[phase.val]?) :
    ∃ queue final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ 61 * graph.nodeCount + 115 * (clauses.map List.length).sum +
        131 * clauses.length + 2 * packet.length + 111 ∧
      peak ≤ state.liveWords + 6 * graph.nodeCount + 6 +
        3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      RawDependencyOrder.DependencyOrder graph queue ∧ queue.Nodup ∧
      ((graph.Acyclic ∧ queue.length = graph.nodeCount ∧
        final.pc = word width rankDone ∧ final.halted = false ∧
        final.stack = suffix ∧ final.output = state.output ∧
        ∃ originalEnd : Nat,
          final.reg 4 = word width (originalEnd + packet.length) ∧
          final.heap.size = originalEnd + packet.length + graph.nodeCount ∧
          (∀ index : Fin queue.length,
            final.heap[Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount)
              (Controller.Horn.SourceSerialize.base clauses) + index.val]? = some (word width queue[index.val].val)) ∧
          (∀ index : Fin packet.length,
            final.heap[originalEnd + index.val]? = some packet[index.val]) ∧
          (∀ index : Fin queue.length,
            final.heap[originalEnd + packet.length + queue[index.val].val]? = some (word width index.val))) ∨
       (¬graph.Acyclic ∧ final.halted = true ∧ final.output = word width tag :: state.output)) := by
  obtain ⟨queue, classified, classTicks, classPeak, classTrace, classCost, classSpace,
    stored, ordered, distinct, saved, heapBound, outcome⟩ :=
    end_saved_classified_execution graph clauses source resident delta conflict state (packet ++ suffix)
      emptyHeap input position running coldAt pushAt setupAt scanAt capacity heapFits runtimeAt runtimeCapacity
      accept tag cycleAt cycleCapacity
  rcases outcome with accepted | rejected
  · rcases accepted with ⟨acyclic, complete, classPC, classRunning, classOutput⟩
    have queueCells : ∀ index : Fin queue.length,
        classified.heap[Controller.Horn.WorklistMark.queueStart (n := graph.nodeCount)
          (Controller.Horn.SourceSerialize.base clauses) + index.val]? = some (word width queue[index.val].val) := by
      intro index
      rw [Array.getElem?_eq_getElem (by have := stored.queue.fits; have := index.isLt; omega)]
      exact congrArg some (stored.queue.entry index)
    obtain ⟨final, rankPeak, rankTrace, rankSpace, finalStack, finalOutput, finalPC, finalRunning,
      finalBase, finalSize, finalQueue, finalPacket, finalRanks⟩ := accepted_rank_execution resident
        accept graph.nodeCount (Controller.Horn.SourceSerialize.base clauses) rankDone classified packet suffix queue
        classPC classRunning saved complete distinct stored.fits queueCells rankCapacity (by omega)
        popAt reloadAt zeroAt rankSetupAt rankAt
    have actualLive : classified.liveWords ≤ classPeak := execution_final_live resident classTrace
    refine ⟨queue, final, classTicks + (2 * packet.length + 10 * graph.nodeCount + 13),
      max classPeak rankPeak, classTrace.append rankTrace, by omega, by omega, ordered, distinct,
      Or.inl ⟨acyclic, complete, finalPC, finalRunning, finalStack, finalOutput.trans classOutput,
        classified.heap.size, finalBase, finalSize, finalQueue, finalPacket, finalRanks⟩⟩
  · refine ⟨queue, classified, classTicks, classPeak, classTrace, by omega, by omega,
      ordered, distinct, Or.inr rejected⟩

end Controller.Cost.RawAdapterProgram
