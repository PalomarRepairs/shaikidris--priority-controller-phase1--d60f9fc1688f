module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedEvaluationRound
public import Controller.Cost.RawSharedOrdered

@[expose] public section

/-! The shared evaluator's heap is reclaimed by a fixed resident loop before
another assignment starts. Stack data, outputs, and caller counter registers
are preserved by the actual fetched instructions. -/
namespace Controller.Cost.SharedEvaluationReclaim
open Controller.Cost.RawTransferLoops

theorem constant_execution (resident : Program width 8)
    (entry value : Nat) (destination : Fin 8) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 1 < 2 ^ width)
    (physical : resident[entry]? = some (.constant destination (word width value))) :
    ∃ final, Execution resident state final 1 state.liveWords ∧
      final.pc = word width (entry + 1) ∧ final.reg destination = word width value ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, index ≠ destination → final.reg index = state.reg index) := by
  let final := state.advance.put destination (word width value)
  have transition : programStep resident state = some final := by
    rw [RawTransferLoops.fetched resident state entry _ position (by omega) physical]
    simp [step, running, final]
  have live : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, running, ?_⟩
  · simpa only [live, Nat.zero_add, Nat.max_self] using Execution.cons transition (Execution.refl final)
  · simpa only [final, State.put] using RawTransferLoops.advance_position state position (by omega)
  · simp [final, State.put]
  · intro index different; simp [final, State.put, State.advance, different]


def code (width entry done count : Nat) : Program width 8 :=
  #[.constant 0 (word width count), .constant 6 (word width 0),
    .constant 7 (word width (2 ^ width - 1))] ++ countedReleaseCode width (entry + 3) done

@[simp] theorem code_size (width entry done count : Nat) :
    (code width entry done count).size = 7 := by simp [code, countedReleaseCode]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (entry done count : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 7 < 2 ^ width)
    (heapCount : state.heap.size = count) (heapFits : count < 2 ^ width)
    (physical : CodeAt resident entry (code width entry done count)) :
    ∃ final, Execution resident state final (4 * count + 4) state.liveWords ∧
      final.heap = #[] ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 6 → index ≠ 7 → final.reg index = state.reg index) := by
  have all := physical
  unfold code at all
  have setup := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  have loop : CodeAt resident (entry + 3) (countedReleaseCode width (entry + 3) done) := by
    simpa only [List.size_toArray, List.length_cons, List.length_nil] using tail
  obtain ⟨counted, t₀, pc₀, value₀, heap₀, stack₀, out₀, run₀, frame₀⟩ :=
    constant_execution resident entry count 0 state position running (by omega)
      (by simpa using setup ⟨0, by change 0 < 3; decide⟩)
  obtain ⟨zeroed, t₁, pc₁, value₁, heap₁, stack₁, out₁, run₁, frame₁⟩ :=
    constant_execution resident (entry + 1) 0 6 counted pc₀ run₀ (by omega)
      (by simpa using setup ⟨1, by change 1 < 3; decide⟩)
  obtain ⟨ready, t₂, pc₂, value₂, heap₂, stack₂, out₂, run₂, frame₂⟩ :=
    constant_execution resident (entry + 2) (2 ^ width - 1) 7 zeroed
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc₁) run₁ (by omega)
      (by simpa using setup ⟨2, by change 2 < 3; decide⟩)
  obtain ⟨final, peak, release, bound, empty, stack, output, pc, active, zero, frame⟩ :=
    counted_release_execution resident (entry + 3) done count ready
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc₂) run₂ (by omega)
      (by rw [heap₂, heap₁, heap₀]; exact heapCount) heapFits
      (by rw [frame₂ 0 (by decide), frame₁ 0 (by decide)]; exact value₀)
      value₂ (by rw [frame₂ 6 (by decide)]; exact value₁) loop
  have countedLive : counted.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₀, stack₀, out₀]
  have zeroedLive : zeroed.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₁, stack₁, out₁, heap₀, stack₀, out₀]
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₂, stack₂, out₂, heap₁, stack₁, out₁, heap₀, stack₀, out₀]
  have joined := t₀.append (t₁.append (t₂.append release))
  have ticksEq : 1 + (1 + (1 + (4 * count + 1))) = 4 * count + 4 := by omega
  have peakEq : max state.liveWords (max counted.liveWords (max zeroed.liveWords peak)) =
      state.liveWords := by simp only [countedLive, zeroedLive, readyLive] at bound ⊢; omega
  rw [ticksEq, peakEq] at joined
  refine ⟨final, joined, empty, stack.trans (stack₂.trans (stack₁.trans stack₀)),
    output.trans (out₂.trans (out₁.trans out₀)), pc, active, zero, ?_, ?_, ?_⟩
  · rw [frame 6 (by decide), frame₂ 6 (by decide)]; exact value₁
  · rw [frame 7 (by decide)]; exact value₂
  · intro index a b c
    rw [frame index a, frame₂ index c, frame₁ index b, frame₀ index a]


open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRun
open Controller.Cost.RegisterWiden Controller.Cost.RawAdapterProgram

def heapWords (channels nodes children guards roots : Nat) : Nat :=
  5 + 7 * nodes + children + guards + roots + channels

theorem evaluated_heap_size (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (values : Assignment n) :
    (evaluationHeap (packetHeaderHeap width n rows roots) rows roots values (graph.evalTable values)).size =
      heapWords n graph.nodeCount graph.childIncidences graph.guardIncidences graph.roots.length := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  simp only [evaluationHeap_size, cacheHeap_size, packetHeaderHeap_size, heapWords,
    matched.length_eq, children, guards, rootCount]
  omega

def roundCode (width n : Nat) (rows : List Row) (roots : List Nat) (values : Assignment n)
    (entry done : Nat) : Program width 8 :=
  (widenProgram (SharedEvaluationRound.kernel width n rows roots values)).map
    (relocatedInstruction entry) ++
  code width (entry + 173 + 2 * n) done
    (heapWords n rows.length (rowChildren rows).length (rowGuards rows).length roots.length)

@[simp] theorem roundCode_size (width n : Nat) (rows : List Row) (roots : List Nat)
    (values : Assignment n) (entry done : Nat) :
    (roundCode width n rows roots values entry done).size = 180 + 2 * n := by
  simp only [roundCode, Array.size_append, Array.size_map, widenProgram,
    SharedEvaluationRound.kernel_size, code_size]
  omega

set_option maxHeartbeats 2000000 in
theorem round_execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (roundCode width n rows roots values entry done))
    (codeFits : entry + (roundCode width n rows roots values entry done).size < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 3 = word width 0) (empty : state.heap = #[])
    (input : state.stack = (inputPacket n 0 rows roots).map (word width) ++
      List.ofFn (fun i => boolWord width (values i)) ++ suffix) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 125 * graph.countedSize + 60 ∧
      peak ≤ 8 * graph.countedSize + 18 + suffix.length + state.output.length ∧
      final.heap = #[] ∧ final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) ∧
      (∀ index : Fin 8, index = 4 ∨ index = 5 → final.reg index = state.reg index) := by
  let part := widenProgram (SharedEvaluationRound.kernel width n rows roots values)
  have all := physical
  unfold roundCode at all
  have kernelAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have cleanupAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  have kernelPhysical : ∀ index (valid : index < part.size),
      resident[entry + index]? = some (relocatedInstruction entry (part[index]'valid)) := by
    intro index valid
    have selected := kernelAt ⟨index, by simpa only [Array.size_map] using valid⟩
    rw [Array.getElem?_map, Array.getElem?_eq_getElem valid, Option.map_some] at selected
    exact selected
  have partSize : part.size = 173 + 2 * n := by simp only [part, widenProgram,
    Array.size_map, SharedEvaluationRound.kernel_size]
  have coreFits : entry + part.size < 2 ^ width := by
    rw [roundCode_size] at codeFits
    omega
  obtain ⟨evaluated, ticks, peak, trace, time, space, stack, output, heap, pc, active, frame⟩ :=
    SharedEvaluationRound.execution resident state graph rows roots matched heads rootMatches values
      suffix entry capacity kernelPhysical coreFits position running zero empty input
  have counts := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have heapCount := evaluated_heap_size (width := width) graph rows roots matched rootMatches values
  rw [←heap] at heapCount
  have heapBound : evaluated.heap.size ≤ 7 * graph.countedSize + 5 := by
    rw [heapCount]
    unfold heapWords
    omega
  have cleanup : CodeAt resident (entry + 173 + 2 * n)
      (code width (entry + 173 + 2 * n) done evaluated.heap.size) := by
    simpa only [Array.size_map, partSize, show
      (widenProgram (SharedEvaluationRound.kernel width n rows roots values)).size = 173 + 2 * n from partSize,
      matched.length_eq, children, guards, rootCount, heapCount, Nat.add_assoc] using cleanupAt
  obtain ⟨final, release, finalHeap, finalStack, finalOut, finalPC, finalRun, zero₀, zero₆, mask, releaseFrame⟩ :=
    execution resident evaluated (entry + 173 + 2 * n) done evaluated.heap.size pc active
      (by rw [roundCode_size] at codeFits; omega) rfl (by omega) cleanup
  have outputCount : evaluated.output.length = graph.roots.length + state.output.length := by
    rw [output]
    simp only [List.length_append, List.length_reverse, List.length_map, DAG.outputValues]
  have evaluatedLive : evaluated.liveWords ≤ 8 * graph.countedSize + 14 +
      suffix.length + state.output.length := by
    simp only [State.liveWords, stack, outputCount]
    omega
  refine ⟨final, _, _, trace.append release, ?_, ?_, finalHeap,
    finalStack.trans stack, finalOut.trans output, finalPC, finalRun, zero₀, zero₆, mask, ?_⟩
  · omega
  · exact max_le space (le_trans evaluatedLive (by omega))
  · intro index which
    rcases which with rfl | rfl
    · rw [releaseFrame 4 (by decide) (by decide) (by decide)]
      exact frame 4 (by decide)
    · rw [releaseFrame 5 (by decide) (by decide) (by decide)]
      exact frame 5 (by decide)


theorem round_assignment_independent (width n : Nat) (rows : List Row) (roots : List Nat)
    (first second : Assignment n) (entry done : Nat) :
    roundCode width n rows roots first entry done = roundCode width n rows roots second entry done := by
  simp only [roundCode, SharedEvaluationRound.assignment_independent width n rows roots first second]

end Controller.Cost.SharedEvaluationReclaim
