module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGRun
public import Controller.Cost.WordWidth

@[expose] public section

/-! A concrete cold-input interpreter program, including its resident code.
The source packet, declared-channel values and retained caller words are all
charged. Sparse cone extraction is a separate operation. -/
namespace Controller.Cost.UniformDAGResources
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRun

def code (width channels : ℕ) (rows : List Row) (roots : List ℕ)
    (values : Channel channels → Bool) : Code width :=
  ForestInputMetadata.fullCode width 0 ++
    (InputLoad.code channels ++ UniformDAGLoop.code width (33 + 2 * channels) 1
      (UniformDAGTypedNode.layout (packetHeaderHeap width channels rows roots) rows roots values))

def program (width channels : ℕ) (rows : List Row) (roots : List ℕ)
    (values : Channel channels → Bool) : Program width 4 :=
  (code width channels rows roots values).toArray

@[simp] theorem code_length (width channels : ℕ) (rows : List Row) (roots : List ℕ)
    (values : Channel channels → Bool) :
    (code width channels rows roots values).length = 159 + 2 * channels := by
  simp [code]; omega

@[simp] theorem program_size (width channels : ℕ) (rows : List Row) (roots : List ℕ)
    (values : Channel channels → Bool) :
    (program width channels rows roots values).size = 159 + 2 * channels := by
  simp [program]

theorem blocks (width n : ℕ) (rows : List Row) (roots : List ℕ)
    (values : Channel n → Bool) :
    BlockAt (program width n rows roots values) 0 (ForestInputMetadata.fullCode width 0) ∧
    BlockAt (program width n rows roots values) 33 (InputLoad.code n) ∧
    BlockAt (program width n rows roots values) (33 + 2 * n)
      (UniformDAGLoop.code width (33 + 2 * n) 1
        (UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots values)) := by
  have whole : BlockAt (program width n rows roots values) 0 (code width n rows roots values) := by
    intro offset bound
    simp [program, List.getElem?_toArray]
  have source := BlockAt.prefix _ 0 _ _ whole
  have rest := BlockAt.suffix _ 0 _ _ whole
  simp only [ForestInputMetadata.fullCode_length, Nat.zero_add] at rest
  have load := BlockAt.prefix _ 33 _ _ rest
  have loop := BlockAt.suffix _ 33 _ _ rest
  simp only [InputLoad.code_length] at loop
  exact ⟨source, load, loop⟩

def chosenWidth (graph : DAG n) : ℕ := Nat.log 2 (graph.countedSize + 1) + 9

theorem capacity (graph : DAG n) : 256 * (graph.countedSize + 1) < 2 ^ chosenWidth graph := by
  have basic := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (graph.countedSize + 1)
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 256)
  have identity : 256 * 2 ^ (Nat.log 2 (graph.countedSize + 1) + 1) =
      2 ^ chosenWidth graph := by
    simp only [chosenWidth, Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  simpa only [Nat.succ_eq_add_one, identity] using scaled

/-- The concrete program starts with an empty heap and the complete source
packet. No instruction-block or preinitialized-cache premise is supplied. -/
theorem execution (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Channel n → Bool)
    (suffix output : List (Word (chosenWidth graph)))
    (address loaded temporary : Word (chosenWidth graph)) :
    ∃ final ticks peak,
      Execution (program (chosenWidth graph) n rows roots values)
        ((ForestCounter.counterState (#[] : Array (Word (chosenWidth graph))) 0
          address loaded temporary).frame
          ((inputPacket n 0 rows roots).map (word (chosenWidth graph)) ++
            List.ofFn (fun i => boolWord (chosenWidth graph) (values i)) ++ suffix) output)
        final ticks peak ∧
      ticks ≤ 85 * graph.countedSize + 33 ∧
      peak ≤ 7 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.heap = evaluationHeap (packetHeaderHeap (chosenWidth graph) n rows roots)
        rows roots values (graph.evalTable values) ∧
      final.stack = suffix ∧ final.output = output ∧
      final.pc = word (chosenWidth graph) (159 + 2 * n) ∧ final.halted = false := by
  have cap := capacity graph
  have size := graph.countedSize_eq
  have room : (cacheHeap (chosenWidth graph) (packetHeaderHeap (chosenWidth graph) n rows roots)
      rows roots).size + n + graph.nodeCount ≤ 2 ^ chosenWidth graph := by
    simp only [cacheHeap_size, packetHeaderHeap_size]
    obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
    have rootsLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
    rw [matched.length_eq, children, guards, rootsLength]
    omega
  obtain ⟨source, load, loop⟩ := blocks (width := chosenWidth graph) (rows := rows)
    (roots := roots) (values := values)
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, out, pc, running⟩ :=
    cold_execution (program (chosenWidth graph) n rows roots values) graph rows roots matched heads
      rootMatches values suffix output address loaded temporary 0 (by omega) room source load
      (by simpa only [Nat.zero_add, Nat.add_assoc] using loop)
  refine ⟨final, ticks, peak, trace, ?_, ?_, heap, stack, out, ?_, running⟩
  · omega
  · omega
  · simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pc

theorem resident_words_le (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (values : Channel n → Bool) (suffix output : List (Word width)) :
    programWords (program width n rows roots values) +
      (7 * graph.countedSize + 14 + suffix.length + output.length) ≤
      15 * graph.countedSize + 650 + suffix.length + output.length := by
  have size := graph.countedSize_eq
  simp only [programWords, program_size]
  omega

theorem representable (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (values : Channel n → Bool) (suffix output : List (Word (chosenWidth graph)))
    (address loaded temporary : Word (chosenWidth graph)) :
    Representable (program (chosenWidth graph) n rows roots values)
      ((ForestCounter.counterState (#[] : Array (Word (chosenWidth graph))) 0
        address loaded temporary).frame
        ((inputPacket n 0 rows roots).map (word (chosenWidth graph)) ++
          List.ofFn (fun i => boolWord (chosenWidth graph) (values i)) ++ suffix) output) := by
  have cap := capacity graph
  have size := graph.countedSize_eq
  refine ⟨by omega, ?_, ?_⟩
  · rw [program_size]; omega
  · simp [ForestCounter.counterState, State.frame]

theorem resident_bits_le (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (values : Channel n → Bool) (suffix output : List (Word (chosenWidth graph))) :
    chosenWidth graph * (programWords (program (chosenWidth graph) n rows roots values) +
      (7 * graph.countedSize + 14 + suffix.length + output.length)) ≤
    (Nat.log 2 (graph.countedSize + 1) + 9) *
      (15 * graph.countedSize + 650 + suffix.length + output.length) := by
  exact Nat.mul_le_mul_left (chosenWidth graph)
    (resident_words_le graph rows roots values suffix output)

end Controller.Cost.UniformDAGResources
