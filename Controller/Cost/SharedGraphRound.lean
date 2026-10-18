module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedGraphReclaim

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Shared evaluation on the caller's eight-register machine. -/
namespace Controller.Cost.SharedGraphRound
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.RegisterWiden Controller.Cost.RawAdapterProgram
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored

def kernel (width n : Nat) (rows : List Row) (roots : List Nat) : Program width 4 :=
  (SharedGraphEvaluation.code width n 0 rows roots).toArray

@[simp] theorem kernel_size (width n : Nat) (rows : List Row) (roots : List Nat) :
    (kernel width n rows roots).size = 126 := by simp [kernel]

private theorem state_ext (left right : State width registers)
    (reg : left.reg = right.reg) (heap : left.heap = right.heap)
    (stack : left.stack = right.stack) (output : left.output = right.output)
    (pc : left.pc = right.pc) (halted : left.halted = right.halted) : left = right := by
  cases left
  cases right
  simp_all

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (entry : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : ∀ index (valid : index < (widenProgram (kernel width n rows roots)).size),
      resident[entry + index]? = some (relocatedInstruction entry
        ((widenProgram (kernel width n rows roots))[index]'valid)))
    (codeFits : entry + 126 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 43 * graph.countedSize + 6 ∧ peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = evaluationHeap (packetHeaderHeap width n rows roots) rows roots values (graph.evalTable values) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 126) ∧ final.halted = false ∧
      (∀ index : Fin 8, 4 ≤ index.val → final.reg index = state.reg index) := by
  let start : State width 4 := {
    reg := fun index => state.reg ⟨index.val, by omega⟩
    heap := state.heap, stack := state.stack, output := state.output
    pc := word width 0, halted := false }
  have block : BlockAt (kernel width n rows roots) 0
      (SharedGraphEvaluation.code width n 0 rows roots) := by
    intro offset bound
    simp [kernel]
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, output, pc, active⟩ :=
    SharedGraphEvaluation.execution (kernel width n rows roots) start graph rows roots
      matched heads rootMatches values 0 heapStored rfl rfl (by omega) capacity block
  have widened := widen_execution _ _ _ _ _ trace state.reg
  have relocated := relocated_execution resident _ entry physical
    (by simpa [widenProgram] using codeFits) widened
  have startEq : relocatedState entry (widenState start state.reg) = state := by
    apply state_ext
    · funext index
      fin_cases index <;> simp [relocatedState, widenState, start]
    · rfl
    · rfl
    · rfl
    · simpa [relocatedState, widenState, start, word] using position.symm
    · exact running.symm
  rw [startEq] at relocated
  refine ⟨relocatedState entry (widenState final state.reg), ticks, peak + 4,
    relocated, time, ?_, heap, stack, output, ?_, active, ?_⟩
  · have live : start.liveWords + 4 = state.liveWords := by simp [start, State.liveWords]; omega
    omega
  · simp only [relocatedState, widenState, pc, Nat.zero_add,
      show (word width 126).val = 126 from Nat.mod_eq_of_lt (by omega)]
    rw [Nat.add_comm]
  · intro index high
    exact widenState_high final state.reg index high


theorem live_bound (state : State width 8) (graph : DAG n) (rows : List Row)
    (roots : List Nat) (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (values : Assignment n)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values) :
    state.liveWords + graph.nodeCount + 4 ≤
      7 * graph.countedSize + 18 + state.stack.length + state.output.length := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  simp only [State.liveWords, heapStored, channelHeap_size,
    cacheHeap_size, packetHeaderHeap_size,
    matched.length_eq, children, guards, rootCount]
  omega

end Controller.Cost.SharedGraphRound
