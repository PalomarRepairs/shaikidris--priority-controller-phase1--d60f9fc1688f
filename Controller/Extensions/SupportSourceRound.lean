module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedGraphRound

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The shared topological interpreter with an arbitrary retained header.
The header can retain healthy reference values before the original DAG cache;
the channel and candidate tables remain separate linear allocations. -/
namespace Controller.Extensions.SupportSourceRound
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGRun
open Controller.Cost.UniformDAGSource
open Controller.Cost.RegisterWiden Controller.Cost.RawAdapterProgram Controller.Cost.RawTransferLoops

def kernel (width n : Nat) (header : Array (Word width)) (rows : List Row) (roots : List Nat) :
    Program width 4 :=
  (UniformDAGLoop.code width 0 1
    (UniformDAGTypedNode.layout header rows roots (fun _ : Fin n => false))).toArray

@[simp] theorem kernel_size (roots : List Nat) : (kernel width n header rows roots).size = 126 := by simp [kernel]

def code (width n : Nat) (header : Array (Word width)) (rows : List Row) (roots : List Nat)
    (entry : Nat) : Program width 8 :=
  (widenProgram (kernel width n header rows roots)).map (relocatedInstruction entry)

@[simp] theorem code_size (roots : List Nat) : (code width n header rows roots entry).size = 126 := by simp [code, widenProgram]

theorem kernel_header_independent (rows : List Row) (roots : List Nat) (left right : Array (Word width))
    (sameSize : left.size = right.size) : kernel width n left rows roots = kernel width n right rows roots := by
  simp only [kernel, UniformDAGTypedNode.layout, cacheHeap_size, channelHeap_size, sameSize]

private theorem state_ext (left right : State width registers)
    (reg : left.reg = right.reg) (heap : left.heap = right.heap)
    (stack : left.stack = right.stack) (output : left.output = right.output)
    (pc : left.pc = right.pc) (halted : left.halted = right.halted) : left = right := by
  cases left; cases right; simp_all

set_option maxHeartbeats 800000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (header : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched) (values : Assignment n)
    (entry : Nat) (heapStored : state.heap = channelHeap header rows roots values)
    (countStored : state.heap[1]? = some (word width graph.nodeCount))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 126 < 2 ^ width)
    (capacity : (cacheHeap width header rows roots).size + n + graph.nodeCount < 2 ^ width)
    (present : CodeAt resident entry (code width n header rows roots entry)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 43 * graph.countedSize + 6 ∧ peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = evaluationHeap header rows roots values (graph.evalTable values) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 126) ∧ final.halted = false ∧
      (∀ i : Fin 8, 4 ≤ i.val → final.reg i = state.reg i) := by
  let start : State width 4 := {
    reg := fun i => state.reg ⟨i.val, by omega⟩
    heap := state.heap, stack := state.stack, output := state.output
    pc := word width 0, halted := false }
  have countBound := (Array.getElem?_eq_some_iff.mp countStored).1
  have countCell := (Array.getElem?_eq_some_iff.mp countStored).2
  have startHeap : start.heap = evaluationHeap header rows roots values (graph.evalPrefix values 0 (by omega)) := by
    simp [start, heapStored, evaluationHeap, withValues]
  have block : BlockAt (kernel width n header rows roots) 0
      (UniformDAGLoop.code width 0 1 (UniformDAGTypedNode.layout header rows roots values)) := by
    have layoutEq : UniformDAGTypedNode.layout header rows roots values =
        UniformDAGTypedNode.layout header rows roots (fun _ : Fin n => false) := by
      simp [UniformDAGTypedNode.layout]
    rw [layoutEq]
    intro offset bound
    simp [kernel]
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, output, pc, active⟩ :=
    UniformDAGRun.execution (kernel width n header rows roots) start header graph rows roots matched heads values
      0 1 startHeap (by omega) countBound countCell rfl rfl (by omega) (by omega) block
  have widened := widen_execution _ _ _ _ _ trace state.reg
  have physical : ∀ i (valid : i < (widenProgram (kernel width n header rows roots)).size),
      resident[entry + i]? = some (relocatedInstruction entry
        ((widenProgram (kernel width n header rows roots))[i]'valid)) := by
    intro i valid
    calc
      resident[entry + i]? = (code width n header rows roots entry)[i]? :=
        present ⟨i, by simpa [code] using valid⟩
      _ = _ := by simp [code, valid]
  have relocated := relocated_execution resident _ entry physical
    (by simpa [widenProgram] using room) widened
  have startEq : relocatedState entry (widenState start state.reg) = state := by
    apply state_ext
    · funext i; fin_cases i <;> simp [relocatedState, widenState, start]
    · rfl
    · rfl
    · rfl
    · simpa [relocatedState, widenState, start, word] using position.symm
    · exact running.symm
  rw [startEq] at relocated
  refine ⟨relocatedState entry (widenState final state.reg), ticks, peak + 4,
    relocated, ?_, ?_, heap, stack, output, ?_, active, ?_⟩
  · have size := graph.countedSize_eq
    rw [UniformDAGRun.weights_sum] at time
    omega
  · have live : start.liveWords + 4 = state.liveWords := by simp [start, State.liveWords]; omega
    omega
  · simp only [relocatedState, widenState, pc, Nat.zero_add,
      show (word width 126).val = 126 from Nat.mod_eq_of_lt (by omega)]
    rw [Nat.add_comm]
  · intro i high; exact widenState_high final state.reg i high

end Controller.Extensions.SupportSourceRound
