module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGContinue
public import Controller.Cost.RawSharedHandoff

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A shared evaluation returns to its eight-register caller while preserving
all four caller registers. This permits counted evaluation rounds and explicit
heap reclamation between assignments. -/
namespace Controller.Cost.SharedEvaluationRound
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.RegisterWiden Controller.Cost.RawAdapterProgram
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored

def kernel (width n : Nat) (rows : List Row) (roots : List Nat) (values : Assignment n) :
    Program width 4 := (UniformDAGContinue.code width n rows roots values).toArray

@[simp] theorem kernel_size (width n : Nat) (rows : List Row) (roots : List Nat)
    (values : Assignment n) : (kernel width n rows roots values).size = 173 + 2 * n := by
  simp [kernel]

theorem assignment_independent (width n : Nat) (rows : List Row) (roots : List Nat)
    (first second : Assignment n) : kernel width n rows roots first = kernel width n rows roots second := by
  simp only [kernel, UniformDAGContinue.code, UniformDAGResources.code,
    UniformDAGTypedNode.layout, channelHeap_size]

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
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (suffix : List (Word width)) (entry : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : ∀ index (valid : index < (widenProgram (kernel width n rows roots values)).size),
      resident[entry + index]? = some (relocatedInstruction entry
        ((widenProgram (kernel width n rows roots values))[index]'valid)))
    (codeFits : entry + (widenProgram (kernel width n rows roots values)).size < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 3 = word width 0) (empty : state.heap = #[])
    (input : state.stack = (inputPacket n 0 rows roots).map (word width) ++
      List.ofFn (fun i => boolWord width (values i)) ++ suffix) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 97 * graph.countedSize + 36 ∧
      peak ≤ 8 * graph.countedSize + 18 + suffix.length + state.output.length ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ state.output ∧
      final.heap = evaluationHeap (packetHeaderHeap width n rows roots)
        rows roots values (graph.evalTable values) ∧
      final.pc = word width (entry + 173 + 2 * n) ∧ final.halted = false ∧
      (∀ index : Fin 8, 4 ≤ index.val → final.reg index = state.reg index) := by
  have block : BlockAt (kernel width n rows roots values) 0
      (UniformDAGContinue.code width n rows roots values) := by
    intro offset bound
    simp only [kernel, Nat.zero_add, List.getElem?_toArray]
  obtain ⟨final, ticks, peak, trace, time, space, stack, output, heap, pc, active⟩ :=
    UniformDAGContinue.execution_from_block (kernel width n rows roots values)
      graph rows roots matched heads rootMatches values capacity suffix state.output
      (state.reg 0) (state.reg 1) (state.reg 2) block
  have widened := widen_execution _ _ _ _ _ trace state.reg
  have relocated := relocated_execution resident _ entry physical codeFits widened
  have startEq : relocatedState entry
      (widenState ((ForestCounter.counterState (#[] : Array (Word width)) 0
        (state.reg 0) (state.reg 1) (state.reg 2)).frame
        ((inputPacket n 0 rows roots).map (word width) ++
          List.ofFn (fun i => boolWord width (values i)) ++ suffix) state.output) state.reg) = state := by
    apply state_ext
    · funext index
      fin_cases index <;> simp [relocatedState, widenState, ForestCounter.counterState,
        State.frame, zero]
    · exact empty.symm
    · exact input.symm
    · rfl
    · simpa [relocatedState, widenState, ForestCounter.counterState, State.frame,
        word] using position.symm
    · exact running.symm
  rw [startEq] at relocated
  refine ⟨relocatedState entry (widenState final state.reg), ticks, peak + 4,
    relocated, time, ?_, stack, output, heap, ?_, active, ?_⟩
  · omega
  · have bound : 173 + 2 * n < 2 ^ width := by
      have bound := codeFits
      simp only [widenProgram, Array.size_map, kernel_size] at bound
      omega
    simp only [relocatedState, widenState, pc, show (word width (173 + 2 * n)).val =
      173 + 2 * n from Nat.mod_eq_of_lt bound]
    congr 1
    omega
  · intro index high
    exact widenState_high final state.reg index high

end Controller.Cost.SharedEvaluationRound
