module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeRealizedCore

@[expose] public section

/-! Complete native realization and lifting from a supplied channel set.
The same program handles every membership vector. Width, instruction counts
and resident memory follow from actual native variables, rows and literals. -/
namespace Controller.Cost.NativeRealizedComplete
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution
open Controller.Cost.NativeSourceExecution Controller.Native Controller.Native.SourceController

def wordWidth (parameters : Parameters) : Nat := Nat.log2 ((selectedSize parameters).total + 1) + 10

def program (parameters : Parameters) : Program (wordWidth parameters) 4 :=
  (NativeRealizedCore.code parameters (wordWidth parameters)).toArray

theorem capacity (parameters : Parameters) :
    512 * ((selectedSize parameters).total + 1) < 2 ^ wordWidth parameters := by
  let N := (selectedSize parameters).total
  have basic : N + 1 < 2 ^ (Nat.log2 (N + 1) + 1) :=
    (Nat.log2_lt (by omega : N + 1 ≠ 0)).mp (Nat.lt_succ_self _)
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 512)
  have identity : 512 * 2 ^ (Nat.log2 (N + 1) + 1) = 2 ^ wordWidth parameters := by
    simp only [wordWidth, N, Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  simpa only [identity] using scaled

theorem time_budget_le (parameters : Parameters) (width : Nat) :
    2 * parameters.channels + 16 * SourceInitialIDs.rootCount parameters +
      (NativeRealizedCore.circuitCode parameters width).length + 3 * (compile parameters).toState.count + 1 ≤
      34 * (selectedSize parameters).total + 1 := by
  have body := NativeSourceExecution.code_length_le parameters width parameters.channels
    (NativeRealizedCore.circuitEntry parameters width)
  change (NativeRealizedCore.circuitCode parameters width).length ≤ 13 * (selectedSize parameters).total at body
  have roots := (sourceCircuit parameters).roots_le
  have channelBound : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]
    omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  omega

theorem code_length_le (parameters : Parameters) (width : Nat) :
    (NativeRealizedCore.code parameters width).length ≤ 34 * (selectedSize parameters).total + 1 := by
  have roots := NativeRootBuilder.source_code_length_le parameters width (2 * parameters.channels)
  change (NativeRealizedCore.rootCode parameters width).length ≤ 16 * SourceInitialIDs.rootCount parameters at roots
  rw [NativeRealizedCore.code_length]
  have total := time_budget_le parameters width
  omega

theorem physical (parameters : Parameters) :
    BlockAt (program parameters) 0 (NativeRealizedCore.code parameters (wordWidth parameters)) := by
  intro offset _
  change (NativeRealizedCore.code parameters (wordWidth parameters)).toArray[0 + offset]? = _
  simp

set_option maxHeartbeats 3000000 in
theorem execution (parameters : Parameters) (K : Finset (Channel parameters.channels))
    (state : State (wordWidth parameters) 4) (suffix : List (Word (wordWidth parameters)))
    (position : state.pc = word (wordWidth parameters) 0) (running : state.halted = false)
    (empty : state.heap = #[])
    (input : state.stack = NativeRootLoad.words (wordWidth parameters) (assignmentOfSet K) ++ suffix) :
    ∃ final ticks peak, Execution (program parameters) state final ticks peak ∧
      ticks ≤ 34 * (selectedSize parameters).total + 1 ∧
      peak ≤ state.liveWords + 2 * (selectedSize parameters).total ∧
      peak + programWords (program parameters) ≤
        139 * (selectedSize parameters).total + 9 + suffix.length + state.output.length ∧
      TableStored final.heap parameters.channels
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K)) ∧
      final.stack = suffix ∧
      final.output = (NativeRootLoad.words (wordWidth parameters)
        (SourceLift.finite parameters (Physical.realizeBridge parameters.bridge parameters.positiveBuses K))).reverse ++ state.output ∧
      final.halted = true := by
  have wordRoom := capacity parameters
  have codeBound := code_length_le parameters (wordWidth parameters)
  have roots := (sourceCircuit parameters).roots_le
  have channelBound : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by
    simp only [SourceInitialIDs.rootCount]
    omega
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have codeRoom : (NativeRealizedCore.code parameters (wordWidth parameters)).length < 2 ^ wordWidth parameters := by omega
  have tableRoom : parameters.channels + (compile parameters).toState.count < 2 ^ wordWidth parameters := by omega
  have boolFits : 1 < 2 ^ wordWidth parameters := by omega
  obtain ⟨final, ticks, trace, bound, table, stack, output, halted⟩ :=
    NativeRealizedCore.execution parameters K (program parameters) state suffix position running empty input
      codeRoom boolFits tableRoom (physical parameters)
  have initialLive : state.liveWords = 5 + parameters.channels + suffix.length + state.output.length := by
    simp only [State.liveWords, empty, input, Array.size_empty, List.length_append, NativeRootLoad.words_length, List.length_nil]
    omega
  refine ⟨final, ticks, state.liveWords + 2 * (compile parameters).toState.count, trace,
    bound.trans (time_budget_le parameters (wordWidth parameters)), ?_, ?_, table, stack, output, halted⟩
  · omega
  · simp only [programWords, program, List.size_toArray]
    omega

end Controller.Cost.NativeRealizedComplete
