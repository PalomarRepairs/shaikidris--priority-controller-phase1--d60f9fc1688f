module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeCircuitComplete
public import Controller.Cost.NativeSourceExecution

@[expose] public section

/-! Complete source lifting starts with physical root words and an empty heap,
emits every allocated native assignment word, and halts. All word-capacity
premises follow from the selected source formula size. -/
namespace Controller.Cost.NativeSourceComplete
open Controller.Cost.GateProgram Controller.Cost.NativeCircuitExecution
open Controller.Cost.NativeSourceExecution Controller.Native Controller.Native.SourceController

def wordWidth (parameters : Parameters) : Nat := Nat.log2 ((selectedSize parameters).total + 1) + 8

def code (parameters : Parameters) : List (Instruction (wordWidth parameters) 4) :=
  NativeCircuitComplete.code (wordWidth parameters) (sourceCircuit parameters)

def program (parameters : Parameters) : Program (wordWidth parameters) 4 := (code parameters).toArray

theorem capacity (parameters : Parameters) :
    128 * ((selectedSize parameters).total + 1) < 2 ^ wordWidth parameters := by
  let N := (selectedSize parameters).total
  have basic : N + 1 < 2 ^ (Nat.log2 (N + 1) + 1) :=
    (Nat.log2_lt (by omega : N + 1 ≠ 0)).mp (Nat.lt_succ_self _)
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 128)
  have identity : 128 * 2 ^ (Nat.log2 (N + 1) + 1) = 2 ^ wordWidth parameters := by
    simp only [wordWidth, N, Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  simpa only [identity] using scaled

theorem code_length_le (parameters : Parameters) :
    (code parameters).length ≤ 18 * (selectedSize parameters).total + 1 := by
  have body := NativeSourceExecution.code_length_le parameters (wordWidth parameters) 0
    (2 * SourceInitialIDs.rootCount parameters)
  have roots := (sourceCircuit parameters).roots_le
  simp only [code, NativeCircuitComplete.code_length]
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  omega

theorem physical (parameters : Parameters) : BlockAt (program parameters) 0 (code parameters) := by
  intro offset _
  change (code parameters).toArray[0 + offset]? = (code parameters)[offset]?
  simp

set_option maxHeartbeats 3000000 in
theorem execution (parameters : Parameters)
    (input : Physical.PrimaryInput parameters.channels parameters.buses)
    (state : State (wordWidth parameters) 4) (suffix : List (Word (wordWidth parameters)))
    (position : state.pc = word (wordWidth parameters) 0) (running : state.halted = false)
    (empty : state.heap = #[])
    (inputWords : state.stack = NativeRootLoad.words (wordWidth parameters) (sourcePhysicalRoots parameters input) ++ suffix) :
    ∃ final ticks peak, Execution (program parameters) state final ticks peak ∧
      ticks ≤ 18 * (selectedSize parameters).total + 1 ∧
      peak ≤ state.liveWords + 2 * (selectedSize parameters).total ∧
      peak + programWords (program parameters) ≤ state.liveWords + 74 * (selectedSize parameters).total + 4 ∧
      TableStored final.heap 0 (SourceLift.finite parameters input) ∧ final.stack = suffix ∧
      final.output = (NativeRootLoad.words (wordWidth parameters) (SourceLift.finite parameters input)).reverse ++ state.output ∧
      final.halted = true := by
  have codeBound := code_length_le parameters
  have wordRoom := capacity parameters
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  have gates := (sourceCircuit parameters).variable_count
  have codeRoom : (code parameters).length < 2 ^ wordWidth parameters := by omega
  have tableRoom : (compile parameters).toState.count < 2 ^ wordWidth parameters := by omega
  have boolFits : 1 < 2 ^ wordWidth parameters := by omega
  obtain ⟨final, ticks, trace, tickBound, table, stack, output, halted⟩ :=
    NativeCircuitComplete.execution (program parameters) state (sourceCircuit parameters)
      (sourcePhysicalRoots parameters input) suffix position running empty inputWords codeRoom boolFits tableRoom
      (physical parameters)
  refine ⟨final, ticks, state.liveWords + (sourceCircuit parameters).gateCount + (compile parameters).toState.count,
    trace, tickBound.trans codeBound, ?_, ?_, table, stack, output, halted⟩
  · omega
  · simp only [programWords, program, List.size_toArray]
    omega

end Controller.Cost.NativeSourceComplete
