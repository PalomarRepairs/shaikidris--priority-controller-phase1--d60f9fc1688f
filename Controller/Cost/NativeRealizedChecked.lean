module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeRealizedComplete
public import Controller.Native.SourceLiftEligible

@[expose] public section

/-! Decoding the actual emitted assignment words yields the checked original
source model. Retained output buffers are excluded by the declared variable
count, and natural source IDs outside that count decode to false. -/
namespace Controller.Cost.NativeRealizedChecked
open Controller.Cost.GateProgram Controller.Cost.NativeSourceExecution
open Controller.Native Controller.Native.SourceController

def decodeOutput (output : List (Word width)) (count source : Nat) : Bool :=
  if 0 < source ∧ source ≤ count then ((output[count - source]?).getD (word width 0)).val == 1 else false

theorem output_decodes (values : Fin count → Bool) (suffix : List (Word width))
    (boolFits : 1 < 2 ^ width) :
    decodeOutput ((NativeRootLoad.words width values).reverse ++ suffix) count = sourceFiniteExtension values := by
  funext source
  by_cases valid : 0 < source ∧ source ≤ count
  · rw [decodeOutput, ite_eq_left valid, sourceFiniteExtension, dite_eq_left valid]
    have position : count - source < (NativeRootLoad.words width values).reverse.length := by
      simp only [List.length_reverse, NativeRootLoad.words_length]
      omega
    rw [List.getElem?_append_left position, List.getElem?_eq_getElem position]
    simp only [Option.getD_some]
    have read : (NativeRootLoad.words width values).reverse[count - source]'position =
        boolWord width (values ⟨source - 1, by omega⟩) := by
      simp only [List.getElem_reverse, NativeRootLoad.words, List.length_ofFn, List.getElem_ofFn]
      congr 1
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [read, boolWord_val width boolFits]
    cases values ⟨source - 1, by omega⟩ <;> rfl
  · simp [decodeOutput, sourceFiniteExtension, valid]

set_option maxHeartbeats 3000000 in
theorem execution_checked (parameters : Parameters) (raw : parameters.layout = .raw)
    (K : Finset (Channel parameters.channels))
    (eligible : Admissible parameters.buses parameters.bridge.target K) (drive : parameters.drive = true)
    (differs : ∃ output, parameters.observations output (assignmentOfSet {parameters.bridge.target}) ≠
      parameters.observations output (assignmentOfSet K))
    (state : State (NativeRealizedComplete.wordWidth parameters) 4)
    (suffix : List (Word (NativeRealizedComplete.wordWidth parameters)))
    (position : state.pc = word (NativeRealizedComplete.wordWidth parameters) 0) (running : state.halted = false)
    (empty : state.heap = #[])
    (input : state.stack = NativeRootLoad.words (NativeRealizedComplete.wordWidth parameters) (assignmentOfSet K) ++ suffix) :
    ∃ final ticks peak, Execution (NativeRealizedComplete.program parameters) state final ticks peak ∧
      ticks ≤ 34 * (selectedSize parameters).total + 1 ∧
      peak ≤ state.liveWords + 2 * (selectedSize parameters).total ∧
      peak + programWords (NativeRealizedComplete.program parameters) ≤
        139 * (selectedSize parameters).total + 9 + suffix.length + state.output.length ∧
      Certificate.ModelCheck.check (formula parameters)
        (decodeOutput final.output (compile parameters).toState.count) = true ∧
      final.stack = suffix ∧ final.halted = true := by
  obtain ⟨final, ticks, peak, trace, time, memory, resident, _, stack, output, halted⟩ :=
    NativeRealizedComplete.execution parameters K state suffix position running empty input
  have capacity := NativeRealizedComplete.capacity parameters
  have boolFits : 1 < 2 ^ NativeRealizedComplete.wordWidth parameters := by omega
  refine ⟨final, ticks, peak, trace, time, memory, resident, ?_, stack, halted⟩
  rw [output, output_decodes _ _ boolFits]
  exact SourceLift.eligible_checked parameters raw K eligible drive differs

end Controller.Cost.NativeRealizedChecked
