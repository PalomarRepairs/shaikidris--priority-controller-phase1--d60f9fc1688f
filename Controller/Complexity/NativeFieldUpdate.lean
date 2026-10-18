module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.DynamicFields
public import Controller.Complexity.NativeStore

@[expose] public section

/-! Exact physical field-commit endpoints under a reusable clean workspace.
This identifies every retained bank, rather than only the decoded field. -/
namespace Controller.Complexity.NativeFieldUpdate
open WordReader

theorem replacement (input : Port → List Bool) (slot : Fin 5) (packet : List Bool)
    (clean : ∀ port ∈ FieldSet.work, input port=[]) :
    FieldReplace.output input slot packet=Function.update input (some (FieldGet.field slot)) packet := by
  have workspace : WordSelect.output (Function.update input (some 20) []) [] []=input := by
    funext port
    have status := clean none (by simp [FieldSet.work])
    have source := clean (some 0) (by simp [FieldSet.work])
    have word := clean (some 1) (by simp [FieldSet.work])
    have scratch := clean (some 2) (by simp [FieldSet.work])
    have counter := clean (some 4) (by simp [FieldSet.work])
    have count := clean (some 10) (by simp [FieldSet.work])
    have buffer := clean (some 20) (by simp [FieldSet.work])
    by_cases hc : port=none <;> by_cases hs : port=some 0 <;> by_cases hw : port=some 1 <;>
      by_cases hk : port=some 2 <;> by_cases hi : port=some 4 <;> by_cases hn : port=some 10 <;>
      by_cases hb : port=some 20 <;> simp_all [WordSelect.output,WordSkip.reader_at]
  change Function.update (WordSelect.output (Function.update input (some 20) []) [] []) (some (FieldGet.field slot)) packet=_
  rw [workspace]

theorem rejection (input : Port → List Bool) (clean : ∀ port ∈ FieldSet.work, input port=[]) :
    WordSelect.output input [false] []=Function.update input none [false] := by
  funext port
  have status := clean none (by simp [FieldSet.work])
  have source := clean (some 0) (by simp [FieldSet.work])
  have word := clean (some 1) (by simp [FieldSet.work])
  have scratch := clean (some 2) (by simp [FieldSet.work])
  have counter := clean (some 4) (by simp [FieldSet.work])
  have count := clean (some 10) (by simp [FieldSet.work])
  by_cases hc : port=none <;> by_cases hs : port=some 0 <;> by_cases hw : port=some 1 <;>
    by_cases hk : port=some 2 <;> by_cases hi : port=some 4 <;> by_cases hn : port=some 10 <;>
      simp_all [WordSelect.output,WordSkip.reader_at]

end Controller.Complexity.NativeFieldUpdate
