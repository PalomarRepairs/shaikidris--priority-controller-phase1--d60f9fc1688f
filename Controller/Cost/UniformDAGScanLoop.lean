module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGScan

@[expose] public section

/-! Full execution of the fixed incidence loop over actual stored source cells.
The storage relation includes each fetched identifier and its value-table cell;
it preserves repeated identifiers and charges every incidence visit. -/
namespace Controller.Cost.UniformDAGScanLoop
open Controller.Cost.GateProgram Controller.Cost.UniformDAGScan

inductive Stored (heap : Array (Word width)) (valueBase : ℕ) : ℕ → List Bool → Prop
  | nil (cursor) : Stored heap valueBase cursor []
  | cons {cursor identifier value values}
      (cursorBound : cursor < heap.size)
      (valueBound : valueBase + identifier < heap.size)
      (valueFits : valueBase + identifier < 2 ^ width)
      (source : heap[cursor]'cursorBound = word width identifier)
      (cell : heap[valueBase + identifier]'valueBound = boolWord width value)
      (rest : Stored heap valueBase (cursor + 1) values) :
      Stored heap valueBase cursor (value :: values)

def accumulate (replacement : Bool) : Word width → List Bool → Word width
  | accumulator, [] => accumulator
  | accumulator, value :: rest =>
      accumulate replacement (if value then boolWord width replacement else accumulator) rest

/-- Each stored incidence contributes at most eighteen fetched instructions;
the final saved-zero exit contributes two. Heap and caller suffix are retained. -/
theorem execution (program : Program width 4) (heap : Array (Word width))
    (base valueBase cursor : ℕ) (values : List Bool)
    (temporary accumulator : Word width) (replacement : Bool)
    (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width)
    (cursorFits : cursor + values.length < 2 ^ width)
    (countFits : values.length < 2 ^ width)
    (cells : Stored heap valueBase cursor values)
    (block : BlockAt program base (code width base replacement)) :
    ∃ ticks peak, Execution program
      (state heap base temporary (word width valueBase) accumulator (word width cursor)
        (word width values.length :: suffix) output)
      (state heap (base + 18) (word width 0) (word width valueBase)
        (accumulate replacement accumulator values) (word width (cursor + values.length))
        suffix output) ticks peak ∧
      ticks ≤ 18 * values.length + 2 ∧
      peak ≤ 7 + heap.size + suffix.length + output.length := by
  induction cells generalizing temporary accumulator with
  | nil cursor =>
      refine ⟨2, 6 + heap.size + suffix.length + output.length, ?_, ?_, ?_⟩
      · simpa [accumulate] using zero_execution program heap base temporary
          (word width valueBase) accumulator (word width cursor) replacement suffix output programFits block
      · simp
      · omega
  | @cons cursor identifier value values cursorBound valueBound valueFits source cell rest ih =>
      obtain ⟨entryPeak, entryTrace, entryBound⟩ := entry_execution program heap base cursor
        valueBase identifier values.length temporary accumulator value replacement suffix output
        programFits (by simp only [List.length_cons] at cursorFits; omega) valueFits
        (by simpa only [List.length_cons] using countFits) cursorBound valueBound source cell block
      obtain ⟨tailTicks, tailPeak, tailTrace, tailBound, tailSpace⟩ := ih
        (word width 0) (if value then boolWord width replacement else accumulator)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at countFits; omega)
      refine ⟨(if value then 18 else 17) + tailTicks, max entryPeak tailPeak, ?_, ?_, ?_⟩
      · simpa only [accumulate, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using entryTrace.append tailTrace
      · cases value <;> simp only [List.length_cons, Bool.false_eq_true, ↓reduceIte] at * <;> omega
      · exact max_le entryBound tailSpace

end Controller.Cost.UniformDAGScanLoop
