module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.CompilerAppendTrace

@[expose] public section

/-! Source-list traces for mapping incidences and laying out gate-cell blocks.
The traces charge mapped entries and append copies. Template evaluation,
arithmetic representation and the RAM compiler remain separate. -/
namespace Controller.Cost.CompilerCellsTrace
open Controller.Cost.GateProgram Controller.Cost.CompilerAppendTrace

inductive MapTrace (f : α → β) : List α → List β → Nat → Prop
  | nil : MapTrace f [] [] 0
  | cons (a : α) (rest : List α) (result : List β) (count : Nat)
      (next : MapTrace f rest result count) : MapTrace f (a :: rest) (f a :: result) (count + 1)

theorem map_exists (f : α → β) (items : List α) : MapTrace f items (items.map f) items.length := by
  induction items with
  | nil => exact MapTrace.nil
  | cons a rest ih => exact MapTrace.cons a rest _ _ ih

theorem map_exact (trace : MapTrace f items result count) :
    result = items.map f ∧ count = items.length := by
  induction trace with
  | nil => simp
  | cons a rest result count next ih => simp [ih.1, ih.2]

/-- Every recursive cell step copies precisely its first append operand.
The cell function itself is not charged as an arbitrary constant-time oracle. -/
inductive CellsTrace (cell : Nat → Nat → Code width) (stride : Nat) :
    Nat → List Nat → Code width → Nat → Prop
  | nil (base : Nat) : CellsTrace cell stride base [] [] 0
  | cons (base address : Nat) (rest : List Nat) (tail result : Code width)
      (tailVisits copyVisits : Nat)
      (next : CellsTrace cell stride (base + stride) rest tail tailVisits)
      (copied : AppendTrace (cell base address) tail result copyVisits) :
      CellsTrace cell stride base (address :: rest) result (tailVisits + copyVisits + 1)

theorem cells_exists (cell : Nat → Nat → Code width) (stride : Nat)
    (fixed : ∀ base address, (cell base address).length = stride)
    (addresses : List Nat) (base : Nat) :
    CellsTrace cell stride base addresses (cells cell stride base addresses)
      ((stride + 1) * addresses.length) := by
  induction addresses generalizing base with
  | nil => simpa [cells] using CellsTrace.nil (cell := cell) (stride := stride) base
  | cons address rest ih =>
    have trace := CellsTrace.cons base address rest (cells cell stride (base + stride) rest)
      (cell base address ++ cells cell stride (base + stride) rest)
      ((stride + 1) * rest.length) stride (ih (base + stride))
      (by simpa only [fixed] using append_exists (cell base address) (cells cell stride (base + stride) rest))
    simpa [cells, Nat.mul_succ, Nat.add_assoc] using trace

theorem cells_exact {width : Nat} {cell : Nat → Nat → Code width}
    {stride base count : Nat} {addresses : List Nat} {result : Code width} (fixed : ∀ base address, (cell base address).length = stride)
    (trace : CellsTrace cell stride base addresses result count) :
    result = cells cell stride base addresses ∧ count = (stride + 1) * addresses.length := by
  induction trace with
  | nil base => simp [cells]
  | cons base address rest tail result tailVisits copyVisits next copied ih =>
    obtain ⟨value, copies⟩ := append_exact copied
    constructor
    · rw [value, ih.1]; rfl
    · rw [ih.2, copies, fixed]; simp [Nat.mul_succ, Nat.add_assoc]

theorem or_cells (width base : Nat) (addresses : List Nat) :
    CellsTrace (orCell width) 4 base addresses (cells (orCell width) 4 base addresses)
      (5 * addresses.length) := cells_exists (orCell width) 4 (by intros; rfl) addresses base

theorem guard_cells (width base : Nat) (addresses : List Nat) :
    CellsTrace (guardCell width) 4 base addresses (cells (guardCell width) 4 base addresses)
      (5 * addresses.length) := cells_exists (guardCell width) 4 (by intros; rfl) addresses base

theorem and_cells (width base : Nat) (addresses : List Nat) :
    CellsTrace (andCell width) 5 base addresses (cells (andCell width) 5 base addresses)
      (6 * addresses.length) := cells_exists (andCell width) 5 (by intros; rfl) addresses base

end Controller.Cost.CompilerCellsTrace
