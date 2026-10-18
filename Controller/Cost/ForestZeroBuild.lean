module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroEmit
public import Controller.Horn.SourceDirectory

@[expose] public section

/-! Literal-stream construction preserves every emitted pair while dictionary
first touches update only the reserved intervals. The physical suffix is tied
to the actual local-ID compiler, including repeated signed occurrences. Clause
directory construction precedes source allocation in the complete caller. -/
namespace Controller.Cost.ForestZeroBuild
open Controller.CNF Controller.Cost.GateProgram
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroRows Controller.Cost.ForestZeroEmit

/-- The two option-indexed cells are actual source words, not decoded values. -/
inductive RawStored (width : ℕ) : Clause ℕ → ℕ → Array (Word width) → Prop
  | nil (start : ℕ) (heap : Array (Word width)) (bound : start ≤ heap.size) :
      RawStored width [] start heap
  | cons (literal : Literal ℕ) (rest : Clause ℕ) (start : ℕ) (heap : Array (Word width))
      (label : heap[start]? = some (word width literal.1))
      (polarity : heap[start + 1]? = some (word width (if literal.2 then 1 else 0)))
      (tail : RawStored width rest (start + 2) heap) :
      RawStored width (literal :: rest) start heap

theorem RawStored.fits (stored : RawStored width row start heap) :
    start + 2 * row.length ≤ heap.size := by
  induction stored with
  | nil start heap bound => simpa using bound
  | cons literal rest start heap label polarity tail ih =>
    simp only [List.length_cons]; omega

theorem RawStored.entry (stored : RawStored width row start heap)
    (index : Fin row.length) :
    heap[start + 2 * index.val]? = some (word width (row.get index).1) ∧
      heap[start + 2 * index.val + 1]? =
        some (word width (if (row.get index).2 then 1 else 0)) := by
  induction stored with
  | nil start heap bound => exact Fin.elim0 index
  | cons literal rest start heap label polarity tail ih =>
    cases positionEq : index.val with
    | zero => simpa [List.get_eq_getElem, positionEq] using And.intro label polarity
    | succ slot =>
      have valid : slot < rest.length := by have := index.isLt; simp only [List.length_cons] at this; omega
      simpa [List.get_eq_getElem, positionEq, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih ⟨slot, valid⟩

/-- An already emitted suffix lies above both writable dictionary intervals. -/
theorem literal_suffix_frame (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (coherent : Coherent state) (literal : Literal (Fin ambient))
    (cut address : ℕ) (tableBelow : layout.tableBase + ambient ≤ cut)
    (inverseBelow : layout.inverseBase + ambient ≤ cut) (above : cut ≤ address)
    (old : address < heap.size) :
    (literalHeap heap layout state literal)[address]? = heap[address]? := by
  have touched : (touchedHeap heap layout state literal.1)[address]? = heap[address]? := by
    by_cases unseen : state.slots[literal.1.val] = 0
    · have capacity := fresh_capacity state coherent literal.1 unseen
      have coordinateBound := literal.1.isLt
      simp only [touchedHeap, ite_eq_left unseen]
      exact fresh_outside heap layout.tableBase layout.inverseBase state literal.1 address (by omega) (by omega)
    · simp only [touchedHeap, ite_eq_right unseen]
  simp only [literalHeap, Array.getElem?_push, Array.size_push, touchedHeap_size,
    ite_eq_right (show address ≠ heap.size + 1 by omega), ite_eq_right (show address ≠ heap.size by omega)]
  exact touched

/-- Every subsequent literal retains every earlier emitted pair cell. -/
theorem emit_suffix_frame (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (input scratch : ℕ) (references : List (Reference ambient)) (cut address : ℕ)
    (tableBelow : layout.tableBase + ambient ≤ cut)
    (inverseBelow : layout.inverseBase + ambient ≤ cut)
    (above : cut ≤ address) (old : address < heap.size) :
    (emitReferences heap layout state input scratch references).heap[address]? = heap[address]? := by
  induction references generalizing heap state input scratch with
  | nil => rfl
  | cons reference rest ih =>
    have first := literal_suffix_frame heap layout state represented.coherent
      (reference.coordinate, reference.positive) cut address tableBelow inverseBelow above old
    have tail := ih (literalHeap heap layout state (reference.coordinate, reference.positive))
      (literalLayout heap layout state (reference.coordinate, reference.positive))
      (touch state reference.coordinate).1
      (literal_represented heap layout state represented (reference.coordinate, reference.positive))
      (touch state reference.coordinate).2.1 (if reference.positive then 1 else 0)
      tableBelow inverseBelow (by rw [literalHeap_size]; omega)
    exact tail.trans first

/-- Both actual allocations store the returned local identifier and polarity. -/
theorem literal_pair_cells (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (literal : Literal (Fin ambient)) :
    (literalHeap heap layout state literal)[heap.size]? = some (word width (touch state literal.1).2.1) ∧
      (literalHeap heap layout state literal)[heap.size + 1]? =
        some (word width (if literal.2 then 1 else 0)) := by
  simp only [literalHeap, Array.getElem?_push, Array.size_push, touchedHeap_size,
    ite_eq_right (show heap.size ≠ heap.size + 1 by omega), ite_eq_left rfl, ite_true]
  exact ⟨trivial, trivial⟩

/-- The complete physical suffix equals the exact signed local-ID output of
compileClause. This statement derives source cells, not only an output length. -/
theorem emit_raw_stored (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (input scratch : ℕ) (references : List (Reference ambient))
    (cut : ℕ) (tableBelow : layout.tableBase + ambient ≤ cut)
    (inverseBelow : layout.inverseBase + ambient ≤ cut) (cutBelow : cut ≤ heap.size) :
    RawStored width
      (compileClause state (references.map (fun reference => (reference.coordinate, reference.positive)))).2.1
      heap.size (emitReferences heap layout state input scratch references).heap := by
  induction references generalizing heap state input scratch with
  | nil => exact RawStored.nil _ _ le_rfl
  | cons reference rest ih =>
    let literal : Literal (Fin ambient) := (reference.coordinate, reference.positive)
    let nextHeap := literalHeap heap layout state literal
    let nextLayout := literalLayout heap layout state literal
    let nextDictionary := (touch state reference.coordinate).1
    have nextRepresented := literal_represented heap layout state represented literal
    have tail := ih nextHeap nextLayout nextDictionary nextRepresented
      (touch state reference.coordinate).2.1 (if reference.positive then 1 else 0)
      tableBelow inverseBelow (by dsimp only [nextHeap]; rw [literalHeap_size]; omega)
    have pair := literal_pair_cells heap layout state literal
    have labelFrame := emit_suffix_frame nextHeap nextLayout nextDictionary nextRepresented
      (touch state reference.coordinate).2.1 (if reference.positive then 1 else 0) rest
      cut heap.size tableBelow inverseBelow cutBelow
      (by dsimp only [nextHeap]; rw [literalHeap_size]; omega)
    have polarityFrame := emit_suffix_frame nextHeap nextLayout nextDictionary nextRepresented
      (touch state reference.coordinate).2.1 (if reference.positive then 1 else 0) rest
      cut (heap.size + 1) tableBelow inverseBelow (by omega)
      (by dsimp only [nextHeap]; rw [literalHeap_size]; omega)
    simp only [List.map_cons, compileClause]
    apply RawStored.cons
    · exact labelFrame.trans pair.1
    · exact polarityFrame.trans pair.2
    · simpa only [nextHeap, nextLayout, nextDictionary, literalHeap_size, emitReferences, literal] using tail

/-- A finite typed source clause is obtained from exact emitted raw cells. -/
theorem raw_to_source (clause : Clause (Fin locals))
    (stored : RawStored width (clause.map (fun literal => (literal.1.val, literal.2))) start heap) :
    Controller.Horn.RowScan.SourceStored clause start heap := by
  refine ⟨?_, ?_⟩
  · simpa only [List.length_map] using stored.fits
  · intro index
    let rawIndex : Fin (clause.map (fun literal => (literal.1.val, literal.2))).length :=
      ⟨index.val, by simpa only [List.length_map] using index.isLt⟩
    have entries := stored.entry rawIndex
    have firstValid : start + 2 * index.val < heap.size := by have := stored.fits; have := index.isLt; simp only [List.length_map] at *; omega
    have secondValid : start + 2 * index.val + 1 < heap.size := by have := stored.fits; have := index.isLt; simp only [List.length_map] at *; omega
    refine ⟨by have := stored.fits; have := index.isLt; simp only [List.length_map] at *; omega, ?_, ?_⟩
    · have label := entries.1
      simp only [List.get_eq_getElem, List.getElem_map, rawIndex] at label
      rw [Array.getElem?_eq_getElem firstValid] at label
      exact Option.some.inj label
    · have polarity := entries.2
      simp only [List.get_eq_getElem, List.getElem_map, rawIndex] at polarity
      rw [Array.getElem?_eq_getElem secondValid] at polarity
      simpa only [Controller.Horn.MarkStorage.encode] using Option.some.inj polarity

/-- Concatenated clause traversal and row traversal allocate the same local IDs. -/
theorem compileClause_append (state : Dictionary ambient) (left right : Clause (Fin ambient)) :
    (compileClause state (left ++ right)).1 = (compileClause (compileClause state left).1 right).1 ∧
      (compileClause state (left ++ right)).2.1 =
        (compileClause state left).2.1 ++ (compileClause (compileClause state left).1 right).2.1 := by
  induction left generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons literal rest ih =>
    have tail := ih (touch state literal.1).1
    constructor
    · simpa only [List.cons_append, compileClause] using tail.1
    · simpa only [List.cons_append, compileClause] using
        congrArg (List.cons ((touch state literal.1).2.1, literal.2)) tail.2

theorem compileRows_flatten (state : Dictionary ambient) (rows : List (Clause (Fin ambient))) :
    (compileRows state rows).1 = (compileClause state rows.flatten).1 ∧
      (compileRows state rows).2.1.flatten = (compileClause state rows.flatten).2.1 := by
  induction rows generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons row rest ih =>
    have tail := ih (compileClause state row).1
    have append := compileClause_append state row rest.flatten
    constructor
    · simpa only [compileRows, List.flatten_cons, tail.1] using append.1.symm
    · simpa only [compileRows, List.flatten_cons, tail.2] using append.2.symm

end Controller.Cost.ForestZeroBuild
