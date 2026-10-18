module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroQuery

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The directory pass allocates all row boundaries before any literal pair.
A running cursor advances once per row. Count fields are generated from the
executed clause-count pass; their generation/loading remains separately charged.
The fetched directory phase itself uses exactly five steps and two heap words
per row, preserving the protected source and dictionary prefix. -/
namespace Controller.Cost.ForestZeroDirectory
open Controller.CNF Controller.Cost.GateProgram
open Controller.Cost.ForestZeroRows Controller.Cost.ForestZeroQuery Controller.Cost.ForestZeroTouch

structure Result (width : ℕ) where
  heap : Array (Word width)
  cursor : ℕ
  count : ℕ

def build (heap : Array (Word width)) (cursor count : ℕ) : List (Clause α) → Result width
  | [] => ⟨heap, cursor, count⟩
  | row :: rest =>
      build ((heap.push (word width cursor)).push (word width (cursor + 2 * countClause row)))
        (cursor + 2 * countClause row) (2 * countClause row) rest

def code (width : ℕ) : List (Clause α) → Code width
  | [] => []
  | row :: rest => [.constant 2 (word width (countClause row))] ++ boundaryCode width ++ code width rest

@[simp] theorem code_length (rows : List (Clause α)) : (code width rows).length = 5 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [code, List.length_append, List.length_cons, List.length_nil, boundaryCode_length, ih]; omega

theorem build_size (heap : Array (Word width)) (cursor count : ℕ) (rows : List (Clause α)) :
    (build heap cursor count rows).heap.size = heap.size + 2 * rows.length := by
  induction rows generalizing heap cursor count with
  | nil => rfl
  | cons row rest ih =>
    have same := ih ((heap.push (word width cursor)).push (word width (cursor + 2 * countClause row)))
      (cursor + 2 * countClause row) (2 * countClause row)
    simp only [Array.size_push] at same
    simp only [build, List.length_cons]
    omega

theorem build_cursor (heap : Array (Word width)) (cursor count : ℕ) (rows : List (Clause α)) :
    (build heap cursor count rows).cursor = cursor + 2 * (rows.map countClause).sum := by
  induction rows generalizing heap cursor count with
  | nil => simp [build]
  | cons row rest ih =>
    simpa only [build, List.map_cons, List.sum_cons, Nat.mul_add, Nat.add_assoc] using
      (ih ((heap.push (word width cursor)).push (word width (cursor + 2 * countClause row)))
        (cursor + 2 * countClause row) (2 * countClause row))

theorem build_prefix (heap : Array (Word width)) (cursor count : ℕ) (rows : List (Clause α))
    (address : ℕ) (valid : address < heap.size) : (build heap cursor count rows).heap[address]? = heap[address]? := by
  induction rows generalizing heap cursor count with
  | nil => rfl
  | cons row rest ih =>
    have tail := ih ((heap.push (word width cursor)).push (word width (cursor + 2 * countClause row)))
      (cursor + 2 * countClause row) (2 * countClause row) (by simp only [Array.size_push]; omega)
    simpa only [build, Array.getElem?_push, Array.size_push,
      ite_eq_right (show address ≠ heap.size + 1 by omega), ite_eq_right (show address ≠ heap.size by omega)] using tail

/-- Generated directory fields equal the concrete sequence of allocations. -/
theorem build_heap (heap : Array (Word width)) (cursor count : ℕ) (rows : List (Clause α)) :
    (build heap cursor count rows).heap =
      Controller.Cost.ForestCursorMaterialize.allocatedHeap width heap (directoryValues cursor rows) := by
  induction rows generalizing heap cursor count with
  | nil => simp [build, directoryValues, Controller.Cost.ForestCursorMaterialize.allocatedHeap]
  | cons row rest ih =>
    apply Array.toList_inj.mp
    have same := congrArg Array.toList
      (ih ((heap.push (word width cursor)).push (word width (cursor + 2 * countClause row)))
        (cursor + 2 * countClause row) (2 * countClause row))
    simpa only [build, directoryValues, Controller.Cost.ForestCursorMaterialize.allocatedHeap,
      Array.toList_append, Array.toList_push, List.toList_toArray, List.map_cons,
      List.append_assoc, List.cons_append, List.nil_append] using same

private theorem constant_execution (program : Program width 4) (heap : Array (Word width))
    (base cursor table count scratch value : ℕ) (stack output : List (Word width))
    (fits : base + 1 < 2 ^ width)
    (entry : program[base]? = some (.constant 2 (word width value))) :
    Execution program (atState heap base cursor table count scratch stack output)
      (atState heap (base + 1) cursor table value scratch stack output)
      1 (5 + heap.size + stack.length + output.length) := by
  let first := atState heap base cursor table count scratch stack output
  let last := atState heap (base + 1) cursor table value scratch stack output
  have transition : programStep program first = some last := by
    unfold programStep
    rw [show first.pc = word width base from rfl,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega), entry]
    change some (first.advance.put 2 (word width value)) = some last
    apply congrArg some
    unfold first last atState State.advance State.put
    simp only [show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
    congr 1
    funext register
    fin_cases register <;> rfl
  convert Execution.cons transition (Execution.refl last) using 1 <;>
    simp only [first, last, atState_liveWords, Nat.max_self]

/-- The complete actual directory pass uses a fixed boundary block per row.
Every source pointer is formed from the previous pointer and row count. -/
theorem execution (program : Program width 4) (heap : Array (Word width))
    (base cursor table count scratch : ℕ) (stack output : List (Word width))
    (rows : List (Clause α)) (room : heap.size + 2 * rows.length ≤ 2 ^ width)
    (pointersFit : cursor + 2 * (rows.map countClause).sum < 2 ^ width)
    (programFits : base + (code width rows).length < 2 ^ width)
    (block : BlockAt program base (code width rows)) :
    let result := build heap cursor count rows
    Execution program (atState heap base cursor table count scratch stack output)
      (atState result.heap (base + (code width rows).length) result.cursor table result.count scratch stack output)
      (5 * rows.length) (5 + heap.size + 2 * rows.length + stack.length + output.length) := by
  induction rows generalizing heap base cursor count with
  | nil => simpa only [build, code, List.length_nil, Nat.mul_zero, Nat.add_zero, atState_liveWords] using
      Execution.refl (p := program) (atState heap base cursor table count scratch stack output)
  | cons row rest ih =>
    have whole : BlockAt program base
        ([.constant 2 (word width (countClause row))] ++ (boundaryCode width ++ code width rest)) := by
      simpa only [code, List.append_assoc] using block
    have constantBlock := BlockAt.prefix program base _ _ whole
    have suffix := BlockAt.suffix program base _ _ whole
    have boundaryBlock : BlockAt program (base + 1) (boundaryCode width) := by
      simpa only [List.length_cons, List.length_nil, Nat.zero_add] using BlockAt.prefix program _ _ _ suffix
    have tailBlock : BlockAt program (base + 5) (code width rest) := by
      simpa only [List.length_cons, List.length_nil, boundaryCode_length, Nat.zero_add, Nat.add_assoc] using
        BlockAt.suffix program _ _ _ suffix
    have countStep := constant_execution program heap base cursor table count scratch (countClause row)
      stack output (by simp only [code_length, List.length_cons] at programFits; omega)
      (by simpa using constantBlock 0 (by simp))
    have boundary := boundary_execution program heap (base + 1) cursor table (countClause row) scratch
      stack output (by simp only [List.length_cons] at room; omega)
      (by simp only [List.map_cons, List.sum_cons, Nat.mul_add] at pointersFit; omega)
      (by simp only [code_length, List.length_cons] at programFits; omega) boundaryBlock
    have first := countStep.append boundary
    have tail := ih ((heap.push (word width cursor)).push (word width (cursor + 2 * countClause row)))
      (base + 5) (cursor + 2 * countClause row) (2 * countClause row)
      (by simp only [Array.size_push, List.length_cons] at room ⊢; omega)
      (by simpa only [List.map_cons, List.sum_cons, Nat.mul_add, Nat.add_assoc] using pointersFit)
      (by simp only [code_length, List.length_cons] at programFits ⊢; omega) tailBlock
    have joined := first.append tail
    simp only [List.length_cons] at room
    simp only [List.map_cons, List.sum_cons, Nat.mul_add] at pointersFit
    simp only [code_length, List.length_cons] at programFits
    have initialPeak : 5 + heap.size + stack.length + output.length ≤
        7 + heap.size + stack.length + output.length := by omega
    have boundaryPeak : 7 + heap.size + stack.length + output.length ≤
        5 + heap.size + 1 + 1 + 2 * rest.length + stack.length + output.length := by omega
    convert joined using 1 <;>
      simp only [build, code_length, List.length_cons, Array.size_push,
        atState_liveWords, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add, Nat.mul_one,
        Nat.max_eq_right initialPeak, Nat.max_eq_right boundaryPeak] <;>
      omega

end Controller.Cost.ForestZeroDirectory
