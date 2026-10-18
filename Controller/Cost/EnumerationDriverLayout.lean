module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverCode

@[expose] public section

/-! Physical extraction of all seventeen blocks of the immutable driver. -/
namespace Controller.Cost.EnumerationDriverLayout
open Controller.Cost.GateProgram Controller.Cost.EnumerationDriverCode
open Controller.Decoder Controller.Native

def offsets (entry : Nat) : List Nat → List Nat
  | [] => []
  | size :: rest => entry :: offsets (entry + size) rest

@[simp] theorem offsets_length (sizes : List Nat) (entry : Nat) :
    (offsets entry sizes).length = sizes.length := by
  induction sizes generalizing entry with
  | nil => rfl
  | cons size rest ih => simp [offsets, ih]

def entries (l : Labels) : List Nat :=
  [l.start, l.call, l.restore, l.dispatch, l.seekPost, l.seekFail, l.initialPost,
    l.completePost, l.completeRepair, l.descend, l.forcedDescend, l.seek,
    l.seekForced, l.seekTry, l.emit, l.halt, l.oracle]

theorem entries_eq (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) :
    entries (labels parameters graph width entry) =
      offsets entry ((chunks parameters graph width entry rows roots).map List.length) := by
  rw [chunks_lengths]
  simp [entries, labels, offsets, Nat.add_assoc]
  repeat' constructor <;> omega

private theorem left_at (program : Program width 8) (entry : Nat)
    (first rest : List (Instruction width 8)) (present : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program entry first := by
  intro offset below
  have whole := present offset (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left below] at whole
  exact whole

private theorem right_at (program : Program width 8) (entry : Nat)
    (first rest : List (Instruction width 8)) (present : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program (entry + first.length) rest := by
  intro offset below
  have whole := present (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at whole
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using whole

theorem block_at (program : Program width 8) (entry : Nat)
    (blocks : List (List (Instruction width 8))) (index : Nat) (inside : index < blocks.length)
    (present : SharedRootRead.BlockAt program entry blocks.flatten) :
    SharedRootRead.BlockAt program ((offsets entry (blocks.map List.length))[index]'(by simpa using inside)) blocks[index] := by
  induction blocks generalizing entry index with
  | nil => simp at inside
  | cons first rest ih =>
    cases index with
    | zero =>
      exact left_at program entry first rest.flatten present
    | succ index =>
      have tail := right_at program entry first rest.flatten present
      simpa only [List.map_cons, offsets, List.getElem_cons_succ] using
        ih (entry + first.length) index (by simpa using inside) tail

/-- Every named block is fetched at its actual calculated absolute address. -/
theorem physical (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (code parameters graph width entry rows roots))
    (index : Nat) (inside : index < 17) :
    SharedRootRead.BlockAt program ((entries (labels parameters graph width entry))[index]'(by simpa [entries] using inside))
      ((chunks parameters graph width entry rows roots)[index]'(by simpa [chunks] using inside)) := by
  have found := block_at program entry (chunks parameters graph width entry rows roots) index
    (by simpa [chunks] using inside) present
  have addressEq := congrArg (fun values : List Nat => values[index]?)
    (entries_eq parameters graph width entry rows roots)
  have leftBound : index < (entries (labels parameters graph width entry)).length := by simpa [entries] using inside
  have rightBound : index < (offsets entry ((chunks parameters graph width entry rows roots).map List.length)).length := by
    simpa [chunks] using inside
  rw [List.getElem?_eq_getElem leftBound, List.getElem?_eq_getElem rightBound] at addressEq
  have exactAddress := Option.some.inj addressEq
  simpa only [exactAddress] using found

def program (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) : Program width 8 :=
  (code parameters graph width 0 rows roots).toArray

theorem resident_at (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) :
    SharedRootRead.BlockAt (program parameters graph width rows roots) 0 (code parameters graph width 0 rows roots) := by
  intro index inside
  simp only [program, Nat.zero_add, List.getElem?_toArray]

theorem call_at (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (resident : Program width 8)
    (present : SharedRootRead.BlockAt resident entry (code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt resident (labels parameters graph width entry).call
      (EnumerationPrefixOracle.callCode parameters graph width (labels parameters graph width entry).call
        (labels parameters graph width entry).oracle) := by
  have found := physical parameters graph width entry rows roots resident present 1 (by decide)
  simpa only [entries, chunks, List.getElem_cons_succ, List.getElem_cons_zero] using found

theorem restore_at (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (resident : Program width 8)
    (present : SharedRootRead.BlockAt resident entry (code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt resident (labels parameters graph width entry).restore
      (EnumerationPrefixReturn.code width (2 * parameters.channels)) := by
  have found := physical parameters graph width entry rows roots resident present 2 (by decide)
  simpa only [entries, chunks, List.getElem_cons_succ, List.getElem_cons_zero] using found

theorem oracle_at (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (resident : Program width 8)
    (present : SharedRootRead.BlockAt resident entry (code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt resident (labels parameters graph width entry).oracle
      (EnumerationPrefixOracle.oracleCode parameters graph width rows roots (labels parameters graph width entry).oracle
        (labels parameters graph width entry).restore) := by
  have found := physical parameters graph width entry rows roots resident present 16 (by decide)
  simpa only [entries, chunks, List.getElem_cons_succ, List.getElem_cons_zero] using found


end Controller.Cost.EnumerationDriverLayout
