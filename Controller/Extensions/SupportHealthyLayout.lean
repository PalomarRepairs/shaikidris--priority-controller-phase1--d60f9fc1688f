module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportSourceRepack
public import Controller.Extensions.SupportCandidate

@[expose] public section

/-! A healthy evaluation table becomes part of the retained header. Source
fields are fetched from the old cache; only its two-column address directory
is shifted by the number of inserted healthy words. -/
namespace Controller.Extensions.SupportHealthyLayout
open Controller.Cost Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Extensions.ResolvedSourceEmit

def reads (width base delta : Nat) : Nat → List (Operand width)
  | 0 => []
  | count+1 => .read base (word width delta) :: reads width (base+1) delta count

@[simp] theorem reads_length : (reads width base delta count).length = count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => simp [reads,ih]

theorem reads_stored (heap : Array (Word width)) (base delta : Nat) (values : List (Word width))
    (cells : ∀ i (below : i<values.length), heap[base+i]? = some values[i]) :
    List.Forall₂ (Stored heap) (reads width base delta values.length)
      (values.map (fun value => word width (value.val+delta))) := by
  induction values generalizing base with
  | nil => exact .nil
  | cons value rest ih =>
    apply List.Forall₂.cons
    · have cell := cells 0 (by simp)
      change heap[base+0]? = some value at cell
      have stored := Stored.read base (word width delta) value (by simpa using cell)
      convert stored using 1
      apply Fin.ext
      simp [word,Nat.add_mod]
    · apply ih (base+1)
      intro i below
      have cell := cells (i+1) (by simp; omega)
      simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cell

theorem reads_zero (heap : Array (Word width)) (base : Nat) (values : List (Word width))
    (cells : ∀ i (below : i<values.length), heap[base+i]? = some values[i]) :
    List.Forall₂ (Stored heap) (reads width base 0 values.length) values := by
  have same : values.map (fun value => word width (value.val+0)) = values := by
    apply List.map_id'' (fun value => ?_)
    exact Fin.ext (by simp only [Nat.add_zero,word,Nat.mod_eq_of_lt value.isLt])
  simpa only [same] using reads_stored heap base 0 values cells

theorem reads_naturals (heap : Array (Word width)) (base delta : Nat) (values : List Nat)
    (cells : ∀ i (below : i<values.length), heap[base+i]? = some (word width values[i])) :
    List.Forall₂ (Stored heap) (reads width base delta values.length)
      (values.map (fun value => word width (value+delta))) := by
  have trace := reads_stored heap base delta (values.map (word width))
    (by intro i below; simpa only [List.getElem_map] using cells i (by simpa using below))
  simpa only [List.length_map,List.map_map,Function.comp_def,word,Nat.add_mod,Nat.mod_mod] using trace

theorem rowBases_shift (rows : List Row) (child guard delta : Nat) :
    rowBases rows (child+delta) (guard+delta) = (rowBases rows child guard).map (·+delta) := by
  induction rows generalizing child guard with
  | nil => rfl
  | cons row rest ih =>
    simp only [rowBases,List.map_cons]
    congr 2
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (child+countSource row.children 0) (guard+countSource row.guards 0)

private theorem preserve_value (heap : Array (Word width)) (values : Fin m → Bool)
    (address : Nat) (value : Word width) (stored : heap[address]? = some value) :
    (withValues heap values)[address]? = some value := by
  unfold withValues
  rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp stored).1]
  exact stored

def tail (rows : List Row) (roots : List Nat) : List Nat :=
  rowArities rows ++ rowChildren rows ++ rowGuards rows ++ roots

@[simp] theorem tail_length : (tail rows roots).length =
    2*rows.length+(rowChildren rows).length+(rowGuards rows).length+roots.length := by simp [tail,Nat.add_assoc]

def plan (width n m : Nat) (header : Array (Word width)) (rows : List Row) (roots : List Nat) : List (Operand width) :=
  reads width 0 0 header.size ++
    (reads width ((cacheHeap width header rows roots).size+n) 0 m ++
    (reads width header.size 0 (2*rows.length) ++
    (reads width (header.size+2*rows.length) m (2*rows.length) ++
    reads width (header.size+4*rows.length) 0 (tail rows roots).length)))

theorem plan_length (header : Array (Word width)) (rows : List Row) (roots : List Nat) :
    (plan width n m header rows roots).length =
      (cacheHeap width header rows roots).size+m := by
  simp only [plan,List.length_append,reads_length,tail_length,cacheHeap_size]
  omega

set_option maxHeartbeats 1600000 in
theorem stored (header : Array (Word width)) (rows : List Row) (roots : List Nat)
    (channels : Controller.Assignment n) (healthy : Fin m → Bool) :
    List.Forall₂ (Stored (evaluationHeap header rows roots channels healthy))
      (plan width n m header rows roots)
      (cacheHeap width (header ++ (List.ofFn (fun i => boolWord width (healthy i))).toArray) rows roots).toList := by
  let heap := evaluationHeap header rows roots channels healthy
  let old := cacheHeap width header rows roots
  let values := List.ofFn (fun i => boolWord width (healthy i))
  let directory := rowBases rows (header.size+6*rows.length)
    (header.size+6*rows.length+(rowChildren rows).length)
  have retained : ∀ (address : Nat) (value : Word width), old[address]? = some value → heap[address]? = some value := by
    intro address value cell
    exact preserve_value _ healthy _ _ (preserve_value _ channels _ _ cell)
  have segment : ∀ (before middle after : List Nat), serializedRows header.size rows roots = before++middle++after →
      ∀ i (below : i<middle.length), heap[header.size+before.length+i]? = some (word width middle[i]) := by
    intro before middle after same i below
    apply retained
    change (Controller.Cost.ForestCursorMaterialize.allocatedHeap width header
      (serializedRows header.size rows roots))[header.size+before.length+i]? = _
    rw [same,Array.getElem?_eq_getElem (by simp; omega)]
    exact congrArg some (allocated_segment_word header before middle after i below)
  have metadata : List.Forall₂ (Stored heap) (reads width 0 0 header.size) header.toList := by
    apply reads_zero
    intro i below
    apply retained
    unfold old cacheHeap Controller.Cost.ForestCursorMaterialize.allocatedHeap
    rw [Array.getElem?_append_left (by simpa using below)]
    simpa using (Array.getElem?_eq_getElem (by simpa using below) : header[i]? = _)
  have health : List.Forall₂ (Stored heap) (reads width (old.size+n) 0 m) values := by
    have length : values.length = m := by simp [values]
    rw [← length]
    apply reads_zero
    intro i below
    let node : Fin m := ⟨i,by simpa only [length] using below⟩
    have cell := value_cell (channelHeap header rows roots channels) healthy node
    rw [Array.getElem?_eq_getElem (by
      simp only [heap,evaluationHeap_size]
      change old.size+n+i < old.size+n+m
      omega)]
    simpa only [heap,evaluationHeap,channelHeap_size,node,values,List.getElem_ofFn] using congrArg some cell
  have headers : List.Forall₂ (Stored heap) (reads width header.size 0 (2*rows.length))
      ((rowHeaders rows).map (word width)) := by
    have trace := reads_naturals heap header.size 0 (rowHeaders rows)
      (by intro i below
          simpa only [List.length_nil,Nat.add_zero] using
            segment [] (rowHeaders rows) (directory++tail rows roots)
              (by simp [serializedRows,directory,tail,List.append_assoc]) i below)
    simpa only [rowHeaders_length,Nat.add_zero] using trace
  have bases : List.Forall₂ (Stored heap) (reads width (header.size+2*rows.length) m (2*rows.length))
      (directory.map (fun value => word width (value+m))) := by
    have trace := reads_naturals heap (header.size+2*rows.length) m directory
      (by intro i below
          simpa only [rowHeaders_length] using segment (rowHeaders rows) directory (tail rows roots)
            (by simp [serializedRows,directory,tail,List.append_assoc]) i below)
    simpa only [directory,rowBases_length] using trace
  have last : List.Forall₂ (Stored heap) (reads width (header.size+4*rows.length) 0 (tail rows roots).length)
      ((tail rows roots).map (word width)) := by
    have trace := reads_naturals heap (header.size+4*rows.length) 0 (tail rows roots)
      (by intro i below
          have cell := segment (rowHeaders rows++directory) (tail rows roots) []
            (by simp [serializedRows,directory,tail,List.append_assoc]) i below
          have prefixLength : (rowHeaders rows++directory).length = 4*rows.length := by
            simp only [List.length_append,rowHeaders_length,directory,rowBases_length]; omega
          simpa only [prefixLength] using cell)
    simpa only [Nat.add_zero] using trace
  have assembled := List.rel_append metadata (List.rel_append health (List.rel_append headers (List.rel_append bases last)))
  have directoryShift : rowBases rows (header.size+m+6*rows.length)
      (header.size+m+6*rows.length+(rowChildren rows).length) = directory.map (·+m) := by
    simpa only [directory,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      rowBases_shift rows (header.size+6*rows.length) (header.size+6*rows.length+(rowChildren rows).length) m
  simpa only [heap,old,plan,cacheHeap,Controller.Cost.ForestCursorMaterialize.allocatedHeap,Array.toList_append,
    List.toList_toArray,Array.size_append,List.size_toArray,List.length_ofFn,serializedRows,directoryShift,
    List.map_append,List.map_map,Function.comp_def,tail,List.append_assoc,values] using assembled

end Controller.Extensions.SupportHealthyLayout
