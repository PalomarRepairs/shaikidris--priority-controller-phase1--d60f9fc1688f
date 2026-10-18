module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorRoot
public import Controller.Cost.ForestGuardRestore

@[expose] public section

/-!
# Declared-root provenance for the unweighted cursor

Before scanning a root, the caller records its declared position if no earlier
leaf has been selected. The first-feasible selector then retains this position
along with its route pointer. The block below fetches a found-cell test and a
conditional store. It applies to unweighted first-feasible selection.
-/
namespace Controller.Cost.ForestCursorRootStore

open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestMarkerMachine Controller.Cost.GateProgram
open Controller.Cost.ForestGuardSchedule
open Controller.Decoder Controller.Cost.ForestCursorRoot Controller.Cost.ForestCursorTraversal
open Controller.Cost.ForestGuardRestore Controller.Cost.ForestCursorExecution

def storeCode (width cell identifier : ℕ) : ForestCounter.Code width :=
  [.constant 2 (word width identifier), .constant 0 (word width cell), .store 0 2]

@[simp] theorem storeCode_length (width cell identifier : ℕ) :
    (storeCode width cell identifier).length = 3 := rfl

def storedHeap (width : ℕ) (heap : Array (Word width)) (cell identifier : ℕ) :
    Array (Word width) := heap.setIfInBounds cell (word width identifier)

theorem store_execution (program : Program width 4) (heap : Array (Word width))
    (base cell identifier : ℕ) (address loaded temporary : Word width)
    (fits : base + 3 < 2 ^ width) (cellFits : cell < 2 ^ width)
    (cellValid : cell < heap.size)
    (block : BlockAt program base (storeCode width cell identifier)) :
    Execution program (counterState heap base address loaded temporary)
      (counterState (storedHeap width heap cell identifier) (base + 3)
        (word width cell) loaded (word width identifier)) 3 (5 + heap.size) := by
  have first : program[base]? = some (.constant 2 (word width identifier)) := by
    simpa [storeCode] using block 0 (by simp)
  have second : program[base + 1]? = some (.constant 0 (word width cell)) := by
    simpa [storeCode] using block 1 (by simp)
  have third : program[base + 2]? = some (.store 0 2) := by
    simpa [storeCode] using block 2 (by simp)
  have a := increment_transition program heap base identifier address loaded temporary (by omega) first
  have b := address_transition program heap (base + 1) cell address loaded (word width identifier)
    (by omega) second
  have c := store_temporary_transition program heap (base + 2) cell loaded (word width identifier)
    (by omega) cellFits cellValid third
  simp only [Nat.add_assoc] at b c
  have heapEq : storedHeap width heap cell identifier = heap.set cell (word width identifier) cellValid := by
    simp [storedHeap, Array.setIfInBounds_def, cellValid]
  have trace := Execution.cons a (Execution.cons b (Execution.cons c (Execution.refl
    (counterState (heap.set cell (word width identifier) cellValid) (base + 3)
      (word width cell) loaded (word width identifier)))))
  simpa only [heapEq, counterState_liveWords, Array.size_set, Nat.zero_add, max_self] using trace

/-- The found bit bypasses provenance writes after the first selected leaf. -/
def rootCode (width base found cell identifier : ℕ) : ForestCounter.Code width :=
  zeroTest width base found (base + 7) ++ storeCode width cell identifier

@[simp] theorem rootCode_length (width base found cell identifier : ℕ) :
    (rootCode width base found cell identifier).length = 7 := rfl

def rootHeap (width : ℕ) (heap : Array (Word width)) (found cell identifier : ℕ) :
    Array (Word width) :=
  if (storedWord heap found).val = 0 then storedHeap width heap cell identifier else heap

/-- This is the actual conditional fetched caller block, with no padded ticks. -/
theorem root_execution (program : Program width 4) (heap : Array (Word width))
    (base found cell identifier : ℕ) (address loaded temporary : Word width)
    (fits : base + 7 < 2 ^ width) (foundFits : found < 2 ^ width)
    (foundValid : found < heap.size) (cellFits : cell < 2 ^ width)
    (cellValid : cell < heap.size)
    (test : BlockAt program base (zeroTest width base found (base + 7)))
    (store : BlockAt program (base + 4) (storeCode width cell identifier)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width,
      Execution program (counterState heap base address loaded temporary)
        (counterState (rootHeap width heap found cell identifier) (base + 7)
          finalAddress finalLoaded finalTemporary)
        (if (storedWord heap found).val = 0 then 6 else 4) (5 + heap.size) := by
  let value := heap[found]'foundValid
  have held : heap[found] = value := rfl
  have lookup : storedWord heap found = value := storedWord_eq heap found foundValid
  have first := zeroTest_execution program heap base found (base + 7) address loaded temporary
    value (by omega) fits foundFits foundValid held test
  by_cases zero : value.val = 0
  · rw [ite_eq_left zero] at first
    have second := store_execution program heap (base + 4) cell identifier (word width found)
      value temporary (by omega) cellFits cellValid store
    have trace := first.append second
    refine ⟨word width cell, value, word width identifier, ?_⟩
    simpa only [rootHeap, lookup, ite_eq_left zero, Nat.add_assoc, max_self] using trace
  · rw [ite_eq_right zero] at first
    refine ⟨word width found, value, temporary, ?_⟩
    simpa only [rootHeap, lookup, ite_eq_right zero] using first

/-- A separate provenance cell leaves the selector's found bit unchanged. -/
theorem rootHeap_found (width : ℕ) (heap : Array (Word width))
    (found cell identifier : ℕ) (different : found ≠ cell) :
    storedWord (rootHeap width heap found cell identifier) found = storedWord heap found := by
  unfold rootHeap
  split
  · unfold storedHeap storedWord
    by_cases valid : cell < heap.size
    · rw [Array.setIfInBounds_def, dite_eq_left valid, Array.getElem?_set_ne valid (Ne.symm different)]
    · simp only [Array.setIfInBounds_def, dite_eq_right valid]
  · rfl

/-- An in-range declared root is stored as its exact natural ID. -/
theorem rootHeap_decodes (width : ℕ) (heap : Array (Word width))
    (found cell identifier : ℕ) (unselected : (storedWord heap found).val = 0)
    (cellValid : cell < heap.size) (identifierFits : identifier < 2 ^ width) :
    (storedWord (rootHeap width heap found cell identifier) cell).val = identifier := by
  simp only [rootHeap, ite_eq_left unselected]
  have heapEq : storedHeap width heap cell identifier = heap.set cell (word width identifier) cellValid := by
    simp [storedHeap, Array.setIfInBounds_def, cellValid]
  rw [heapEq, storedWord_eq _ cell (by simpa using cellValid)]
  simpa only [Array.getElem_set_self, word] using Nat.mod_eq_of_lt identifierFits

/-- Once a leaf is selected, later root setup preserves the complete heap. -/
theorem rootHeap_selected (width : ℕ) (heap : Array (Word width))
    (found cell identifier : ℕ) (selected : (storedWord heap found).val ≠ 0) :
    rootHeap width heap found cell identifier = heap := by
  simp [rootHeap, selected]

/-- A provenance cell occupies its own heap region, separate from path counters
and the two selector metadata stores. -/
structure RootCellLayout (layout : SelectorLayout n) (cell : ℕ) : Prop where
  outside : Outside layout.counterOffset n cell
  found : cell ≠ layout.found
  best : cell ≠ layout.best

private theorem set_other (heap : Array (Word width)) (cell address : ℕ) (value : Word width)
    (different : address ≠ cell) : (heap.setIfInBounds cell value)[address]? = heap[address]? := by
  by_cases valid : cell < heap.size
  · rw [Array.setIfInBounds_def, dite_eq_left valid]
    exact Array.getElem?_set_ne valid (Ne.symm different)
  · simp [Array.setIfInBounds_def, valid]

/-- Every source operation retains the caller's declared-root provenance word. -/
theorem modelStep_rootCell (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) (cell : ℕ)
    (separate : RootCellLayout layout cell) (operation : CursorOp n) :
    (modelStep layout index b target state operation).heap[cell]? = state.heap[cell]? := by
  cases operation with
  | node owner => rfl
  | down owner position child => rfl
  | up => rfl
  | enter owner position channel =>
      exact update_outside width layout.counterOffset state.heap (.enter channel) cell separate.outside
  | leave owner position channel =>
      exact update_outside width layout.counterOffset state.heap (.leave channel) cell separate.outside
  | leaf owner route head =>
      change (leafHeap width state.heap layout b target head state.counters state.selected
        (index.pointer route))[cell]? = state.heap[cell]?
      unfold leafHeap
      split
      · unfold committedHeap
        rw [set_other _ layout.found cell _ separate.found,
          set_other _ layout.best cell _ separate.best]
      · rfl

theorem runModel_rootCell (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) (cell : ℕ)
    (separate : RootCellLayout layout cell) (operations : List (CursorOp n)) :
    (runModel layout index b target state operations).heap[cell]? = state.heap[cell]? := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      change (runModel layout index b target (modelStep layout index b target state operation) rest).heap[cell]? = _
      exact (ih _).trans (modelStep_rootCell layout index b target state cell separate operation)

/-- The caller's root-ID store retains represented graph and parent cells when
its allocated cell is distinct from every persistent source/descriptor address. -/
theorem rootHeap_frame (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (heap : Array (Word width))
    (frame : PersistentFrame graph records routes heap) (found cell identifier : ℕ)
    (separate : ∀ address, PersistentCell graph records routes address → address ≠ cell) :
    PersistentFrame graph records routes (rootHeap width heap found cell identifier) := by
  unfold rootHeap
  split
  · refine ⟨?_, ?_⟩
    · simpa [storedHeap] using frame.size
    · intro address persistent
      change (heap.setIfInBounds cell (word width identifier))[address]? = initial[address]?
      rw [set_other heap cell address _ (separate address persistent)]
      exact frame.cells address persistent
  · exact frame

/-- The unweighted cursor retains its first feasible leaf across later roots. -/
theorem modelStep_selected (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) (pointer : ℕ)
    (selected : state.selected = some pointer) (operation : CursorOp n) :
    (modelStep layout index b target state operation).selected = some pointer := by
  cases operation <;> simp [modelStep, leafChoice, selected]

theorem runModel_selected (layout : SelectorLayout n) (index : OccurrenceIndex graph)
    (b : ℕ) (target : Channel n) (state : RuntimeModel width n) (pointer : ℕ)
    (selected : state.selected = some pointer) (operations : List (CursorOp n)) :
    (runModel layout index b target state operations).selected = some pointer := by
  induction operations generalizing state with
  | nil => exact selected
  | cons operation rest ih =>
      exact ih _ (modelStep_selected layout index b target state pointer selected operation)

@[simp] theorem rootHeap_size (width : ℕ) (heap : Array (Word width))
    (found cell identifier : ℕ) : (rootHeap width heap found cell identifier).size = heap.size := by
  unfold rootHeap
  split <;> simp [storedHeap]

private theorem rootHeap_read (width : ℕ) (heap : Array (Word width))
    (found cell identifier address : ℕ) (different : address ≠ cell) (valid : address < heap.size) :
    (rootHeap width heap found cell identifier)[address]'(by simpa using valid) = heap[address]'valid := by
  have query : (rootHeap width heap found cell identifier)[address]? = heap[address]? := by
    unfold rootHeap
    split
    · exact set_other heap cell address (word width identifier) different
    · rfl
  simpa only [Array.getElem?_eq_getElem (by simpa using valid : address <
      (rootHeap width heap found cell identifier).size), Array.getElem?_eq_getElem valid,
    Option.some.injEq] using query

/-- Setup preserves every invariant consumed by the checked full root execution.
The separately allocated root cell is outside both mutable and persistent cells. -/
theorem setup_runtimeStored (graph : DAG n) (records : GraphRecords width initial graph)
    (routes : RouteDescriptors width initial) (layout : SelectorLayout n)
    (state : RuntimeModel width n) (held : RuntimeStored graph records routes layout state)
    (cell identifier : ℕ) (separate : RootCellLayout layout cell)
    (persistent : ∀ address, PersistentCell graph records routes address → address ≠ cell) :
    RuntimeStored graph records routes layout
      { state with heap := rootHeap width state.heap layout.found cell identifier } := by
  constructor
  · refine ⟨fun channel => by simpa using held.counters.valid channel, ?_⟩
    intro channel
    have different : layout.counterOffset + channel.val ≠ cell := by
      have bound := channel.isLt
      rcases separate.outside with before | after <;> omega
    exact (rootHeap_read width state.heap layout.found cell identifier _ different
      (held.counters.valid channel)).trans (held.counters.held channel)
  · refine ⟨by simpa using held.selector.foundValid, by simpa using held.selector.bestValid, ?_, ?_⟩
    · exact (rootHeap_read width state.heap layout.found cell identifier _ separate.found.symm
        held.selector.foundValid).trans held.selector.foundWord
    · intro pointer selected
      exact (rootHeap_read width state.heap layout.found cell identifier _ separate.best.symm
        held.selector.bestValid).trans (held.selector.bestWord pointer selected)
  · exact rootHeap_frame graph records routes state.heap held.persistent layout.found cell identifier persistent

end Controller.Cost.ForestCursorRootStore
