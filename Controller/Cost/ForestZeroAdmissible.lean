module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroPositive
public import Controller.Cost.ForestZeroAssembly

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Optional nonemptiness-row construction preserves the actual dictionary
count on the machine stack before the bounded search. Positive-row cells are
obtained from the executed descending table loop, and two real stores install
its directory endpoints in an already reserved row slot. -/
namespace Controller.Cost.ForestZeroAdmissible
variable {width : ℕ}
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroBuild Controller.Cost.ForestZeroAssembly

private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) (fits : cursor < 2 ^ width) :
    (atState heap cursor x0 x1 x2 x3 stack output).advance =
      atState heap (cursor + 1) x0 x1 x2 x3 stack output := by
  simp [atState, State.advance, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put0_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 0 (word width value) =
      atState heap cursor value x1 x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put3_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 3 (word width value) =
      atState heap cursor x0 x1 x2 value stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put1_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 1 (word width value) =
      atState heap cursor x0 value x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put2_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 2 (word width value) =
      atState heap cursor x0 x1 value x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl



/-- Preserve an emitted signed stream under an actual old-cell frame. -/
theorem RawStored.frame (stored : RawStored width row start before)
    (growth : before.size ≤ after.size)
    (cells : ∀ address, address < before.size → after[address]? = before[address]?) :
    RawStored width row start after := by
  induction stored with
  | nil start heap bound => exact RawStored.nil start after (by omega)
  | cons literal rest start heap label polarity tail ih =>
    have first : start < heap.size := (Array.getElem?_eq_some_iff.mp label).1
    have second : start + 1 < heap.size := (Array.getElem?_eq_some_iff.mp polarity).1
    exact RawStored.cons literal rest start after ((cells start first).trans label)
      ((cells (start + 1) second).trans polarity) (ih growth cells)

/-- The countdown emitter only appends; all previous pair cells remain exact. -/
theorem pairHeap_prefix (heap : Array (Word width)) (labels : List ℕ)
    (address : ℕ) (old : address < heap.size) :
    (ForestZeroPositive.pairHeap heap labels)[address]? = heap[address]? := by
  induction labels generalizing heap with
  | nil => rfl
  | cons localIndex rest ih =>
    have first : (heap.push (word width localIndex))[address]? = heap[address]? := by
      simp only [Array.getElem?_push, ite_eq_right (show address ≠ heap.size by omega)]
    have second : ((heap.push (word width localIndex)).push (word width 1))[address]? =
        (heap.push (word width localIndex))[address]? := by
      simp only [Array.getElem?_push, Array.size_push, ite_eq_right (show address ≠ heap.size + 1 by omega)]
    exact (ih ((heap.push (word width localIndex)).push (word width 1))
      (by simp only [Array.size_push]; omega)).trans (second.trans first)

/-- Actual allocated pairs represent the new row, including every localIndex ID. -/
theorem pairHeap_raw (heap : Array (Word width)) (labels : List ℕ) :
    RawStored width (labels.map (fun localIndex => (localIndex, true))) heap.size
      (ForestZeroPositive.pairHeap heap labels) := by
  induction labels generalizing heap with
  | nil => exact RawStored.nil heap.size heap le_rfl
  | cons localIndex rest ih =>
    let pair := (heap.push (word width localIndex)).push (word width 1)
    have first : pair[heap.size]? = some (word width localIndex) := by
      simp only [pair, Array.getElem?_push, Array.size_push,
        ite_eq_right (show heap.size ≠ heap.size + 1 by omega), ite_eq_left rfl, ite_true]
    have second : pair[heap.size + 1]? = some (word width 1) := by
      simp only [pair, Array.getElem?_push, Array.size_push, ite_eq_left rfl, ite_true]
    have tail := ih pair
    have size : pair.size = heap.size + 2 := by simp [pair]
    rw [size] at tail
    exact RawStored.cons (localIndex, true) _ heap.size _
      ((pairHeap_prefix pair rest heap.size (by rw [size]; omega)).trans first)
      ((pairHeap_prefix pair rest (heap.size + 1) (by rw [size]; omega)).trans second) tail

/-- The localIndex count is saved before the search overwrites register two with
its physical table pointer. It is independent of the mutable inputHeader. -/
def savedSearchCode (width base : ℕ) : Code width :=
  [.push 2] ++ ForestZeroNonempty.fullCode width (base + 1)

@[simp] theorem savedSearchCode_length : (savedSearchCode width base).length = 19 := rfl

private theorem save_execution (program : Program width 4) (heap : Array (Word width))
    (base input table count scratch : ℕ) (stack output : List (Word width))
    (fits : base + 1 < 2 ^ width) (entry : program[base]? = some (.push 2)) :
    Execution program (atState heap base input table count scratch stack output)
      (atState heap (base + 1) input table count scratch (word width count :: stack) output)
      1 (6 + heap.size + stack.length + output.length) := by
  let first := atState heap base input table count scratch stack output
  let final := atState heap (base + 1) input table count scratch (word width count :: stack) output
  have transition : programStep program first = some final := by
    rw [fetched program first base (.push 2) rfl (by omega) entry]
    change some { first.advance with stack := word width count :: stack } = some final
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  convert Execution.cons transition (Execution.refl final) using 1 <;>
    simp only [first, final, atState, State.liveWords, List.length_cons] <;> omega

theorem saved_search_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (base channels input scratch : ℕ)
    (stack output : List (Word width)) (within : channels ≤ ambient)
    (channelCell : heap[0]? = some (word width channels)) (valid : 0 < heap.size)
    (heapFits : heap.size < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (fits : base + 21 < 2 ^ width) (block : BlockAt program base (savedSearchCode width base)) :
    let result := ForestZeroNonempty.search state (state.coordinates.size + 1) channels 0
    ∃ ticks, Execution program
      (atState heap base input layout.tableBase state.coordinates.size scratch stack output)
      (atState heap (base + 8 + ForestZeroNonempty.exitOffset result.reason)
        (channels - result.marked) (state.coordinates.size + 1 - result.marked)
        (layout.tableBase + result.marked) 0 (word width state.coordinates.size :: stack) output)
      ticks (6 + heap.size + stack.length + output.length) ∧
      ticks ≤ 11 * min channels (state.coordinates.size + 1) + 12 ∧
      result.reason ≠ .exhausted := by
  have prefixBlock := BlockAt.prefix program base _ _ block
  have searchBlock : BlockAt program (base + 1) (ForestZeroNonempty.fullCode width (base + 1)) := by
    simpa only [List.length_cons, List.length_nil, Nat.add_zero] using
      BlockAt.suffix program base [.push 2] _ block
  have first := save_execution program heap base input layout.tableBase state.coordinates.size scratch
    stack output (by omega) (by simpa using prefixBlock 0 (by simp))
  obtain ⟨ticks, later, bound, notExhausted⟩ := ForestZeroNonempty.loaded_bounded_execution
    program heap layout state represented (base + 1) channels input scratch
    (word width state.coordinates.size :: stack) output within channelCell valid heapFits ambientFits
    (by omega) searchBlock
  refine ⟨1 + ticks, ?_, by omega, notExhausted⟩
  convert first.append later using 1 <;>
    simp only [List.length_cons, Nat.add_assoc, Nat.max_self] <;> omega

/-- The reserved optional row receives actual source cursor words. Register
three contains its physically formed directory address. -/
def boundaryCode (width : ℕ) : Code width :=
  [.store 3 0, .constant 2 (word width 1), .add 3 3 2, .store 3 1]

@[simp] theorem boundaryCode_length : (boundaryCode width).length = 4 := rfl

def boundaryHeap (heap : Array (Word width)) (slot start finish : ℕ) : Array (Word width) :=
  (heap.setIfInBounds slot (word width start)).setIfInBounds (slot + 1) (word width finish)

/-- Bounds and separation are explicit: these are directory stores, never
writes to the shared dictionary or immutable graph prefix. -/
theorem boundary_prefix (heap : Array (Word width)) (slot start finish address : ℕ)
    (before : address < slot) :
    (boundaryHeap heap slot start finish)[address]? = heap[address]? := by
  unfold boundaryHeap
  rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega)]

@[simp] theorem boundaryHeap_size : (boundaryHeap heap slot start finish).size = heap.size := by
  simp only [boundaryHeap, Array.size_setIfInBounds]

theorem boundary_cells (heap : Array (Word width)) (slot start finish : ℕ)
    (valid : slot + 1 < heap.size) :
    (boundaryHeap heap slot start finish)[slot]? = some (word width start) ∧
    (boundaryHeap heap slot start finish)[slot + 1]? = some (word width finish) := by
  constructor
  · unfold boundaryHeap
    rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_self_of_lt (by omega)]
  · unfold boundaryHeap
    apply Array.getElem?_setIfInBounds_self_of_lt
    simpa only [Array.size_setIfInBounds] using valid

/-- Four actual stores/arithmetic transitions install the optional directory
row. The saved dictionary-count stack word is untouched. -/
theorem boundary_execution (program : Program width 4) (heap : Array (Word width))
    (base slot start finish count : ℕ) (stack output : List (Word width))
    (valid : slot + 1 < heap.size) (slotFits : slot + 1 < 2 ^ width)
    (fits : base + 4 < 2 ^ width) (block : BlockAt program base (boundaryCode width)) :
    Execution program (atState heap base start finish count slot stack output)
      (atState (boundaryHeap heap slot start finish) (base + 4) start finish 1 (slot + 1) stack output)
      4 (5 + heap.size + stack.length + output.length) := by
  let firstHeap := heap.setIfInBounds slot (word width start)
  let s0 := atState heap base start finish count slot stack output
  let s1 := atState firstHeap (base + 1) start finish count slot stack output
  let s2 := atState firstHeap (base + 2) start finish 1 slot stack output
  let s3 := atState firstHeap (base + 3) start finish 1 (slot + 1) stack output
  let s4 := atState (boundaryHeap heap slot start finish) (base + 4) start finish 1 (slot + 1) stack output
  have slotWord : (word width slot).val = slot := Nat.mod_eq_of_lt (by omega)
  have nextWord : (word width (slot + 1)).val = slot + 1 := Nat.mod_eq_of_lt slotFits
  have oneWord : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have firstBound : slot < heap.size := by omega
  have secondBound : slot + 1 < firstHeap.size := by simpa only [firstHeap, Array.size_setIfInBounds] using valid
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.store 3 0) rfl (by omega)
      (by simpa [boundaryCode] using block 0 (by simp [boundaryCode]))]
    change (if h : (word width slot).val < heap.size then
      some { s0.advance with heap := heap.set (word width slot).val (word width start) } else none) = some s1
    rw [slotWord, dite_eq_left firstBound, advance_at _ _ _ _ _ _ _ _ (by omega)]
    simp only [s1, firstHeap, Array.setIfInBounds_def, dite_eq_left firstBound, atState]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.constant 2 (word width 1)) rfl (by omega)
      (by simpa [boundaryCode] using block 1 (by simp [boundaryCode]))]
    change some (s1.advance.put 2 (word width 1)) = some s2
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.add 3 3 2) rfl (by omega)
      (by simpa [boundaryCode] using block 2 (by simp [boundaryCode]))]
    change some (s2.advance.put 3 (word width ((word width slot).val + (word width 1).val))) = some s3
    rw [slotWord, oneWord, advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.store 3 1) rfl (by omega)
      (by simpa [boundaryCode] using block 3 (by simp [boundaryCode]))]
    change (if h : (word width (slot + 1)).val < firstHeap.size then
      some { s3.advance with heap := firstHeap.set (word width (slot + 1)).val (word width finish) }
      else none) = some s4
    rw [nextWord, dite_eq_left secondBound, advance_at _ _ _ _ _ _ _ _ (by omega)]
    simp only [s4, boundaryHeap, firstHeap, Array.setIfInBounds_def, dite_eq_left firstBound,
      Array.size_set, dite_eq_left valid, Nat.add_assoc, atState]
  have first := Execution.cons t0 (Execution.cons t1 (Execution.refl s2))
  have later := Execution.cons t2 (Execution.cons t3 (Execution.refl s4))
  convert first.append later using 1 <;>
    simp only [s0, s1, s2, s3, s4, atState, State.liveWords, firstHeap,
      boundaryHeap_size, Array.size_setIfInBounds, Nat.max_self] <;> omega

open Controller.Horn.SourceDirectory Controller.Horn.SourceScan Controller.Horn.RowScan

private theorem cursor_frame {before after : Array (Word width)}
    (stored : CursorStored pointer header before)
    (growth : before.size ≤ after.size)
    (cell : after[header]? = before[header]?) : CursorStored pointer header after := by
  have valid : header < after.size := lt_of_lt_of_le stored.bound growth
  refine ⟨valid, ?_⟩
  have value : before[header]? = some (word width pointer) := by
    rw [Array.getElem?_eq_getElem stored.bound, stored.value]
  exact Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans (cell.trans value))

private theorem source_frame (stored : SourceStored clause start before)
    (growth : before.size ≤ after.size)
    (cells : ∀ address, start ≤ address → address < start + 2 * clause.length →
      after[address]? = before[address]?) : SourceStored clause start after := by
  refine ⟨stored.fits.trans growth, ?_⟩
  intro index
  have original := stored.entry index
  have first : start + 2 * index.val < before.size := by have := original.fits; omega
  have second : start + 2 * index.val + 1 < before.size := by have := original.fits; omega
  have firstNew := lt_of_lt_of_le first growth
  have secondNew := lt_of_lt_of_le second growth
  refine ⟨original.fits.trans growth, ?_, ?_⟩
  · have value := cells (start + 2 * index.val) (by omega) (by have := index.isLt; omega)
    rw [Array.getElem?_eq_getElem firstNew, Array.getElem?_eq_getElem first] at value
    exact (Option.some.inj value).trans original.label
  · have value := cells (start + 2 * index.val + 1) (by omega) (by have := index.isLt; omega)
    rw [Array.getElem?_eq_getElem secondNew, Array.getElem?_eq_getElem second] at value
    exact (Option.some.inj value).trans original.polarity

/-- Pair allocations preserve every original directory and literal cell. -/
theorem stored_pairs (stored : Stored rows directory source heap) (labels : List ℕ) :
    Stored rows directory source (ForestZeroPositive.pairHeap heap labels) := by
  have growth : heap.size ≤ (ForestZeroPositive.pairHeap heap labels).size := by
    rw [ForestZeroPositive.pairHeap_size]; omega
  refine ⟨stored.fits.trans growth, ?_, ?_⟩
  · intro index
    have original := stored.entry index
    exact ⟨cursor_frame original.1 growth (pairHeap_prefix heap labels _ original.1.bound),
      cursor_frame original.2 growth (pairHeap_prefix heap labels _ original.2.bound)⟩
  · intro index
    have original := stored.literals index
    apply source_frame original growth
    intro address _ before
    exact pairHeap_prefix heap labels address (lt_of_lt_of_le before original.fits)

/-- The two reserved directory cells lie after old entries and before source
pairs, so installing them preserves every existing clause occurrence. -/
theorem stored_boundary (stored : Stored rows directory source heap)
    (separation : directory + 2 * rows.length + 2 ≤ source)
    (start finish : ℕ) :
    Stored rows directory source
      (boundaryHeap heap (directory + 2 * rows.length) start finish) := by
  have size : (boundaryHeap heap (directory + 2 * rows.length) start finish).size = heap.size :=
    boundaryHeap_size
  refine ⟨by rw [size]; exact stored.fits, ?_, ?_⟩
  · intro index
    have original := stored.entry index
    have left : directory + 2 * index.val < directory + 2 * rows.length := by have := index.isLt; omega
    have right : directory + 2 * index.val + 1 < directory + 2 * rows.length := by have := index.isLt; omega
    exact ⟨cursor_frame original.1 (by rw [size]) (boundary_prefix heap _ start finish _ left),
      cursor_frame original.2 (by rw [size]) (boundary_prefix heap _ start finish _ right)⟩
  · intro index
    have original := stored.literals index
    apply source_frame original (by rw [size])
    intro address above _
    have sourceBelow : source ≤ sourceOffset rows source index.val := by
      unfold sourceOffset; omega
    unfold boundaryHeap
    rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega)]

private theorem sourceOffset_append_prefix (rows : List (Clause (Fin locals)))
    (last : Clause (Fin locals)) (source index : ℕ) (within : index ≤ rows.length) :
    sourceOffset (rows ++ [last]) source index = sourceOffset rows source index := by
  unfold sourceOffset
  rw [List.take_append, Nat.sub_eq_zero_of_le within]
  simp

/-- Original entries and an actually emitted final row give the complete
physical clause directory, retaining ordered and duplicate occurrences. -/
theorem stored_append_last (rows : List (Clause (Fin locals))) (last : Clause (Fin locals))
    (directory source : ℕ) (heap : Array (Word width))
    (old : Stored rows directory source heap)
    (slotRoom : directory + 2 * rows.length + 2 ≤ heap.size)
    (first : CursorStored (sourceOffset rows source rows.length)
      (directory + 2 * rows.length) heap)
    (finish : CursorStored (sourceOffset rows source rows.length + 2 * last.length)
      (directory + 2 * rows.length + 1) heap)
    (newRow : SourceStored last (sourceOffset rows source rows.length) heap) :
    Stored (rows ++ [last]) directory source heap := by
  refine ⟨by simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.mul_add, Nat.mul_one, Nat.add_assoc] using slotRoom, ?_, ?_⟩
  · intro index
    by_cases before : index.val < rows.length
    · have original := old.entry ⟨index.val, before⟩
      simpa only [sourceOffset_append_prefix rows last source index.val (by omega),
        sourceOffset_append_prefix rows last source (index.val + 1) (by omega)] using original
    · have lastIndex : index.val = rows.length := by have := index.isLt; simp only [List.length_append, List.length_cons, List.length_nil] at this; omega
      rw [lastIndex]
      constructor
      · simpa only [sourceOffset_append_prefix rows last source rows.length le_rfl] using first
      · simpa [sourceOffset, List.take_append, List.take_of_length_le, Nat.add_mul, Nat.mul_add,
          Nat.add_assoc] using finish
  · intro index
    by_cases before : index.val < rows.length
    · have original := old.literals ⟨index.val, before⟩
      simpa only [List.getElem_append_left before,
        sourceOffset_append_prefix rows last source index.val (by omega)] using original
    · have lastIndex : index.val = rows.length := by have := index.isLt; simp only [List.length_append, List.length_cons, List.length_nil] at this; omega
      simpa [lastIndex, sourceOffset_append_prefix rows last source rows.length le_rfl] using newRow

/-- The executed positive-pair loop and reserved boundary stores install a
complete source row. The typed clause is tied to the emitted IDs by equality. -/
theorem installed_positive_stored (rows : List (Clause (Fin locals)))
    (last : Clause (Fin locals)) (labels : List ℕ) (heap : Array (Word width))
    (directory source : ℕ) (old : Stored rows directory source heap)
    (sourceEnd : sourceOffset rows source rows.length = heap.size)
    (separation : directory + 2 * rows.length + 2 ≤ source)
    (reserved : directory + 2 * rows.length + 2 ≤ heap.size)
    (emitted : last.map (fun literal => (literal.1.val, literal.2)) =
      labels.map (fun localIndex => (localIndex, true))) :
    Stored (rows ++ [last]) directory source
      (boundaryHeap (ForestZeroPositive.pairHeap heap labels)
        (directory + 2 * rows.length) heap.size
        (ForestZeroPositive.pairHeap heap labels).size) := by
  let pairs := ForestZeroPositive.pairHeap heap labels
  let final := boundaryHeap pairs (directory + 2 * rows.length) heap.size pairs.size
  have pairSize : pairs.size = heap.size + 2 * labels.length := ForestZeroPositive.pairHeap_size heap labels
  have lengths : last.length = labels.length := by
    have same := congrArg List.length emitted
    simpa only [List.length_map] using same
  have oldFinal : Stored rows directory source final :=
    stored_boundary (stored_pairs old labels) separation heap.size pairs.size
  have cells := boundary_cells pairs (directory + 2 * rows.length) heap.size pairs.size (by rw [pairSize]; omega)
  have first : CursorStored heap.size (directory + 2 * rows.length) final := by
    refine ⟨by simp only [final, boundaryHeap_size]; rw [pairSize]; omega, ?_⟩
    exact Option.some.inj ((Array.getElem?_eq_getElem (by simp only [final, boundaryHeap_size]; rw [pairSize]; omega)).symm.trans cells.1)
  have finish : CursorStored pairs.size (directory + 2 * rows.length + 1) final := by
    refine ⟨by simp only [final, boundaryHeap_size]; rw [pairSize]; omega, ?_⟩
    exact Option.some.inj ((Array.getElem?_eq_getElem (by simp only [final, boundaryHeap_size]; rw [pairSize]; omega)).symm.trans cells.2)
  have raw : RawStored width (last.map (fun literal => (literal.1.val, literal.2))) heap.size pairs := by
    rw [emitted]; exact pairHeap_raw heap labels
  have newPairs := raw_to_source last raw
  have newFinal : SourceStored last heap.size final := by
    apply source_frame newPairs (by simp only [final, boundaryHeap_size]; exact le_rfl)
    intro address above _
    unfold final boundaryHeap
    rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega)]
  apply stored_append_last rows last directory source final oldFinal
  · simp only [final, boundaryHeap_size]; rw [pairSize]; omega
  · simpa only [sourceEnd] using first
  · simpa only [sourceEnd, lengths, pairSize] using finish
  · simpa only [sourceEnd] using newFinal

/-- Active directory/source endpoints are installed from the actual cursor
registers. The localIndex count stays on the stack across this routine. -/
def activeCode (width recordHeader endHeader : ℕ) : Code width :=
  [.constant 3 (word width recordHeader), .store 3 1,
   .constant 3 (word width endHeader), .store 3 0]

@[simp] theorem activeCode_length : (activeCode width recordHeader endHeader).length = 4 := rfl

def activeHeap (heap : Array (Word width)) (recordHeader endHeader sourceEnd directoryEnd : ℕ) :=
  (heap.setIfInBounds recordHeader (word width sourceEnd)).setIfInBounds endHeader (word width directoryEnd)

@[simp] theorem activeHeap_size : (activeHeap heap recordHeader endHeader sourceEnd directoryEnd).size = heap.size := by
  simp only [activeHeap, Array.size_setIfInBounds]

theorem active_prefix (heap : Array (Word width)) (recordHeader endHeader sourceEnd directoryEnd address : ℕ)
    (recordAbove : address < recordHeader) (endAbove : address < endHeader) :
    (activeHeap heap recordHeader endHeader sourceEnd directoryEnd)[address]? = heap[address]? := by
  unfold activeHeap
  rw [Array.getElem?_setIfInBounds_ne (by omega), Array.getElem?_setIfInBounds_ne (by omega)]

theorem active_execution (program : Program width 4) (heap : Array (Word width))
    (base recordHeader endHeader sourceEnd directoryEnd count scratch : ℕ)
    (stack output : List (Word width))
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (recordFits : recordHeader < 2 ^ width) (endFits : endHeader < 2 ^ width)
    (fits : base + 4 < 2 ^ width)
    (block : BlockAt program base (activeCode width recordHeader endHeader)) :
    Execution program (atState heap base directoryEnd sourceEnd count scratch stack output)
      (atState (activeHeap heap recordHeader endHeader sourceEnd directoryEnd)
        (base + 4) directoryEnd sourceEnd count endHeader stack output)
      4 (5 + heap.size + stack.length + output.length) := by
  let firstHeap := heap.setIfInBounds recordHeader (word width sourceEnd)
  let s0 := atState heap base directoryEnd sourceEnd count scratch stack output
  let s1 := atState heap (base + 1) directoryEnd sourceEnd count recordHeader stack output
  let s2 := atState firstHeap (base + 2) directoryEnd sourceEnd count recordHeader stack output
  let s3 := atState firstHeap (base + 3) directoryEnd sourceEnd count endHeader stack output
  let s4 := atState (activeHeap heap recordHeader endHeader sourceEnd directoryEnd)
    (base + 4) directoryEnd sourceEnd count endHeader stack output
  have recordWord : (word width recordHeader).val = recordHeader := Nat.mod_eq_of_lt recordFits
  have endWord : (word width endHeader).val = endHeader := Nat.mod_eq_of_lt endFits
  have secondBound : endHeader < firstHeap.size := by simpa only [firstHeap, Array.size_setIfInBounds] using endValid
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 3 (word width recordHeader)) rfl (by omega)
      (by simpa [activeCode] using block 0 (by simp [activeCode]))]
    change some (s0.advance.put 3 (word width recordHeader)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.store 3 1) rfl (by omega)
      (by simpa [activeCode] using block 1 (by simp [activeCode]))]
    change (if h : (word width recordHeader).val < heap.size then
      some { s1.advance with heap := heap.set (word width recordHeader).val (word width sourceEnd) } else none) = some s2
    rw [recordWord, dite_eq_left recordValid, advance_at _ _ _ _ _ _ _ _ (by omega)]
    simp only [s2, firstHeap, Array.setIfInBounds_def, dite_eq_left recordValid, atState]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.constant 3 (word width endHeader)) rfl (by omega)
      (by simpa [activeCode] using block 2 (by simp [activeCode]))]
    change some (s2.advance.put 3 (word width endHeader)) = some s3
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.store 3 0) rfl (by omega)
      (by simpa [activeCode] using block 3 (by simp [activeCode]))]
    change (if h : (word width endHeader).val < firstHeap.size then
      some { s3.advance with heap := firstHeap.set (word width endHeader).val (word width directoryEnd) } else none) = some s4
    rw [endWord, dite_eq_left secondBound, advance_at _ _ _ _ _ _ _ _ (by omega)]
    simp only [s4, activeHeap, firstHeap, Array.setIfInBounds_def, dite_eq_left recordValid,
      Array.size_set, dite_eq_left endValid, Nat.add_assoc, atState]
  have first := Execution.cons t0 (Execution.cons t1 (Execution.refl s2))
  have later := Execution.cons t2 (Execution.cons t3 (Execution.refl s4))
  convert first.append later using 1 <;>
    simp only [s0, s1, s2, s3, s4, atState, State.liveWords, firstHeap,
      activeHeap_size, Array.size_setIfInBounds, Nat.max_self] <;> omega

/-- Header activation lies before directory and source cells, preserving the
complete actual source representation produced by optional row installation. -/
theorem stored_active {heap : Array (Word width)}
    (stored : Stored rows directory source heap)
    (recordHeader endHeader sourceEnd directoryEnd : ℕ)
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (recordBefore : recordHeader < directory) (endBefore : endHeader < directory)
    (directoryBefore : directory ≤ source) :
    Stored rows directory source (activeHeap heap recordHeader endHeader sourceEnd directoryEnd) := by
  have first : Stored rows directory source (heap.set recordHeader (word width sourceEnd) recordValid) := by
    refine ⟨by simpa using stored.fits, ?_, ?_⟩
    · intro index
      have original := stored.entry index
      exact ⟨Controller.Horn.RowScan.CursorStored.after_store original.1 recordHeader recordValid _ (by omega),
        Controller.Horn.RowScan.CursorStored.after_store original.2 recordHeader recordValid _ (by omega)⟩
    · intro index
      apply (stored.literals index).after_store recordHeader recordValid (word width sourceEnd)
      left; unfold sourceOffset; omega
  have secondBound : endHeader < (heap.set recordHeader (word width sourceEnd) recordValid).size := by simpa using endValid
  have second : Stored rows directory source
      ((heap.set recordHeader (word width sourceEnd) recordValid).set endHeader (word width directoryEnd) secondBound) := by
    refine ⟨by simpa using first.fits, ?_, ?_⟩
    · intro index
      have original := first.entry index
      exact ⟨Controller.Horn.RowScan.CursorStored.after_store original.1 endHeader secondBound _ (by omega),
        Controller.Horn.RowScan.CursorStored.after_store original.2 endHeader secondBound _ (by omega)⟩
    · intro index
      apply (first.literals index).after_store endHeader secondBound (word width directoryEnd)
      left; unfold sourceOffset; omega
  simpa only [activeHeap, Array.setIfInBounds_def, dite_eq_left recordValid,
    dite_eq_left secondBound] using second

/-- Both active endpoints are actual stored words; count is not read from the
mutable input cursor header. -/
theorem active_cells (heap : Array (Word width)) (recordHeader endHeader sourceEnd directoryEnd : ℕ)
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (different : recordHeader ≠ endHeader) :
    (activeHeap heap recordHeader endHeader sourceEnd directoryEnd)[recordHeader]? =
      some (word width sourceEnd) ∧
    (activeHeap heap recordHeader endHeader sourceEnd directoryEnd)[endHeader]? =
      some (word width directoryEnd) := by
  constructor
  · unfold activeHeap
    rw [Array.getElem?_setIfInBounds_ne different.symm,
      Array.getElem?_setIfInBounds_self_of_lt recordValid]
  · unfold activeHeap
    apply Array.getElem?_setIfInBounds_self_of_lt
    simpa only [Array.size_setIfInBounds] using endValid

/-- Complete representation after actual optional pair allocation, reserved
boundary stores and active-header stores. Every clause remains tied to cells. -/
theorem installed_positive_active (rows : List (Clause (Fin locals)))
    (last : Clause (Fin locals)) (labels : List ℕ) (heap : Array (Word width))
    (directory source recordHeader endHeader : ℕ) (old : Stored rows directory source heap)
    (sourceEnd : sourceOffset rows source rows.length = heap.size)
    (separation : directory + 2 * rows.length + 2 ≤ source)
    (reserved : directory + 2 * rows.length + 2 ≤ heap.size)
    (recordValid : recordHeader < heap.size) (endValid : endHeader < heap.size)
    (recordBefore : recordHeader < directory) (endBefore : endHeader < directory)
    (emitted : last.map (fun literal => (literal.1.val, literal.2)) =
      labels.map (fun localIndex => (localIndex, true))) :
    let pairs := ForestZeroPositive.pairHeap heap labels
    let installed := boundaryHeap pairs (directory + 2 * rows.length) heap.size pairs.size
    Stored (rows ++ [last]) directory source
      (activeHeap installed recordHeader endHeader pairs.size (directory + 2 * (rows.length + 1))) := by
  have actual := installed_positive_stored rows last labels heap directory source old sourceEnd separation reserved emitted
  apply stored_active actual recordHeader endHeader _ _
  · simp only [boundaryHeap_size, ForestZeroPositive.pairHeap_size]; omega
  · simp only [boundaryHeap_size, ForestZeroPositive.pairHeap_size]; omega
  · exact recordBefore
  · exact endBefore
  · omega

end Controller.Cost.ForestZeroAdmissible
