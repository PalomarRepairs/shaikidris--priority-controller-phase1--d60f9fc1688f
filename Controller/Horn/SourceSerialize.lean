module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.NormalizeCNF

@[expose] public section

/-! Original-input word encoding for the physical CNF normalizer. Five control
headers are followed by two boundary-pointer words per source clause, then two
words per original literal occurrence. Repeated literals remain repeated pairs.
No normalized rule or propagation bucket is serialized. -/
namespace Controller.Horn.SourceSerialize
open Controller.Cost Controller.Horn.SourceDirectory Controller.Horn.SourceScan
open Controller.Horn.Worklist.IndexedNormalize

/-- Original occurrences occupy label/polarity pairs in their supplied order. -/
def clauseWords (clause : Controller.CNF.Clause (Fin n)) : Array (Word width) :=
  Array.ofFn fun slot : Fin (2 * clause.length) =>
    let literal := clause[slot.val / 2]'(by have := slot.isLt; omega)
    if slot.val % 2 = 0 then word width literal.1.val
    else Controller.Horn.MarkStorage.encode width literal.2

@[simp] theorem clauseWords_size (clause : Controller.CNF.Clause (Fin n)) :
    (clauseWords (width := width) clause).size = 2 * clause.length := by simp [clauseWords]

def sourceWords : List (Controller.CNF.Clause (Fin n)) → Array (Word width)
  | [] => #[]
  | clause :: clauses => clauseWords clause ++ sourceWords clauses

@[simp] theorem sourceWords_size (clauses : List (Controller.CNF.Clause (Fin n))) :
    (sourceWords (width := width) clauses).size = 2 * (clauses.map List.length).sum := by
  induction clauses with
  | nil => simp [sourceWords]
  | cons clause clauses ih => simp [sourceWords, ih, Nat.mul_add]

theorem sourceWords_append (first rest : List (Controller.CNF.Clause (Fin n))) :
    sourceWords (width := width) (first ++ rest) = sourceWords first ++ sourceWords rest := by
  induction first with
  | nil => simp [sourceWords]
  | cons clause first ih => simp [sourceWords, ih, Array.append_assoc]

theorem sourceWords_slice (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Nat) (bound : index < clauses.length) :
    sourceWords (width := width) clauses = sourceWords (clauses.take index) ++
      (clauseWords clauses[index] ++ sourceWords (clauses.drop (index + 1))) := by
  calc
    sourceWords clauses = sourceWords (clauses.take index ++ clauses.drop index) :=
      congrArg sourceWords (List.take_append_drop index clauses).symm
    _ = _ := by rw [sourceWords_append, List.drop_eq_getElem_cons bound]; rfl

/-- Looking into one physical source row retains the complete original pair list. -/
theorem sourceWords_cell (clauses : List (Controller.CNF.Clause (Fin n)))
    (index position : Nat) (bound : index < clauses.length)
    (inside : position < 2 * clauses[index].length) :
    (sourceWords (width := width) clauses)[(sourceWords (width := width) (clauses.take index)).size + position]? =
      (clauseWords (width := width) clauses[index])[position]? := by
  rw [sourceWords_slice clauses index bound]
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact Array.getElem?_append_left (by simpa using inside)

theorem clauseWords_label (clause : Controller.CNF.Clause (Fin n)) (index : Fin clause.length) :
    (clauseWords (width := width) clause)[2 * index.val]? = some (word width clause[index.val].1.val) := by
  have bound : 2 * index.val < (clauseWords (width := width) clause).size := by
    rw [clauseWords_size]; have := index.isLt; omega
  rw [Array.getElem?_eq_getElem bound]
  have quotient : 2 * index.val / 2 = index.val := by omega
  have remainder : 2 * index.val % 2 = 0 := by omega
  simp [clauseWords, quotient, remainder]

theorem clauseWords_polarity (clause : Controller.CNF.Clause (Fin n)) (index : Fin clause.length) :
    (clauseWords (width := width) clause)[2 * index.val + 1]? =
      some (Controller.Horn.MarkStorage.encode width clause[index.val].2) := by
  have bound : 2 * index.val + 1 < (clauseWords (width := width) clause).size := by
    rw [clauseWords_size]; have := index.isLt; omega
  rw [Array.getElem?_eq_getElem bound]
  have quotient : (2 * index.val + 1) / 2 = index.val := by omega
  have remainder : (2 * index.val + 1) % 2 = 1 := by omega
  simp [clauseWords, quotient, remainder]

def directory : Nat := 5

def source (clauses : List (Controller.CNF.Clause (Fin n))) : Nat := 5 + 2 * clauses.length

def base (clauses : List (Controller.CNF.Clause (Fin n))) : Nat :=
  source clauses + 2 * (clauses.map List.length).sum

/-- Each directory pair contains its actual start/end offsets in the source data. -/
def directoryWords (clauses : List (Controller.CNF.Clause (Fin n))) : Array (Word width) :=
  Array.ofFn fun slot : Fin (2 * clauses.length) =>
    word width (sourceOffset clauses (source clauses) (slot.val / 2 + slot.val % 2))

@[simp] theorem directoryWords_size (clauses : List (Controller.CNF.Clause (Fin n))) :
    (directoryWords (width := width) clauses).size = 2 * clauses.length := by simp [directoryWords]

/-- Record pointer zero is overwritten by the actual initializer's register-seven
store. First/input pointers are source headers; directory/end pointers drive the loop. -/
def headers (clauses : List (Controller.CNF.Clause (Fin n))) : Array (Word width) :=
  #[word width 0, word width (source clauses), word width (source clauses),
    word width directory, word width (directory + 2 * clauses.length)]

@[simp] theorem headers_size (clauses : List (Controller.CNF.Clause (Fin n))) :
    (headers (width := width) clauses).size = 5 := rfl

def heap (clauses : List (Controller.CNF.Clause (Fin n))) : Array (Word width) :=
  headers clauses ++ (directoryWords clauses ++ sourceWords clauses)

@[simp] theorem heap_size (clauses : List (Controller.CNF.Clause (Fin n))) :
    (heap (width := width) clauses).size = base clauses := by
  simp [heap, base, source, Nat.add_assoc]

/-- All control headers precede the immutable input and the fresh scratch region. -/
def layout (clauses : List (Controller.CNF.Clause (Fin n))) : Layout clauses where
  directory := directory
  source := source clauses
  base := base clauses
  recordHeader := 0
  inputHeader := 1
  firstHeader := 2
  directoryHeader := 3
  endHeader := 4
  directoryBefore := by simp [directory, source]
  sourceBefore := by simp [sourceOffset, base]
  headersBefore := by
    intro header member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  headersDistinct := by decide

/-- Representation capacity is retained explicitly for source labels and pointers. -/
def Representable (width : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Prop :=
  n ≤ 2 ^ width ∧ base clauses < 2 ^ width

theorem label_value (literal : Controller.CNF.Literal (Fin n))
    (declared : n ≤ 2 ^ width) : (word width literal.1.val).val = literal.1.val :=
  Nat.mod_eq_of_lt (literal.1.isLt.trans_le declared)

theorem directoryWords_start (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Fin clauses.length) :
    (directoryWords (width := width) clauses)[2 * index.val]? =
      some (word width (sourceOffset clauses (source clauses) index.val)) := by
  have bound : 2 * index.val < (directoryWords (width := width) clauses).size := by
    rw [directoryWords_size]; have := index.isLt; omega
  rw [Array.getElem?_eq_getElem bound]
  have quotient : 2 * index.val / 2 = index.val := by omega
  have remainder : 2 * index.val % 2 = 0 := by omega
  simp [directoryWords, quotient, remainder]

theorem directoryWords_end (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Fin clauses.length) :
    (directoryWords (width := width) clauses)[2 * index.val + 1]? =
      some (word width (sourceOffset clauses (source clauses) (index.val + 1))) := by
  have bound : 2 * index.val + 1 < (directoryWords (width := width) clauses).size := by
    rw [directoryWords_size]; have := index.isLt; omega
  rw [Array.getElem?_eq_getElem bound]
  have quotient : (2 * index.val + 1) / 2 = index.val := by omega
  have remainder : (2 * index.val + 1) % 2 = 1 := by omega
  simp [directoryWords, quotient, remainder]

theorem heap_directory (clauses : List (Controller.CNF.Clause (Fin n))) (position : Nat)
    (inside : position < 2 * clauses.length) :
    (heap (width := width) clauses)[directory + position]? =
      (directoryWords (width := width) clauses)[position]? := by
  unfold heap
  rw [Array.getElem?_append_right (by simp [directory])]
  simp only [headers_size]
  have shifted : directory + position - 5 = position := by unfold directory; omega
  rw [shifted]
  exact Array.getElem?_append_left (by simpa using inside)

/-- This equality also holds at an out-of-range offset, preserving option-index frames. -/
theorem heap_source (clauses : List (Controller.CNF.Clause (Fin n))) (position : Nat) :
    (heap (width := width) clauses)[source clauses + position]? =
      (sourceWords (width := width) clauses)[position]? := by
  unfold heap
  rw [Array.getElem?_append_right (by simp only [headers_size]; unfold source; omega)]
  simp only [headers_size]
  have shifted : source clauses + position - 5 = 2 * clauses.length + position := by
    unfold source; omega
  rw [shifted, Array.getElem?_append_right (by simp)]
  simp only [directoryWords_size, Nat.add_sub_cancel_left]

theorem offset_prefix (clauses : List (Controller.CNF.Clause (Fin n))) (index : Nat) :
    sourceOffset clauses (source clauses) index = source clauses +
      (sourceWords (width := width) (clauses.take index)).size := by
  simp [sourceOffset]

/-- Every original source row is represented, including repeated literals. -/
theorem source_row_stored (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Fin clauses.length) :
    Controller.Horn.RowScan.SourceStored clauses[index.val]
      (sourceOffset clauses (source clauses) index.val) (heap (width := width) clauses) := by
  have splitSize := congrArg Array.size (sourceWords_slice (width := width) clauses index.val index.isLt)
  simp only [Array.size_append, clauseWords_size] at splitSize
  have prefixOffset := offset_prefix (width := width) clauses index.val
  have room : sourceOffset clauses (source clauses) index.val + 2 * clauses[index.val].length ≤
      (heap (width := width) clauses).size := by
    rw [prefixOffset, heap_size]
    unfold base
    rw [← sourceWords_size (width := width) clauses]
    omega
  refine ⟨room, ?_⟩
  intro occurrence
  have first : (heap (width := width) clauses)[sourceOffset clauses (source clauses) index.val +
      2 * occurrence.val]? = some (word width clauses[index.val][occurrence.val].1.val) := by
    rw [prefixOffset, Nat.add_assoc, heap_source,
      sourceWords_cell clauses index.val (2 * occurrence.val) index.isLt
        (by have := occurrence.isLt; omega)]
    exact clauseWords_label _ occurrence
  have second : (heap (width := width) clauses)[sourceOffset clauses (source clauses) index.val +
      2 * occurrence.val + 1]? = some (Controller.Horn.MarkStorage.encode width clauses[index.val][occurrence.val].2) := by
    rw [prefixOffset, Nat.add_assoc, Nat.add_assoc, heap_source,
      sourceWords_cell clauses index.val (2 * occurrence.val + 1) index.isLt
        (by have := occurrence.isLt; omega)]
    exact clauseWords_polarity _ occurrence
  refine ⟨by have := occurrence.isLt; omega, ?_, ?_⟩
  · simpa only [Array.getElem?_eq_getElem (show sourceOffset clauses (source clauses) index.val +
        2 * occurrence.val < (heap (width := width) clauses).size by have := occurrence.isLt; omega),
      Option.some.injEq] using first
  · simpa only [Array.getElem?_eq_getElem (show sourceOffset clauses (source clauses) index.val +
        2 * occurrence.val + 1 < (heap (width := width) clauses).size by have := occurrence.isLt; omega),
      Option.some.injEq] using second

/-- The original word encoding provides the complete physical source-directory contract. -/
theorem stored (clauses : List (Controller.CNF.Clause (Fin n))) :
    Stored clauses directory (source clauses) (heap (width := width) clauses) := by
  refine ⟨by simp only [heap_size]; unfold base source directory; omega, ?_, source_row_stored clauses⟩
  intro index
  have b0 : directory + 2 * index.val < (heap (width := width) clauses).size := by
    rw [heap_size]; unfold base source directory; have := index.isLt; omega
  have b1 : directory + 2 * index.val + 1 < (heap (width := width) clauses).size := by
    rw [heap_size]; unfold base source directory; have := index.isLt; omega
  refine ⟨⟨b0, ?_⟩, ⟨b1, ?_⟩⟩
  · have value := (heap_directory (width := width) clauses (2 * index.val)
        (by have := index.isLt; omega)).trans (directoryWords_start (width := width) clauses index)
    rw [Array.getElem?_eq_getElem b0] at value
    exact Option.some.inj value
  · have value := (heap_directory (width := width) clauses (2 * index.val + 1)
        (by have := index.isLt; omega)).trans (directoryWords_end (width := width) clauses index)
    have same : directory + (2 * index.val + 1) = directory + 2 * index.val + 1 := by omega
    rw [same, Array.getElem?_eq_getElem b1] at value
    exact Option.some.inj value

theorem header_value (clauses : List (Controller.CNF.Clause (Fin n))) (index : Fin 5) :
    (heap (width := width) clauses)[index.val]? = some (headers (width := width) clauses)[index.val] := by
  unfold heap
  rw [Array.getElem?_append_left (by simpa using index.isLt)]
  exact Array.getElem?_eq_getElem (by simpa using index.isLt)

/-- A loaded original-input heap and actual constant-register facts imply the
initial physical directory state. This does not assert a normalized record. -/
theorem input (clauses : List (Controller.CNF.Clause (Fin n))) (state : State width 8)
    (loaded : state.heap = heap clauses) (zero : state.reg 2 = word width 0)
    (one : state.reg 5 = word width 1) (decrement : state.reg 6 = word width (2 ^ width - 1))
    (running : state.halted = false) (capacity : Representable (width := width) clauses) :
    Controller.Horn.ClauseEntry.Input clauses (layout clauses) 0 state := by
  have directoryBound : 3 < state.heap.size := by rw [loaded, heap_size]; unfold base source; omega
  have endBound : 4 < state.heap.size := by rw [loaded, heap_size]; unfold base source; omega
  refine ⟨by simpa [loaded, layout] using stored (width := width) clauses,
    by omega, ⟨directoryBound, ?_⟩, ⟨endBound, ?_⟩, zero, one, decrement, running⟩
  · have value := header_value (width := width) clauses ⟨3, by decide⟩
    rw [← loaded, Array.getElem?_eq_getElem directoryBound] at value
    exact Option.some.inj (by simpa [layout, headers, directory] using value)
  · have value := header_value (width := width) clauses ⟨4, by decide⟩
    rw [← loaded, Array.getElem?_eq_getElem endBound] at value
    exact Option.some.inj (by simpa [layout, headers, directory] using value)

/-- Representable source pointers decode to the original natural offsets. -/
theorem offset_value (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Nat) (bound : index ≤ clauses.length)
    (capacity : Representable (width := width) clauses) :
    (word width (sourceOffset clauses (source clauses) index)).val =
      sourceOffset clauses (source clauses) index := by
  have endpoint := Controller.Horn.NormalizeCNF.sourceOffset_le_end clauses (source clauses) index
  have last : sourceOffset clauses (source clauses) clauses.length = base clauses := by
    simp [sourceOffset, base]
  have fits : base clauses < 2 ^ width := capacity.2
  exact Nat.mod_eq_of_lt (by rw [last] at endpoint; omega)

end Controller.Horn.SourceSerialize
