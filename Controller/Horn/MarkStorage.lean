module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexedNormalize
public import Controller.Horn.Initialize

@[expose] public section

/-!
# Indexed normalizer marks in machine storage

Every declared channel has two adjacent Boolean words, including channels
absent from all clauses. The representation relates heap entries directly to
`Marks.read`. Initialization uses the actual allocator execution. Cell reads,
writes and per-label clearing are fetched machine instructions; the normalizer's
list layout, traversal and complete control program are separate refinements.
-/

namespace Controller.Horn.MarkStorage

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

def encode (width : Nat) (value : Bool) : Word width :=
  word width (if value then 1 else 0)

theorem encode_zero_iff (capacity : 1 < 2 ^ width) (value : Bool) :
    (encode width value).val = 0 ↔ value = false := by
  cases value <;> simp [encode, word, Nat.mod_eq_of_lt, capacity]

/-- Positive then negative polarity occupy the two cells for each channel. -/
def address (offset : Nat) (literal : CNF.Literal (Fin n)) : Nat :=
  offset + (2 * literal.1.val + if literal.2 then 0 else 1)

theorem address_lt (offset : Nat) (literal : CNF.Literal (Fin n)) :
    address offset literal < offset + 2 * n := by
  have labelBound := literal.1.isLt
  cases polarity : literal.2 <;> simp only [address, polarity, Bool.false_eq_true, ite_false, ite_true]
    <;> omega

theorem address_injective (offset : Nat) :
    Function.Injective (address (n := n) offset) := by
  rintro ⟨left, sign⟩ ⟨right, otherSign⟩ equal
  cases sign <;> cases otherSign <;> simp only [address, Bool.false_eq_true, ite_false, ite_true] at equal
  all_goals first
    | have same : left.val = right.val := by omega
      have labels : left = right := Fin.ext same
      subst right
      rfl
    | omega

/-- A contiguous two-cell encoding of the accepted finite mark vector. -/
structure Stored (marks : Marks n) (offset : Nat) (heap : Array (Word width)) : Prop where
  fits : offset + 2 * n ≤ heap.size
  entry : ∀ literal : CNF.Literal (Fin n),
    heap[address offset literal]'(by have := address_lt offset literal; omega) =
      encode width (marks.read literal)

theorem Stored.bound {marks : Marks n} {offset : Nat} {heap : Array (Word width)}
    (stored : Stored marks offset heap) (literal : CNF.Literal (Fin n)) :
    address offset literal < heap.size :=
  (address_lt offset literal).trans_le stored.fits

/-- Writing one polarity leaves the other polarity and all other labels intact. -/
def write (marks : Marks n) (literal : CNF.Literal (Fin n)) (value : Bool) : Marks n :=
  let old := marks[literal.1.val]
  marks.set literal.1.val
    (if literal.2 then (value, old.2) else (old.1, value)) literal.1.isLt

theorem read_write (marks : Marks n) (literal query : CNF.Literal (Fin n)) (value : Bool) :
    (write marks literal value).read query =
      if query = literal then value else marks.read query := by
  rcases literal with ⟨label, polarity⟩
  rcases query with ⟨other, sign⟩
  by_cases equal : label = other
  · subst other
    cases polarity <;> cases sign <;> simp [write, Marks.read]
  · have unequal : label.val ≠ other.val := fun same => equal (Fin.ext same)
    cases polarity <;> cases sign <;> simp [write, Marks.read, unequal, Ne.symm equal]

theorem record_marks (row : Row n) (literal : CNF.Literal (Fin n)) :
    (row.record literal).marks = write row.marks literal true := rfl

theorem Stored.write {marks : Marks n} {offset : Nat} {heap : Array (Word width)}
    (stored : Stored marks offset heap) (literal : CNF.Literal (Fin n)) (value : Bool) :
    Stored (write marks literal value) offset
      (heap.set (address offset literal) (encode width value) (stored.bound literal)) := by
  refine ⟨by simpa only [Array.size_set] using stored.fits, ?_⟩
  intro query
  rw [read_write]
  by_cases equal : query = literal
  · subst query
    simp
  · have different : address offset literal ≠ address offset query := by
      intro same
      exact equal ((address_injective offset same).symm)
    rw [Array.getElem_set_ne (stored.bound literal) (stored.bound query) different, ite_eq_right equal]
    exact stored.entry query

/-- A cell update preserves every address outside the entire mark region. -/
theorem store_preserves_outside {marks : Marks n} {offset : Nat} {heap : Array (Word width)}
    (stored : Stored marks offset heap) (literal : CNF.Literal (Fin n)) (value : Bool)
    (index : Fin heap.size) (outside : index.val < offset ∨ offset + 2 * n ≤ index.val) :
    (heap.set (address offset literal) (encode width value) (stored.bound literal))[index.val]'(by simp) =
      heap[index.val] := by
  have lower : offset ≤ address offset literal := by unfold address; omega
  have upper := address_lt offset literal
  have different : address offset literal ≠ index.val := by omega
  simp [different]

/-- The allocated zero region represents all ambient marks, also when `n = 0`. -/
theorem initial_stored (heap : Array (Word width)) (n : Nat) :
    Stored (Marks.initial n) heap.size
      (heap ++ Array.replicate (2 * n) (word width 0)) := by
  refine ⟨by simp, ?_⟩
  intro literal
  cases polarity : literal.2 <;>
    simp [address, encode, Marks.read, Marks.initial, polarity]

/-- The same-program allocator creates the actual table before handing control
to instruction 4. No clause is scanned and no assignment is precomputed. -/
theorem initialize_marks (destination : Program width 3)
    (agreement : Initialize.LoopAgreement destination) (heap : Array (Word width)) (n : Nat)
    (capacity : 5 < 2 ^ width) (fits : heap.size + 2 * n < 2 ^ width) :
    Execution destination (Initialize.configuration heap (2 * n) 0)
      (Initialize.configuration (heap ++ Array.replicate (2 * n) (word width 0)) 0 4)
      (8 * n + 1) ((Initialize.configuration heap (2 * n) 0).liveWords + 2 * n) ∧
    Stored (Marks.initial n) heap.size
      (Initialize.configuration (heap ++ Array.replicate (2 * n) (word width 0)) 0 4).heap := by
  constructor
  · simpa only [← Nat.mul_assoc, Nat.reduceMul] using
      Initialize.loop_execution destination agreement heap (2 * n) capacity fits
  · exact initial_stored heap n

/-- A fetched read returns the represented sign mark and leaves the table intact. -/
theorem load_mark (program : Program width registers) (state : State width registers)
    (marks : Marks n) (offset : Nat) (stored : Stored marks offset state.heap)
    (literal : CNF.Literal (Fin n)) (destination addressRegister : Fin registers)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.load destination addressRegister))
    (points : (state.reg addressRegister).val = address offset literal) :
    programStep program state =
      some (state.advance.put destination (encode width (marks.read literal))) := by
  have valid : (state.reg addressRegister).val < state.heap.size := by
    rw [points]
    exact stored.bound literal
  unfold programStep
  rw [fetched]
  change step (.load destination addressRegister) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, valid, dite_eq_left]
  have read : state.heap[(state.reg addressRegister).val] = encode width (marks.read literal) := by
    simpa only [points] using stored.entry literal
  rw [read]

theorem load_mark_execution (program : Program width registers) (state : State width registers)
    (marks : Marks n) (offset : Nat) (stored : Stored marks offset state.heap)
    (literal : CNF.Literal (Fin n)) (destination addressRegister : Fin registers)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.load destination addressRegister))
    (points : (state.reg addressRegister).val = address offset literal) :
    Execution program state
      (state.advance.put destination (encode width (marks.read literal))) 1 state.liveWords ∧
    Stored marks offset (state.advance.put destination (encode width (marks.read literal))).heap := by
  constructor
  · have trace := Execution.cons
      (load_mark program state marks offset stored literal destination addressRegister running fetched points)
      (Execution.refl (state.advance.put destination (encode width (marks.read literal))))
    simpa [State.liveWords, State.advance, State.put] using trace
  · exact stored

theorem store_mark (program : Program width registers) (state : State width registers)
    (marks : Marks n) (offset : Nat) (stored : Stored marks offset state.heap)
    (literal : CNF.Literal (Fin n)) (value : Bool) (addressRegister source : Fin registers)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.store addressRegister source))
    (points : (state.reg addressRegister).val = address offset literal)
    (held : state.reg source = encode width value) :
    programStep program state =
      some { state.advance with
        heap := state.heap.set (address offset literal) (encode width value) (stored.bound literal) } := by
  have valid : (state.reg addressRegister).val < state.heap.size := by
    rw [points]
    exact stored.bound literal
  unfold programStep
  rw [fetched]
  change step (.store addressRegister source) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, valid, dite_eq_left, held]
  simp only [points]

/-- Updating a mark is one actual store, with the unchanged heap size and the
new mark vector related to the resulting heap. -/
theorem store_mark_execution (program : Program width registers) (state : State width registers)
    (marks : Marks n) (offset : Nat) (stored : Stored marks offset state.heap)
    (literal : CNF.Literal (Fin n)) (value : Bool) (addressRegister source : Fin registers)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.store addressRegister source))
    (points : (state.reg addressRegister).val = address offset literal)
    (held : state.reg source = encode width value) :
    Execution program state
      { state.advance with
        heap := state.heap.set (address offset literal) (encode width value) (stored.bound literal) }
      1 state.liveWords ∧
    Stored (write marks literal value) offset
      (state.heap.set (address offset literal) (encode width value) (stored.bound literal)) := by
  constructor
  · have transition := store_mark program state marks offset stored literal value addressRegister source
      running fetched points held
    have trace := Execution.cons transition
      (Execution.refl { state.advance with
        heap := state.heap.set (address offset literal) (encode width value) (stored.bound literal) })
    simpa [State.liveWords, State.advance] using trace
  · exact stored.write literal value

/-- The store refines the mark component of `Row.record`; scratch-list and
tautology-control instructions are not included in this fragment. -/
theorem record_marks_execution (program : Program width registers) (state : State width registers)
    (row : Row n) (offset : Nat) (stored : Stored row.marks offset state.heap)
    (literal : CNF.Literal (Fin n)) (addressRegister source : Fin registers)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.store addressRegister source))
    (points : (state.reg addressRegister).val = address offset literal)
    (held : state.reg source = encode width true) :
    Execution program state
      { state.advance with
        heap := state.heap.set (address offset literal) (encode width true) (stored.bound literal) }
      1 state.liveWords ∧
    Stored (row.record literal).marks offset
      (state.heap.set (address offset literal) (encode width true) (stored.bound literal)) := by
  simpa only [record_marks] using store_mark_execution program state row.marks offset stored
    literal true addressRegister source running fetched points held

theorem write_pair_false (marks : Marks n) (label : Fin n) :
    write (write marks (label, true) false) (label, false) false =
      marks.set label.val (false, false) label.isLt := by
  apply Vector.ext
  intro index within
  by_cases same : label.val = index
  · subst index
    simp [write]
  · simp [write, same]

/-- Clearing one touched label executes two fetched stores. Register values,
stack and output are preserved; the caller supplies the two actual addresses.
The traversal that obtains successive touched labels is a separate block. -/
theorem clear_label_execution (program : Program width registers) (state : State width registers)
    (marks : Marks n) (offset : Nat) (stored : Stored marks offset state.heap)
    (label : Fin n) (positiveAddress negativeAddress zeroRegister : Fin registers)
    (running : state.halted = false)
    (first : program[state.pc.val]? = some (.store positiveAddress zeroRegister))
    (second : program[state.advance.pc.val]? = some (.store negativeAddress zeroRegister))
    (positivePoints : (state.reg positiveAddress).val = address offset (label, true))
    (negativePoints : (state.reg negativeAddress).val = address offset (label, false))
    (zeroHeld : state.reg zeroRegister = encode width false) :
    ∃ next : State width registers, Execution program state next 2 state.liveWords ∧
      Stored (Marks.clear [label] marks) offset next.heap ∧
      next.reg = state.reg ∧ next.stack = state.stack ∧ next.output = state.output ∧
      next.pc = state.advance.advance.pc ∧ next.halted = false := by
  let middle : State width registers :=
    { state.advance with
      heap := state.heap.set (address offset (label, true)) (encode width false) (stored.bound (label, true)) }
  have firstResult := store_mark_execution program state marks offset stored (label, true) false
    positiveAddress zeroRegister running first positivePoints zeroHeld
  have firstTrace : Execution program state middle 1 state.liveWords := firstResult.1
  have middleStored : Stored (write marks (label, true) false) offset middle.heap := firstResult.2
  have middleRunning : middle.halted = false := by simpa [middle, State.advance] using running
  have middleFetched : program[middle.pc.val]? = some (.store negativeAddress zeroRegister) := second
  have middlePoints : (middle.reg negativeAddress).val = address offset (label, false) := negativePoints
  have middleHeld : middle.reg zeroRegister = encode width false := zeroHeld
  let next : State width registers :=
    { middle.advance with
      heap := middle.heap.set (address offset (label, false)) (encode width false) (middleStored.bound (label, false)) }
  have secondResult := store_mark_execution program middle (write marks (label, true) false)
    offset middleStored (label, false) false negativeAddress zeroRegister middleRunning middleFetched
    middlePoints middleHeld
  have secondTrace : Execution program middle next 1 middle.liveWords := secondResult.1
  have middleWords : middle.liveWords = state.liveWords := by
    simp [middle, State.liveWords, State.advance]
  refine ⟨next, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simpa only [middleWords, Nat.max_self, Nat.reduceAdd] using firstTrace.append secondTrace
  · simpa only [write_pair_false, Marks.clear] using secondResult.2
  · simpa [next, middle, State.advance] using running

end Controller.Horn.MarkStorage
