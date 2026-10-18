module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexScan

@[expose] public section

/-! The fetched incidence-index loop consumes the physical immutable row bodies.
The body iteration includes its endpoint test, allocation, and return branch on
one program. Ghost occurrences specify the produced links; they are not machine
inputs or an uncharged index table. -/
namespace Controller.Horn.IndexScanLoop
open Controller.Cost Controller.Horn.WorklistStorage
variable {width n : Nat}

@[simp] theorem test_heap (state : State width 8) (header pointer limit exit : Nat) :
    (IndexScan.testFinished state header pointer limit exit).heap = state.heap := by
  unfold IndexScan.testFinished Controller.Horn.RuleDispatch.branchFinished
  split <;> rfl

@[simp] theorem test_stack (state : State width 8) (header pointer limit exit : Nat) :
    (IndexScan.testFinished state header pointer limit exit).stack = state.stack := by
  unfold IndexScan.testFinished Controller.Horn.RuleDispatch.branchFinished
  split <;> rfl

@[simp] theorem test_output (state : State width 8) (header pointer limit exit : Nat) :
    (IndexScan.testFinished state header pointer limit exit).output = state.output := by
  unfold IndexScan.testFinished Controller.Horn.RuleDispatch.branchFinished
  split <;> rfl

@[simp] theorem test_halted (state : State width 8) (header pointer limit exit : Nat) :
    (IndexScan.testFinished state header pointer limit exit).halted = state.halted := by
  unfold IndexScan.testFinished Controller.Horn.RuleDispatch.branchFinished
  split <;> rfl

@[simp] theorem test_live (state : State width 8) (header pointer limit exit : Nat) :
    (IndexScan.testFinished state header pointer limit exit).liveWords = state.liveWords := by
  simp [State.liveWords]

theorem test_reg (state : State width 8) (header pointer limit exit : Nat) (register : Fin 8)
    (notThree : register ≠ 3) (notFour : register ≠ 4) :
    (IndexScan.testFinished state header pointer limit exit).reg register = state.reg register := by
  unfold IndexScan.testFinished Controller.Horn.RuleDispatch.branchFinished
  split <;> simp [IndexScan.testCompared, State.advance, State.put, notThree, notFour]

/-- Both endpoint tests are read from the same stored 32-instruction region. -/
theorem body_test_at (program : Program width 8) (entry base recordStart : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart) :
    IndexScan.TestAt program (entry + 14) (base + 2 * n) (entry + 30) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code] using present ⟨14, by decide⟩
  · simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code, Nat.add_assoc] using present ⟨15, by decide⟩
  · simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code, Nat.add_assoc] using present ⟨16, by decide⟩
  · simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code, Nat.add_assoc] using present ⟨17, by decide⟩

theorem outer_test_at (program : Program width 8) (entry base recordStart : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart) :
    IndexScan.TestAt program (entry + 2) 0 (entry + 32) 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code] using present ⟨2, by decide⟩
  · simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code, Nat.add_assoc] using present ⟨3, by decide⟩
  · simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code, Nat.add_assoc] using present ⟨4, by decide⟩
  · simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code, Nat.add_assoc] using present ⟨5, by decide⟩

theorem body_return_at (program : Program width 8) (entry base recordStart : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart) :
    program[entry + 29]? = some (.branchZero 2 (word width (entry + 14))) := by
  simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code] using present ⟨29, by decide⟩

/-- This endpoint is the literal state produced by the three executed stages,
so no caller frame or register reconstruction is supplied as a premise. -/
def bodyFinished (state : State width 8) (entry base pointer limit row previous : Nat)
    (label : Fin n) (headBound : headAddress base label < state.heap.size) : State width 8 :=
  let tested := IndexScan.testFinished state (base + 2 * n) pointer limit (entry + 30)
  let inserted := IndexBuild.finished tested (entry + 18) base pointer row previous label
    (by simpa [tested] using headBound)
  Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)

/-- Every positive source occurrence incurs four fetched test instructions,
eleven fetched incidence instructions, and one fetched return instruction.
The count and endpoint are read from the physical row/header, not preloaded
from a semantic remaining-incidence count. -/
theorem body_execution (program : Program width 8) (entry base recordStart pointer limit row previous : Nat)
    (state : State width 8) (label : Fin n)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (position : state.pc = word width (entry + 14)) (running : state.halted = false)
    (headerBound : base + 2 * n < state.heap.size)
    (endpointCell : state.heap[base + 2 * n]'headerBound = word width limit)
    (bodyBound : pointer < state.heap.size) (headBound : headAddress base label < state.heap.size)
    (source : state.heap[pointer]'bodyBound = word width label.val)
    (head : state.heap[headAddress base label]'headBound = word width previous)
    (previousBound : previous < state.heap.size) (rowBound : row < state.heap.size)
    (sourceHeld : state.reg 0 = word width pointer) (rowHeld : state.reg 1 = word width row)
    (allocationHeld : state.reg 7 = word width state.heap.size)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (remaining : pointer < limit) (limitFits : limit < 2 ^ width)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width) :
    Execution program state (bodyFinished state entry base pointer limit row previous label headBound)
      16 (state.liveWords + 2) := by
  let tested := IndexScan.testFinished state (base + 2 * n) pointer limit (entry + 30)
  have testTrace := IndexScan.test_execution program (entry + 14) (base + 2 * n) pointer limit (entry + 30)
    0 state (body_test_at program entry base recordStart present) position running
    headerBound endpointCell sourceHeld (by decide) (by decide) (by omega) (by omega)
    (by omega) limitFits
  have testedPosition : tested.pc = word width (entry + 18) := by
    have result := IndexScan.test_position state (entry + 14) (base + 2 * n) pointer limit (entry + 30)
      position (by omega) (by omega) limitFits
    simpa [tested, Nat.ne_of_lt remaining, Nat.add_assoc] using result
  have testedHead : headAddress base label < tested.heap.size := by simpa [tested] using headBound
  let inserted := IndexBuild.finished tested (entry + 18) base pointer row previous label testedHead
  have insertion := IndexBuild.incidence_execution program (entry + 18) base pointer row previous tested label
    (IndexScan.kernel_at program entry base recordStart present)
    (by simpa [tested] using bodyBound) testedHead
    (by simpa [tested] using source) (by simpa [tested] using head)
    (by simpa [tested] using previousBound) (by simpa [tested] using rowBound)
    (by simpa [tested, test_reg state _ _ _ _ 0 (by decide) (by decide)] using sourceHeld)
    (by simpa [tested, test_reg state _ _ _ _ 1 (by decide) (by decide)] using rowHeld)
    (by simpa [tested, test_reg state _ _ _ _ 7 (by decide) (by decide)] using allocationHeld)
    (by simpa [tested, test_reg state _ _ _ _ 5 (by decide) (by decide)] using one)
    testedPosition (by simpa [tested] using running) (by omega) (by simpa [tested] using room)
  have insertedPosition : inserted.pc = word width (entry + 29) := by
    simp [inserted, IndexBuild.finished, Nat.add_assoc]
  have returnTrace := Controller.Horn.RuleDispatch.branch_execution program (entry + 29) (entry + 14) 2
    (body_return_at program entry base recordStart present) inserted insertedPosition
    (by simp [inserted, IndexBuild.finished]) (by omega)
  have combined := testTrace.append (insertion.append returnTrace)
  convert combined using 1
  · rfl
  · simp [State.liveWords, tested, inserted, IndexBuild.finished, IndexBuild.linkedHeap] <;> omega

/-- The actual zero register forces the fetched return branch back to the
body test; this fact is separate from merely executing the branch instruction. -/
theorem body_position (state : State width 8) (entry base pointer limit row previous : Nat)
    (label : Fin n) (headBound : headAddress base label < state.heap.size)
    (zero : state.reg 2 = word width 0) :
    (bodyFinished state entry base pointer limit row previous label headBound).pc = word width (entry + 14) := by
  let tested := IndexScan.testFinished state (base + 2 * n) pointer limit (entry + 30)
  let inserted := IndexBuild.finished tested (entry + 18) base pointer row previous label
    (by simpa [tested] using headBound)
  have held : inserted.reg 2 = word width 0 := by
    simpa [inserted, IndexBuild.finished, tested,
      test_reg state _ _ _ _ 2 (by decide) (by decide)] using zero
  have isZero : (inserted.reg 2).val = 0 := by rw [held]; simp [word]
  change (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).pc = _
  unfold Controller.Horn.RuleDispatch.branchFinished
  rw [ite_eq_left isZero]

/-- Caller storage, cursor progression, and register constants follow from the
literal executed endpoint. No desired terminal register file is assumed. -/
theorem body_frame (state : State width 8) (entry base pointer limit row previous : Nat)
    (label : Fin n) (headBound : headAddress base label < state.heap.size) :
    let final := bodyFinished state entry base pointer limit row previous label headBound
    final.heap.size = state.heap.size + 2 ∧
    final.reg 0 = word width (pointer + 1) ∧
    final.reg 7 = word width (state.heap.size + 2) ∧
    final.reg 1 = state.reg 1 ∧ final.reg 2 = state.reg 2 ∧ final.reg 5 = state.reg 5 ∧
    final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false := by
  dsimp only
  let tested := IndexScan.testFinished state (base + 2 * n) pointer limit (entry + 30)
  let inserted := IndexBuild.finished tested (entry + 18) base pointer row previous label
    (by simpa [tested] using headBound)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame inserted 2 (entry + 14)
  change (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).heap.size = _ ∧
    (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).reg 0 = _ ∧
    (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).reg 7 = _ ∧
    (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).reg 1 = _ ∧
    (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).reg 2 = _ ∧
    (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).reg 5 = _ ∧
    (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).stack = _ ∧
    (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).output = _ ∧
    (Controller.Horn.RuleDispatch.branchFinished inserted 2 (entry + 14)).halted = _
  simp only [frame.1, frame.2.1, frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1]
  simp [inserted, IndexBuild.finished, IndexBuild.linkedHeap, tested,
    test_reg state _ _ _ _ 1 (by decide) (by decide),
    test_reg state _ _ _ _ 2 (by decide) (by decide),
    test_reg state _ _ _ _ 5 (by decide) (by decide)]

theorem body_heap (state : State width 8) (entry base pointer limit row previous : Nat)
    (label : Fin n) (headBound : headAddress base label < state.heap.size) :
    (bodyFinished state entry base pointer limit row previous label headBound).heap =
      IndexBuild.linkedHeap state base label row previous headBound := by
  dsimp only [bodyFinished]
  rw [(Controller.Horn.RuleDispatch.branchFinished_frame _ _ _).2.1]
  dsimp only [IndexBuild.finished]
  simp only [IndexBuild.linkedHeap, test_heap]

/-- All bucket pointers are physically present and decode to nil or allocated
storage. This validity invariant is maintained before any rule count mutates. -/
structure BucketsValid (base : Nat) (heap : Array (Word width)) : Prop where
  bound : ∀ label : Fin n, headAddress base label < heap.size
  pointer : ∀ label : Fin n, (heap[headAddress base label]'(bound label)).val < heap.size

/-- The full original-occurrence invariant entails pointer validity, including
strictly positive allocated node addresses and the nil-zero alternative. -/
theorem buckets_of_index (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base processed : Nat) (heap : Array (Word width))
    (index : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed heap)
    (room : heap.size < 2 ^ width) : BucketsValid (n := n) base heap := by
  have prefixLength : ((IndexScan.occurrences clauses recordStart).take processed).length = processed :=
    List.length_take_of_le index.prefixBound
  have bound (label : Fin n) : headAddress base label < heap.size := by
    have isLabel := label.isLt
    have lower := index.separation
    have endpoint := index.endpoint
    have ending := index.originalEnd
    unfold Controller.Horn.NormalizeLoop.recordOffset at ending
    unfold headAddress
    omega
  refine ⟨bound, ?_⟩
  intro label
  have value := index.headValues label
  rw [Array.getElem?_eq_getElem (bound label)] at value
  have exactCell := Option.some.inj value
  have below := IndexScan.heads_bound recordEnd index.positiveEnd
    ((IndexScan.occurrences clauses recordStart).take processed) label
  rw [prefixLength, ← index.endpoint] at below
  rw [exactCell]
  exact (Nat.mod_eq_of_lt (by omega)).trans_lt below

/-- Allocating a new incidence changes one bucket head to the old allocation
end and leaves all other decoded pointers valid. -/
theorem buckets_after (state : State width 8) (base row previous : Nat) (label : Fin n)
    (buckets : BucketsValid (n := n) base state.heap)
    (room : state.heap.size + 2 < 2 ^ width) :
    BucketsValid (n := n) base
      (IndexBuild.linkedHeap state base label row previous (buckets.bound label)) := by
  have growth : (IndexBuild.linkedHeap state base label row previous (buckets.bound label)).size =
      state.heap.size + 2 := by simp [IndexBuild.linkedHeap]
  refine ⟨fun query => by have := buckets.bound query; omega, ?_⟩
  intro query
  by_cases same : query = label
  · subst query
    simp only [IndexBuild.linkedHeap, Array.getElem_set_self]
    change state.heap.size % 2 ^ width < _
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [Array.size_set, Array.size_push]
    omega
  · have different : headAddress base label ≠ headAddress base query := by
      intro equal
      apply same
      apply Fin.ext
      unfold headAddress at equal
      omega
    have frame := IndexBuild.incidence_old_frame state base row previous label (buckets.bound label)
      (headAddress base query) (buckets.bound query) different
    rw [Array.getElem?_eq_getElem (by have := buckets.bound query; omega),
      Array.getElem?_eq_getElem (buckets.bound query)] at frame
    rw [Option.some.inj frame]
    have pointerBound := buckets.pointer query
    omega

/-- A physical source suffix is framed through the bucket insertion because
all its cells lie above the scratch bucket region. -/
theorem labels_frame (labels : List (Fin n)) (offset base row previous : Nat)
    (state : State width 8) (label : Fin n)
    (stored : Controller.Horn.ResetTouched.LabelsStored labels offset state.heap)
    (headBound : headAddress base label < state.heap.size)
    (separation : headAddress base label < offset) :
    Controller.Horn.ResetTouched.LabelsStored labels offset
      (IndexBuild.linkedHeap state base label row previous headBound) := by
  refine ⟨by have := stored.fits; simp only [IndexBuild.linkedHeap, Array.size_set, Array.size_push]; omega, ?_⟩
  intro index
  have inside : offset + index.val < state.heap.size := by
    have := stored.fits
    have := index.isLt
    omega
  have frame := IndexBuild.incidence_old_frame state base row previous label headBound
    (offset + index.val) inside (by omega)
  rw [Array.getElem?_eq_getElem (by simp [IndexBuild.linkedHeap]; omega),
    Array.getElem?_eq_getElem inside] at frame
  exact (Option.some.inj frame).trans (stored.entry index)

/-- The saved endpoint header is outside every channel bucket and remains a
physically stored word during all incidence insertions. -/
theorem endpoint_frame (state : State width 8) (base row previous endpoint : Nat)
    (label : Fin n) (headBound : headAddress base label < state.heap.size)
    (stored : Controller.Horn.SourceScan.CursorStored endpoint (base + 2 * n) state.heap) :
    Controller.Horn.SourceScan.CursorStored endpoint (base + 2 * n)
      (IndexBuild.linkedHeap state base label row previous headBound) := by
  have different : headAddress base label ≠ base + 2 * n := by
    have := label.isLt
    unfold headAddress
    omega
  have frame := IndexBuild.incidence_old_frame state base row previous label headBound
    (base + 2 * n) stored.bound different
  refine ⟨by have := stored.bound; simp [IndexBuild.linkedHeap]; omega, ?_⟩
  rw [Array.getElem?_eq_getElem (by have := stored.bound; simp [IndexBuild.linkedHeap]; omega),
    Array.getElem?_eq_getElem stored.bound] at frame
  exact (Option.some.inj frame).trans stored.value

/-- Existing link nodes are preserved by a frame on their actual two cells. -/
theorem node_frame (row previous offset : Nat) (before after : Array (Word width))
    (stored : NodeStored row previous offset before)
    (growth : before.size ≤ after.size)
    (frame : ∀ position, offset ≤ position → position < before.size →
      after[position]? = before[position]?) : NodeStored row previous offset after := by
  have cell (position : Nat) (above : offset ≤ position) (inside : position < before.size) :
      after[position]'(by omega) = before[position]'inside := by
    have exactCell := frame position above inside
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem inside] at exactCell
    exact Option.some.inj exactCell
  refine ⟨by have := stored.fits; omega, stored.rowFits, stored.previousFits, stored.offsetFits, ?_, ?_⟩
  · exact (cell offset (by omega) (by have := stored.fits; omega)).trans stored.row
  · exact (cell (offset + 1) (by omega) (by have := stored.fits; omega)).trans stored.next

/-- Appending one physically allocated node extends the exact original-source
index prefix. Bucket heads, older nodes, and every original immutable row are
proved from the insertion heap, not supplied as a completed index premise. -/
theorem index_after (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base processed row : Nat) (state : State width 8) (label : Fin n)
    (index : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed state.heap)
    (available : processed < (IndexScan.occurrences clauses recordStart).length)
    (sourceOccurrence : (IndexScan.occurrences clauses recordStart)[processed]'available = (row, label))
    (room : state.heap.size + 2 < 2 ^ width) :
    let buckets := buckets_of_index clauses recordStart recordEnd base processed state.heap index (by omega)
    IndexScan.PhysicalIndex clauses recordStart recordEnd base (processed + 1)
      (IndexBuild.linkedHeap state base label row
        (IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take processed) label)
        (buckets.bound label)) := by
  dsimp only
  let buckets := buckets_of_index clauses recordStart recordEnd base processed state.heap index (by omega)
  let previous := IndexScan.heads recordEnd ((IndexScan.occurrences clauses recordStart).take processed) label
  let finalHeap := IndexBuild.linkedHeap state base label row previous (buckets.bound label)
  have prefixLength : ((IndexScan.occurrences clauses recordStart).take processed).length = processed :=
    List.length_take_of_le index.prefixBound
  have takeNext : (IndexScan.occurrences clauses recordStart).take (processed + 1) =
      (IndexScan.occurrences clauses recordStart).take processed ++ [(row, label)] := by
    rw [List.take_succ_eq_append_getElem available, sourceOccurrence]
  have recordsBelow : recordStart ≤ recordEnd := by
    have ending := index.originalEnd
    unfold Controller.Horn.NormalizeLoop.recordOffset at ending
    omega
  have bucketBelow (query : Fin n) : headAddress base query < recordStart := by
    have := query.isLt
    have := index.separation
    unfold headAddress
    omega
  have growth : finalHeap.size = state.heap.size + 2 := by simp [finalHeap, IndexBuild.linkedHeap]
  have occurrenceMember : (row, label) ∈ IndexScan.occurrences clauses recordStart := by
    rw [← sourceOccurrence]
    exact List.getElem_mem available
  have rowBound : row < state.heap.size := by
    have original := IndexScan.occurrence_row_bound clauses recordStart row label occurrenceMember
    rw [← index.originalEnd] at original
    have endpoint := index.endpoint
    omega
  have previousBound : previous < state.heap.size := by
    have bound := IndexScan.heads_bound recordEnd index.positiveEnd ((IndexScan.occurrences clauses recordStart).take processed)
      label
    rw [prefixLength, ← index.endpoint] at bound
    exact bound
  refine ⟨by omega, by rw [growth, index.endpoint]; omega, ?_, ?_, ?_,
    index.originalEnd, index.separation, index.positiveEnd⟩
  · intro query
    rw [takeNext, IndexScan.heads_append recordEnd index.positiveEnd _ row label query, prefixLength]
    by_cases same : query = label
    · subst query
      rw [ite_eq_left rfl]
      rw [Array.getElem?_eq_getElem (by simpa only [IndexBuild.linkedHeap, Array.size_set, Array.size_push] using
        (show headAddress base label < state.heap.size + 1 + 1 by have := buckets.bound label; omega))]
      apply congrArg some
      simp [finalHeap, IndexBuild.linkedHeap, index.endpoint]
    · rw [ite_eq_right same]
      have different : headAddress base label ≠ headAddress base query := by
        intro equal
        apply same
        apply Fin.ext
        unfold headAddress at equal
        omega
      exact (IndexBuild.incidence_old_frame state base row previous label (buckets.bound label)
        (headAddress base query) (buckets.bound query) different).trans (index.headValues query)
  · intro node
    by_cases earlier : node.val < processed
    · have stored := index.nodes ⟨node.val, earlier⟩
      apply node_frame _ _ _ state.heap finalHeap stored (by omega)
      intro position above inside
      exact IndexBuild.incidence_old_frame state base row previous label (buckets.bound label)
        position inside (by have := bucketBelow label; omega)
    · have last : node.val = processed := by have := node.isLt; omega
      have actual := (IndexBuild.incidence_node state base row previous label (buckets.bound label)
        rowBound previousBound room).1
      simpa only [last, sourceOccurrence, Prod.fst, Prod.snd, previous, index.endpoint] using actual
  · intro original
    have stored := index.records original
    apply IndexScan.record_frame _ _ state.heap finalHeap stored (by omega)
    intro position above inside
    have originalAbove : recordStart ≤ Controller.Horn.NormalizeLoop.recordOffset clauses recordStart original.val := by
      unfold Controller.Horn.NormalizeLoop.recordOffset
      omega
    exact IndexBuild.incidence_old_frame state base row previous label (buckets.bound label)
      position inside (by have := bucketBelow label; omega)

/-- The body exit preserves the caller and the row/allocation registers needed
by the outer loop. Its heap contains the two-word links actually allocated. -/
structure BodyResult (before after : State width 8) (entry limit count : Nat) (base : Nat) : Prop where
  position : after.pc = word width (entry + 30)
  sourceHeld : after.reg 0 = word width limit
  rowHeld : after.reg 1 = before.reg 1
  allocationHeld : after.reg 7 = word width after.heap.size
  zero : after.reg 2 = before.reg 2
  one : after.reg 5 = before.reg 5
  growth : after.heap.size = before.heap.size + 2 * count
  stack : after.stack = before.stack
  output : after.output = before.output
  running : after.halted = false
  buckets : BucketsValid (n := n) base after.heap

/-- The body cursor consumes the actual physically stored suffix. This is an
induction over its source words on the same fetched program, including the
final four-instruction endpoint test. It performs no semantic list lookup. -/
theorem body_suffix_execution (program : Program width 8) (entry base recordStart row limit : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (capacity : entry + 32 < 2 ^ width) (limitFits : limit < 2 ^ width)
    (labels : List (Fin n)) (pointer : Nat) (state : State width 8)
    (stored : Controller.Horn.ResetTouched.LabelsStored labels pointer state.heap)
    (buckets : BucketsValid (n := n) base state.heap)
    (endpoint : Controller.Horn.SourceScan.CursorStored limit (base + 2 * n) state.heap)
    (endEq : limit = pointer + labels.length)
    (separate : base + 2 * n ≤ pointer)
    (rowBound : row < state.heap.size)
    (sourceHeld : state.reg 0 = word width pointer) (rowHeld : state.reg 1 = word width row)
    (allocationHeld : state.reg 7 = word width state.heap.size)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (position : state.pc = word width (entry + 14)) (running : state.halted = false)
    (room : state.heap.size + 2 * labels.length < 2 ^ width) :
    ∃ final, Execution program state final (16 * labels.length + 4)
      (state.liveWords + 2 * labels.length) ∧
      BodyResult (n := n) state final entry limit labels.length base := by
  induction labels generalizing pointer state with
  | nil =>
      have pointerEq : pointer = limit := by simpa using endEq.symm
      let final := IndexScan.testFinished state (base + 2 * n) pointer limit (entry + 30)
      have trace := IndexScan.test_execution program (entry + 14) (base + 2 * n) pointer limit (entry + 30)
        0 state (body_test_at program entry base recordStart present) position running endpoint.bound endpoint.value
        sourceHeld (by decide) (by decide) (by omega) (by omega) (by omega) limitFits
      refine ⟨final, by simpa [final] using trace, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have exit := IndexScan.test_position state (entry + 14) (base + 2 * n) pointer limit (entry + 30)
          position (by omega) (by omega) limitFits
        simpa [final, pointerEq] using exit
      · simpa [final, test_reg state _ _ _ _ 0 (by decide) (by decide), pointerEq] using sourceHeld
      · exact test_reg state _ _ _ _ 1 (by decide) (by decide)
      · simpa [final, test_reg state _ _ _ _ 7 (by decide) (by decide)] using allocationHeld
      · exact test_reg state _ _ _ _ 2 (by decide) (by decide)
      · exact test_reg state _ _ _ _ 5 (by decide) (by decide)
      · simp [final]
      · simp [final]
      · simp [final]
      · simpa [final] using running
      · simpa [final] using buckets
  | cons label rest ih =>
      have sourceBound : pointer < state.heap.size := by have := stored.fits; simp only [List.length_cons] at this; omega
      have headBound := buckets.bound label
      let previous := (state.heap[headAddress base label]'headBound).val
      have previousBound : previous < state.heap.size := buckets.pointer label
      have head : state.heap[headAddress base label]'headBound = word width previous := by
        apply Fin.ext
        simp only [previous, word, Nat.mod_eq_of_lt (state.heap[headAddress base label]'headBound).isLt]
      let middle := bodyFinished state entry base pointer limit row previous label headBound
      have stepTrace := body_execution program entry base recordStart pointer limit row previous state label present
        position running endpoint.bound endpoint.value sourceBound headBound stored.head head previousBound rowBound
        sourceHeld rowHeld allocationHeld zero one (by simp only [List.length_cons] at endEq; omega)
        limitFits capacity (by simp only [List.length_cons] at room; omega)
      have frame := body_frame state entry base pointer limit row previous label headBound
      have middleHeap := body_heap state entry base pointer limit row previous label headBound
      have suffix : Controller.Horn.ResetTouched.LabelsStored rest (pointer + 1) middle.heap := by
        rw [show middle.heap = IndexBuild.linkedHeap state base label row previous headBound from middleHeap]
        exact labels_frame rest (pointer + 1) base row previous state label stored.tail headBound
          (by have := label.isLt; unfold headAddress; omega)
      have nextBuckets : BucketsValid (n := n) base middle.heap := by
        rw [show middle.heap = IndexBuild.linkedHeap state base label row previous headBound from middleHeap]
        exact buckets_after state base row previous label buckets (by simp only [List.length_cons] at room; omega)
      have nextEndpoint : Controller.Horn.SourceScan.CursorStored limit (base + 2 * n) middle.heap := by
        rw [show middle.heap = IndexBuild.linkedHeap state base label row previous headBound from middleHeap]
        exact endpoint_frame state base row previous limit label headBound endpoint
      obtain ⟨final, tailTrace, result⟩ := ih (pointer + 1) middle suffix nextBuckets nextEndpoint
        (by simp only [List.length_cons] at endEq; omega) (by omega)
        (by have size := frame.1; dsimp [middle] at ⊢; omega)
        frame.2.1 (frame.2.2.2.1.trans rowHeld)
        (by change middle.reg 7 = word width middle.heap.size; rw [show middle.heap.size = state.heap.size + 2 from frame.1]; exact frame.2.2.1)
        (frame.2.2.2.2.1.trans zero) (frame.2.2.2.2.2.1.trans one)
        (body_position state entry base pointer limit row previous label headBound zero)
        frame.2.2.2.2.2.2.2.2
        (by have size := frame.1; simp only [List.length_cons] at room; dsimp [middle] at ⊢; omega)
      have middleLive : middle.liveWords = state.liveWords + 2 := by
        unfold State.liveWords
        rw [frame.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1]
        omega
      refine ⟨final, ?_, ?_⟩
      · have trace := stepTrace.append tailTrace
        convert trace using 1
        · simp only [List.length_cons]; omega
        · rw [middleLive]
          simp only [List.length_cons]
          omega
      · refine ⟨result.position, result.sourceHeld, result.rowHeld.trans frame.2.2.2.1,
          result.allocationHeld, result.zero.trans frame.2.2.2.2.1,
          result.one.trans frame.2.2.2.2.2.1, ?_,
          result.stack.trans frame.2.2.2.2.2.2.1,
          result.output.trans frame.2.2.2.2.2.2.2.1, result.running, result.buckets⟩
        rw [result.growth, frame.1]
        simp only [List.length_cons]
        omega

/-- Concatenating original rows concatenates their occurrence lists at the
physical packed-record endpoint, retaining every original row's own offset. -/
theorem occurrences_append (left right : List (Controller.CNF.Clause (Fin n))) (start : Nat) :
    IndexScan.occurrences (left ++ right) start = IndexScan.occurrences left start ++
      IndexScan.occurrences right (Controller.Horn.NormalizeLoop.recordOffset left start left.length) := by
  induction left generalizing start with
  | nil => simp [IndexScan.occurrences, Controller.Horn.NormalizeLoop.recordOffset]
  | cons clause rest ih =>
      have tail := ih (start + 3 + (Controller.Horn.Worklist.compileClause clause).positives.length)
      simpa [IndexScan.occurrences, Controller.Horn.NormalizeLoop.recordOffset, List.take_length,
        Nat.add_assoc, List.append_assoc] using
        congrArg (fun suffix => (Controller.Horn.Worklist.compileClause clause).positives.map
          (fun label => (start, label)) ++ suffix) tail

/-- The ghost cursor prefix partitions the original occurrence list at the
physical endpoint of exactly those original rows already traversed. -/
theorem occurrences_split (clauses : List (Controller.CNF.Clause (Fin n))) (start index : Nat) :
    IndexScan.occurrences clauses start = IndexScan.occurrences (clauses.take index) start ++
      IndexScan.occurrences (clauses.drop index)
        (Controller.Horn.NormalizeLoop.recordOffset clauses start index) := by
  have partition := occurrences_append (clauses.take index) (clauses.drop index) start
  have offsetEq : Controller.Horn.NormalizeLoop.recordOffset (clauses.take index) start
      (clauses.take index).length = Controller.Horn.NormalizeLoop.recordOffset clauses start index := by
    unfold Controller.Horn.NormalizeLoop.recordOffset
    rw [List.take_length]
  rw [offsetEq] at partition
  simpa only [List.take_append_drop] using partition

theorem prefix_occurrences_succ (clauses : List (Controller.CNF.Clause (Fin n))) (start index : Nat)
    (bound : index < clauses.length) :
    (IndexScan.occurrences (clauses.take (index + 1)) start).length =
      (IndexScan.occurrences (clauses.take index) start).length +
        (Controller.Horn.Worklist.compileClause clauses[index]).positives.length := by
  rw [List.take_succ_eq_append_getElem bound, occurrences_append]
  simp [IndexScan.occurrences]

def rowExitFinished (state : State width 8) (entry : Nat) : State width 8 :=
  Controller.Horn.RuleDispatch.branchFinished (state.advance.put 1 (state.reg 0)) 2 (entry + 2)

/-- The outer cursor is copied from the body cursor only after its physical
endpoint test succeeds; both exit instructions are fetched from the same code. -/
theorem row_exit_execution (program : Program width 8) (entry base recordStart : Nat)
    (present : IndexScan.At (n := n) program entry base recordStart)
    (state : State width 8) (position : state.pc = word width (entry + 30))
    (running : state.halted = false) (capacity : entry + 32 < 2 ^ width) :
    Execution program state (rowExitFinished state entry) 2 state.liveWords := by
  let copied := state.advance.put 1 (state.reg 0)
  have copyAt : program[entry + 30]? = some (.copy 1 0) := by
    simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code] using present ⟨30, by decide⟩
  have returnAt : program[entry + 31]? = some (.branchZero 2 (word width (entry + 2))) := by
    simpa [IndexScan.code, IndexScan.setupPrefix, IndexScan.suffix, IndexBuild.code] using present ⟨31, by decide⟩
  have first : programStep program state = some copied := by
    unfold programStep
    rw [position, show (word width (entry + 30)).val = entry + 30 from Nat.mod_eq_of_lt (by omega), copyAt]
    simp [step, copied, running]
  have copiedPosition : copied.pc = word width (entry + 31) := by
    simp [copied, State.put, State.advance, position,
      show (word width (entry + 30)).val = entry + 30 from Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  have second := Controller.Horn.RuleDispatch.branch_execution program (entry + 31) (entry + 2) 2
    returnAt copied copiedPosition (by simpa [copied, State.put, State.advance] using running) (by omega)
  simpa [rowExitFinished, copied, State.liveWords, State.put, State.advance] using Execution.cons first second

/-- This is the real outer-loop back edge, forced by the preserved zero register. -/
theorem row_exit_position (state : State width 8) (entry : Nat)
    (zero : state.reg 2 = word width 0) :
    (rowExitFinished state entry).pc = word width (entry + 2) := by
  simp [rowExitFinished, Controller.Horn.RuleDispatch.branchFinished, State.put, State.advance, zero, word]

theorem row_exit_frame (state : State width 8) (entry : Nat) :
    let final := rowExitFinished state entry
    final.reg 1 = state.reg 0 ∧ final.reg 0 = state.reg 0 ∧ final.reg 7 = state.reg 7 ∧
    final.reg 2 = state.reg 2 ∧ final.reg 5 = state.reg 5 ∧
    final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
    final.halted = state.halted := by
  dsimp only
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame (state.advance.put 1 (state.reg 0)) 2 (entry + 2)
  simp only [rowExitFinished, frame.1, frame.2.1, frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1]
  simp [State.put, State.advance]

/-- The runtime cursor invariant refers to the next original retained occurrence;
repeated source rows occupy distinct offsets and all their links are indexed. -/
structure RowInvariant (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry rowIndex consumed processed : Nat)
    (state : State width 8) : Prop where
  rowBound : rowIndex < clauses.length
  consumedBound : consumed ≤ (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(rowBound))).positives.length
  processedEq : processed = (IndexScan.occurrences (clauses.take rowIndex) recordStart).length + consumed
  physical : IndexScan.PhysicalIndex clauses recordStart recordEnd base processed state.heap
  sourceHeld : state.reg 0 = word width (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex + 3 + consumed)
  rowHeld : state.reg 1 = word width (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex)
  allocationHeld : state.reg 7 = word width state.heap.size
  zero : state.reg 2 = word width 0
  one : state.reg 5 = word width 1
  endpoint : Controller.Horn.SourceScan.CursorStored
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart rowIndex + 3 +
      (Controller.Horn.Worklist.compileClause (clauses[rowIndex]'(rowBound))).positives.length)
    (base + 2 * n) state.heap
  position : state.pc = word width (entry + 14)
  running : state.halted = false

end Controller.Horn.IndexScanLoop
