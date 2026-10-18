module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.RowScan

@[expose] public section

/-!
# Physical normalized-rule storage

A rule record carries an explicit tag, a head word and a counted positive
body. The tag distinguishes an absent head from the valid channel zero.
Positive labels are copied from the actual suffix buffer before mark reset.
-/
namespace Controller.Horn.RuleCopy

open Controller.Cost Controller.Horn.Worklist
open Controller.Horn.ResetTouched

/-- A tag identifies inert, positive and negative-headed records. -/
def tag : Rule (Fin n) → Nat
  | .skip => 0
  | .positive _ => 1
  | .negative _ _ => 2

/-- The head word is interpreted only when the stored tag is two. -/
def headWord (width : Nat) : Rule (Fin n) → Word width
  | .negative head _ => word width head.val
  | _ => word width 0

/-- All record fields and every copied body label occur in the actual heap.
The count must fit the machine word; it is produced by the copying loop. -/
structure Stored (rule : Rule (Fin n)) (offset : Nat) (heap : Array (Word width)) : Prop where
  fits : offset + 3 + rule.positives.length ≤ heap.size
  countFits : rule.positives.length < 2 ^ width
  tagValue : heap[offset]'(by omega) = word width (tag rule)
  headValue : heap[offset + 1]'(by omega) = headWord width rule
  countValue : heap[offset + 2]'(by omega) = word width rule.positives.length
  body : LabelsStored rule.positives (offset + 3) heap

/-- Eight fixed instructions per copied label. Termination tests the actual
source pointer against the static end of its allocated scratch buffer. Register
four counts actual visits; no semantic list length is loaded into the code. -/
def bodyCode (width entry sourceEnd exit : Nat) : Program width 8 :=
  #[.constant 1 (word width sourceEnd), .xor 1 0 1,
    .branchZero 1 (word width exit), .load 3 0, .allocate 3,
    .add 0 0 5, .add 4 4 5, .branchZero 2 (word width entry)]

@[simp] theorem bodyCode_size (width entry sourceEnd exit : Nat) :
    (bodyCode width entry sourceEnd exit).size = 8 := rfl

/-- The positive source cursor is physically read, and the visit counter is
initialized by a fetched constant. -/
def setupCode (width positiveHeader : Nat) : Program width 8 :=
  #[.constant 0 (word width positiveHeader), .load 0 0, .constant 4 (word width 0)]

@[simp] theorem setupCode_size (width positiveHeader : Nat) :
    (setupCode width positiveHeader).size = 3 := rfl

/-- The actual visit count is written through the preserved record address.
That address must be established by the physical record-cursor prologue. -/
def finishCode (width : Nat) : Program width 8 := #[.store 7 4]

@[simp] theorem finishCode_size (width : Nat) : (finishCode width).size = 1 := rfl

/-- Appending one copied label preserves every source label already in heap. -/
theorem labels_after_push {labels : List (Fin n)} {offset : Nat}
    {heap : Array (Word width)} (stored : LabelsStored labels offset heap) (value : Word width) :
    LabelsStored labels offset (heap.push value) := by
  refine ⟨by have := stored.fits; simp only [Array.size_push]; omega, ?_⟩
  intro index
  have bound : offset + index.val < heap.size := by
    have := stored.fits
    have := index.isLt
    omega
  exact (Array.getElem_push_lt bound).trans (stored.entry index)

/-- Later body allocations preserve every already stored rule record. -/
theorem Stored.after_push {rule : Rule (Fin n)} {offset : Nat} {heap : Array (Word width)}
    (stored : Stored rule offset heap) (value : Word width) : Stored rule offset (heap.push value) := by
  have tagBound : offset < heap.size := by have := stored.fits; omega
  have headBound : offset + 1 < heap.size := by have := stored.fits; omega
  have countBound : offset + 2 < heap.size := by have := stored.fits; omega
  refine ⟨by have := stored.fits; simp only [Array.size_push]; omega,
    stored.countFits, ?_, ?_, ?_, labels_after_push stored.body value⟩
  · exact (Array.getElem_push_lt tagBound).trans stored.tagValue
  · exact (Array.getElem_push_lt headBound).trans stored.headValue
  · exact (Array.getElem_push_lt countBound).trans stored.countValue

/-- Allocation at the heap end preserves the scratch marks for later reset. -/
theorem marks_after_push {marks : IndexedNormalize.Marks n} {base : Nat}
    {heap : Array (Word width)} (stored : Controller.Horn.MarkStorage.Stored marks base heap)
    (value : Word width) : Controller.Horn.MarkStorage.Stored marks base (heap.push value) := by
  refine ⟨by have := stored.fits; simp only [Array.size_push]; omega, ?_⟩
  intro literal
  exact (Array.getElem_push_lt (stored.bound literal)).trans (stored.entry literal)

/-- Appending a copied word preserves a physically stored suffix cursor. -/
theorem header_after_push {labels : List (Fin n)} {header lower cursor limit : Nat}
    {heap : Array (Word width)}
    (stored : Controller.Horn.RecordStorage.HeaderStored labels header lower cursor limit heap)
    (value : Word width) :
    Controller.Horn.RecordStorage.HeaderStored labels header lower cursor limit (heap.push value) := by
  refine ⟨⟨stored.buffer.lower_le_cursor, stored.buffer.ends,
    by have := stored.buffer.fits; simp only [Array.size_push]; omega,
    labels_after_push stored.buffer.labels value⟩,
    by have := stored.bound; simp only [Array.size_push]; omega,
    stored.separate, ?_⟩
  exact (Array.getElem_push_lt stored.bound).trans stored.value

/-- The complete scratch row survives each actual positive-body allocation. -/
theorem row_after_push {row : IndexedNormalize.Row n}
    {base positive negative touched : Nat} {heap : Array (Word width)}
    (stored : Controller.Horn.LiteralDispatch.RowStored row base positive negative touched heap)
    (value : Word width) :
    Controller.Horn.LiteralDispatch.RowStored row base positive negative touched (heap.push value) := by
  refine ⟨marks_after_push stored.marks value,
    header_after_push stored.positive value, header_after_push stored.negative value,
    header_after_push stored.touched value,
    by have := stored.flagBound; simp only [Array.size_push]; omega, ?_⟩
  exact (Array.getElem_push_lt stored.flagBound).trans stored.flag

/-- The actual body loop compares two pointer words before copying. -/
def bodyTest (state : Controller.Cost.State width 8) (pointer sourceEnd : Nat) : Controller.Cost.State width 8 :=
  (state.advance.put 1 (word width sourceEnd)).advance.put 1
    (word width (Nat.xor pointer sourceEnd))

/-- One body iteration appends its physically loaded label and increments
both the pointer and the visit counter before returning to the same loop. -/
def bodyFinished (state : Controller.Cost.State width 8) (entry pointer sourceEnd count : Nat)
    (label : Fin n) : Controller.Cost.State width 8 :=
  let tested := (bodyTest state pointer sourceEnd).advance
  let loaded := tested.advance.put 3 (word width label.val)
  let copied := { loaded.advance with heap := loaded.heap.push (word width label.val) }
  let advanced := copied.advance.put 0 (word width (pointer + 1))
  let counted := advanced.advance.put 4 (word width (count + 1))
  { counted.advance with pc := word width entry }

@[simp] theorem bodyFinished_heap (state : Controller.Cost.State width 8)
    (entry pointer sourceEnd count : Nat) (label : Fin n) :
    (bodyFinished state entry pointer sourceEnd count label).heap =
      state.heap.push (word width label.val) := rfl

/-- The tail remains physically readable after allocating the copied head. -/
theorem bodyFinished_tail (state : Controller.Cost.State width 8) (entry pointer sourceEnd count : Nat)
    (label : Fin n) (tail : List (Fin n)) (stored : LabelsStored (label :: tail) pointer state.heap) :
    LabelsStored tail (pointer + 1) (bodyFinished state entry pointer sourceEnd count label).heap :=
  labels_after_push stored.tail (word width label.val)

/-- The next iteration starts with physically incremented pointer and count. -/
theorem bodyFinished_control (state : Controller.Cost.State width 8) (entry pointer sourceEnd count : Nat)
    (label : Fin n) (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (running : state.halted = false) :
    (bodyFinished state entry pointer sourceEnd count label).reg 0 = word width (pointer + 1) ∧
    (bodyFinished state entry pointer sourceEnd count label).reg 4 = word width (count + 1) ∧
    (bodyFinished state entry pointer sourceEnd count label).reg 2 = word width 0 ∧
    (bodyFinished state entry pointer sourceEnd count label).reg 5 = word width 1 ∧
    (bodyFinished state entry pointer sourceEnd count label).halted = false ∧
    (bodyFinished state entry pointer sourceEnd count label).pc = word width entry ∧
    (bodyFinished state entry pointer sourceEnd count label).stack = state.stack ∧
    (bodyFinished state entry pointer sourceEnd count label).output = state.output := by
  simp [bodyFinished, bodyTest, Controller.Cost.State.put, Controller.Cost.State.advance, zero, one, running]

/-- Body copying preserves the actual decrement constant needed by reset. -/
theorem bodyFinished_decrement (state : Controller.Cost.State width 8) (entry pointer sourceEnd count : Nat)
    (label : Fin n) : (bodyFinished state entry pointer sourceEnd count label).reg 6 = state.reg 6 := by
  simp [bodyFinished, bodyTest, Controller.Cost.State.put, Controller.Cost.State.advance]

/-- The actual persistent count-cell address survives every body iteration. -/
theorem bodyFinished_recordAddress (state : Controller.Cost.State width 8) (entry pointer sourceEnd count : Nat)
    (label : Fin n) : (bodyFinished state entry pointer sourceEnd count label).reg 7 = state.reg 7 := by
  simp [bodyFinished, bodyTest, Controller.Cost.State.put, Controller.Cost.State.advance]

def BodyAt (program : Program width 8) (entry sourceEnd exit : Nat) : Prop :=
  ∀ phase : Fin 8, program[entry + phase.val]? =
    some ((bodyCode width entry sourceEnd exit)[phase.val])

@[simp] private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem advance_position (state : Controller.Cost.State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [Controller.Cost.State.advance, position, word_val (width := width) entry fits]

/-- The empty suffix exits after three actual pointer-test instructions. -/
theorem body_terminal (program : Program width 8) (entry sourceEnd exit : Nat)
    (present : BodyAt program entry sourceEnd exit) (state : Controller.Cost.State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (pointerHeld : state.reg 0 = word width sourceEnd)
    (capacity : entry + 3 < 2 ^ width) (endFits : sourceEnd < 2 ^ width) :
    Execution program state
      { (bodyTest state sourceEnd sourceEnd).advance with pc := word width exit }
      3 state.liveWords := by
  let s1 := state.advance.put 1 (word width sourceEnd)
  let s2 := s1.advance.put 1 (word width 0)
  let final := { s2.advance with pc := word width exit }
  have p1 : s1.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, Controller.Cost.State.put, Nat.add_assoc] using advance_position s1 (entry + 1) p1 (by omega)
  have t1 : programStep program state = some s1 := by
    have read : program[state.pc.val]? = some (.constant 1 (word width sourceEnd)) := by
      rw [position, word_val (width := width) entry (by omega)]
      simpa [bodyCode] using present 0
    unfold programStep
    rw [read]
    change step (.constant 1 (word width sourceEnd)) state = _
    simp [step, running, s1]
  have t2 : programStep program s1 = some s2 := by
    have read : program[s1.pc.val]? = some (.xor 1 0 1) := by
      rw [p1, word_val (width := width) (entry + 1) (by omega)]
      simpa [bodyCode] using present 1
    unfold programStep
    rw [read]
    change step (.xor 1 0 1) s1 = _
    simp [step, s1, s2, Controller.Cost.State.put, Controller.Cost.State.advance, running, pointerHeld, word_val (width := width) sourceEnd endFits]
  have t3 : programStep program s2 = some final := by
    have read : program[s2.pc.val]? = some (.branchZero 1 (word width exit)) := by
      rw [p2, word_val (width := width) (entry + 2) (by omega)]
      simpa [bodyCode] using present 2
    unfold programStep
    rw [read]
    change step (.branchZero 1 (word width exit)) s2 = _
    simp [step, s2, s1, final, Controller.Cost.State.put, Controller.Cost.State.advance, running, word]
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl final)))
  simpa [bodyTest, final, s2, s1, Controller.Cost.State.put, Controller.Cost.State.advance, Controller.Cost.State.liveWords] using trace

/-- One physical source label is copied by eight fetched instructions.
The count and pointer increments are actual register updates. -/
theorem body_iteration (program : Program width 8) (entry pointer sourceEnd exit count : Nat)
    (present : BodyAt program entry sourceEnd exit) (state : Controller.Cost.State width 8)
    (label : Fin n) (tail : List (Fin n)) (stored : LabelsStored (label :: tail) pointer state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (pointerHeld : state.reg 0 = word width pointer) (countHeld : state.reg 4 = word width count)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (different : pointer ≠ sourceEnd) (capacity : entry + 8 < 2 ^ width)
    (pointerFits : pointer + 1 < 2 ^ width) (endFits : sourceEnd < 2 ^ width)
    (countFits : count + 1 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (bodyFinished state entry pointer sourceEnd count label) 8
      (state.liveWords + 1) := by
  let s1 := state.advance.put 1 (word width sourceEnd)
  let s2 := s1.advance.put 1 (word width (Nat.xor pointer sourceEnd))
  let s3 := s2.advance
  let s4 := s3.advance.put 3 (word width label.val)
  let s5 := { s4.advance with heap := s4.heap.push (word width label.val) }
  let s6 := s5.advance.put 0 (word width (pointer + 1))
  let s7 := s6.advance.put 4 (word width (count + 1))
  let s8 := { s7.advance with pc := word width entry }
  have p1 : s1.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, Controller.Cost.State.put, Nat.add_assoc] using advance_position s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa [s3, Controller.Cost.State.put, Nat.add_assoc] using advance_position s2 (entry + 2) p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    simpa [s4, Controller.Cost.State.put, Nat.add_assoc] using advance_position s3 (entry + 3) p3 (by omega)
  have p5 : s5.pc = word width (entry + 5) := by
    simpa [s5, Nat.add_assoc] using advance_position s4 (entry + 4) p4 (by omega)
  have p6 : s6.pc = word width (entry + 6) := by
    simpa [s6, Controller.Cost.State.put, Nat.add_assoc] using advance_position s5 (entry + 5) p5 (by omega)
  have p7 : s7.pc = word width (entry + 7) := by
    simpa [s7, Controller.Cost.State.put, Nat.add_assoc] using advance_position s6 (entry + 6) p6 (by omega)
  have fetched (phase : Fin 8) (current : Controller.Cost.State width 8)
      (pc : current.pc = word width (entry + phase.val)) :
      program[current.pc.val]? = some (bodyCode width entry sourceEnd exit)[phase.val] := by
    rw [pc, word_val (width := width) (entry + phase.val) (by have := phase.isLt; omega)]
    exact present phase
  have t1 : programStep program state = some s1 := by
    have read : program[state.pc.val]? = some (.constant 1 (word width sourceEnd)) := by
      simpa [bodyCode] using fetched 0 state (by simpa using position)
    unfold programStep
    rw [read]
    change step (.constant 1 (word width sourceEnd)) state = _
    simp [step, running, s1]
  have t2 : programStep program s1 = some s2 := by
    have read : program[s1.pc.val]? = some (.xor 1 0 1) := by
      simpa [bodyCode] using fetched 1 s1 p1
    unfold programStep
    rw [read]
    change step (.xor 1 0 1) s1 = _
    have held : s1.reg 0 = word width pointer := by simp [s1, Controller.Cost.State.put, Controller.Cost.State.advance, pointerHeld]
    simp [step, s1, s2, running, held, Controller.Cost.State.put, Controller.Cost.State.advance,
      pointerHeld, word_val (width := width) pointer (by omega), word_val (width := width) sourceEnd endFits]
  have t3 : programStep program s2 = some s3 := by
    have read : program[s2.pc.val]? = some (.branchZero 1 (word width exit)) := by
      simpa [bodyCode] using fetched 2 s2 p2
    unfold programStep
    rw [read]
    change step (.branchZero 1 (word width exit)) s2 = _
    have xorFits := Nat.xor_lt_two_pow (show pointer < 2 ^ width by omega) endFits
    have nonzero : Nat.xor pointer sourceEnd ≠ 0 := fun equal =>
      different ((Controller.Horn.ResetPointer.xor_zero_iff _ _).mp equal)
    have held : s2.reg 1 = word width (Nat.xor pointer sourceEnd) := by
      simp [s2, Controller.Cost.State.put]
    simp only [step, show s2.halted = false from running, Bool.false_eq_true, ite_false, held]
    change some (if (word width (Nat.xor pointer sourceEnd)).val = 0 then _ else _) = _
    rw [word_val (width := width) (Nat.xor pointer sourceEnd) xorFits, ite_eq_right nonzero]
  have t4 : programStep program s3 = some s4 := by
    have read : program[s3.pc.val]? = some (.load 3 0) := by
      simpa [bodyCode] using fetched 3 s3 p3
    unfold programStep
    rw [read]
    change step (.load 3 0) s3 = _
    have held : s3.reg 0 = word width pointer := by simp [s3, s2, s1, Controller.Cost.State.put, Controller.Cost.State.advance, pointerHeld]
    have bound : pointer < s3.heap.size := by
      change pointer < state.heap.size
      have := stored.fits
      simp only [List.length_cons] at this
      omega
    simp only [step, show s3.halted = false from running, Bool.false_eq_true, ite_false,
      held, word_val (width := width) pointer (by omega), dite_eq_left bound]
    change some (s3.advance.put 3 (state.heap[pointer]'(by simpa [s3, s2, s1, Controller.Cost.State.advance, Controller.Cost.State.put] using bound))) = some s4
    rw [stored.head]
  have t5 : programStep program s4 = some s5 := by
    have read : program[s4.pc.val]? = some (.allocate 3) := by
      simpa [bodyCode] using fetched 4 s4 p4
    unfold programStep
    rw [read]
    change step (.allocate 3) s4 = _
    simp [step, s4, s3, s2, s1, s5, Controller.Cost.State.put, Controller.Cost.State.advance, running, heapFits]
  have t6 : programStep program s5 = some s6 := by
    have read : program[s5.pc.val]? = some (.add 0 0 5) := by
      simpa [bodyCode] using fetched 5 s5 p5
    unfold programStep
    rw [read]
    change step (.add 0 0 5) s5 = _
    simp [step, s6, s5, s4, s3, s2, s1, Controller.Cost.State.put, Controller.Cost.State.advance, running,
      pointerHeld, one, word_val (width := width) pointer (by omega), word_val (width := width) 1 (by omega)]
  have t7 : programStep program s6 = some s7 := by
    have read : program[s6.pc.val]? = some (.add 4 4 5) := by
      simpa [bodyCode] using fetched 6 s6 p6
    unfold programStep
    rw [read]
    change step (.add 4 4 5) s6 = _
    simp [step, s7, s6, s5, s4, s3, s2, s1, Controller.Cost.State.put, Controller.Cost.State.advance, running,
      countHeld, one, word_val (width := width) count (by omega), word_val (width := width) 1 (by omega)]
  have t8 : programStep program s7 = some s8 := by
    have read : program[s7.pc.val]? = some (.branchZero 2 (word width entry)) := by
      simpa [bodyCode] using fetched 7 s7 p7
    unfold programStep
    rw [read]
    change step (.branchZero 2 (word width entry)) s7 = _
    simp [step, s8, s7, s6, s5, s4, s3, s2, s1, Controller.Cost.State.put, Controller.Cost.State.advance, running, zero, word]
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4
    (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s8))))))))
  have l1 : s1.liveWords = state.liveWords := rfl
  have l2 : s2.liveWords = state.liveWords := rfl
  have l3 : s3.liveWords = state.liveWords := rfl
  have l4 : s4.liveWords = state.liveWords := rfl
  have l5 : s5.liveWords = state.liveWords + 1 := by
    simp only [s5, s4, s3, s2, s1, Controller.Cost.State.liveWords, Controller.Cost.State.advance, Controller.Cost.State.put, Array.size_push]
    omega
  have l6 : s6.liveWords = state.liveWords + 1 := l5
  have l7 : s7.liveWords = state.liveWords + 1 := l5
  have l8 : s8.liveWords = state.liveWords + 1 := l5
  have peak : max state.liveWords (state.liveWords + 1) = state.liveWords + 1 := Nat.max_eq_right (by omega)
  change Execution program state s8 8 (state.liveWords + 1)
  simpa only [l1, l2, l3, l4, l5, l6, l7, l8, Nat.max_self, peak] using trace

/-- Logical description of the heap produced by successive actual allocations. -/
def copiedHeap (heap : Array (Word width)) : List (Fin n) → Array (Word width)
  | [] => heap
  | label :: tail => copiedHeap (heap.push (word width label.val)) tail

@[simp] theorem copiedHeap_size (heap : Array (Word width)) (labels : List (Fin n)) :
    (copiedHeap heap labels).size = heap.size + labels.length := by
  induction labels generalizing heap with
  | nil => simp [copiedHeap]
  | cons label tail ih => simp [copiedHeap, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Every old heap cell survives the whole allocation traversal. -/
theorem copiedHeap_frame (heap : Array (Word width)) (labels : List (Fin n))
    (index : Nat) (bound : index < heap.size) :
    (copiedHeap heap labels)[index]'(by rw [copiedHeap_size]; omega) = heap[index] := by
  induction labels generalizing heap with
  | nil => rfl
  | cons label tail ih =>
    exact (ih (heap.push (word width label.val)) (by simp only [Array.size_push]; omega)).trans
      (Array.getElem_push_lt bound)

/-- Copied body labels occupy consecutive newly allocated heap cells. -/
theorem copied_labels (heap : Array (Word width)) (labels : List (Fin n)) :
    LabelsStored labels heap.size (copiedHeap heap labels) := by
  induction labels generalizing heap with
  | nil =>
    refine ⟨by simp [copiedHeap], ?_⟩
    intro index
    exact Fin.elim0 index
  | cons label tail ih =>
    have rest := ih (heap.push (word width label.val))
    refine ⟨by simp only [copiedHeap_size]; omega, ?_⟩
    intro index
    by_cases first : index.val = 0
    · have frame := copiedHeap_frame (heap.push (word width label.val)) tail heap.size (by simp)
      simpa [copiedHeap, first] using frame
    · have bound : index.val - 1 < tail.length := by
        have := index.isLt
        simp only [List.length_cons] at this
        omega
      let previous : Fin tail.length := ⟨index.val - 1, bound⟩
      have equation : index.val = previous.val + 1 := by dsimp [previous]; omega
      have successor : (label :: tail)[index.val] = tail[previous.val] := by
        simp only [equation, List.getElem_cons_succ]
      rw [successor]
      simpa [copiedHeap, Array.size_push, equation, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest.entry previous

/-- The scratch row remains intact until the later touched reset. -/
theorem row_after_copy {row : IndexedNormalize.Row n} {base positive negative touched : Nat}
    {heap : Array (Word width)}
    (stored : Controller.Horn.LiteralDispatch.RowStored row base positive negative touched heap)
    (labels : List (Fin n)) :
    Controller.Horn.LiteralDispatch.RowStored row base positive negative touched (copiedHeap heap labels) := by
  induction labels generalizing heap with
  | nil => exact stored
  | cons label tail ih => exact ih (row_after_push stored (word width label.val))

/-- Full physical positive-buffer traversal. Its proof index is the suffix
list; the machine tests only pointer equality and increments its visit counter. -/
theorem body_execution (program : Program width 8) (entry pointer sourceEnd exit count : Nat)
    (present : BodyAt program entry sourceEnd exit) (state : Controller.Cost.State width 8)
    (labels : List (Fin n)) (stored : LabelsStored labels pointer state.heap)
    (ends : pointer + labels.length = sourceEnd)
    (position : state.pc = word width entry) (running : state.halted = false)
    (pointerHeld : state.reg 0 = word width pointer) (countHeld : state.reg 4 = word width count)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (capacity : entry + 8 < 2 ^ width) (endFits : sourceEnd < 2 ^ width)
    (countFits : count + labels.length < 2 ^ width)
    (heapFits : state.heap.size + labels.length < 2 ^ width) :
    ∃ final : Controller.Cost.State width 8,
      Execution program state final (8 * labels.length + 3) (state.liveWords + labels.length) ∧
      final.heap = copiedHeap state.heap labels ∧
      final.reg 0 = word width sourceEnd ∧ final.reg 4 = word width (count + labels.length) ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 ∧ final.halted = false ∧
      final.pc = word width exit ∧ final.stack = state.stack ∧ final.output = state.output := by
  induction labels generalizing state pointer count with
  | nil =>
    have equal : pointer = sourceEnd := by simpa using ends
    let final := { (bodyTest state sourceEnd sourceEnd).advance with pc := word width exit }
    have trace := body_terminal program entry sourceEnd exit present state position running
      (by simpa only [equal] using pointerHeld) (by omega) endFits
    refine ⟨final, by simpa using trace, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    all_goals simp [final, bodyTest, Controller.Cost.State.put, Controller.Cost.State.advance, pointerHeld, countHeld, equal, zero, one, running]
  | cons label tail ih =>
    have different : pointer ≠ sourceEnd := by simp only [List.length_cons] at ends; omega
    let middle := bodyFinished state entry pointer sourceEnd count label
    have first := body_iteration program entry pointer sourceEnd exit count present state label tail stored
      position running pointerHeld countHeld one zero different capacity
      (by simp only [List.length_cons] at ends; omega) endFits
      (by simp only [List.length_cons] at countFits; omega)
      (by simp only [List.length_cons] at heapFits; omega)
    have held := bodyFinished_control state entry pointer sourceEnd count label zero one running
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp only [middle, bodyFinished, bodyTest, Controller.Cost.State.liveWords, Controller.Cost.State.advance, Controller.Cost.State.put, Array.size_push]
      omega
    obtain ⟨final, rest, heap, finalPointer, finalCount, finalZero, finalOne, finalSix, finalSeven, finalRunning,
      finalPC, stack, output⟩ :=
      ih (pointer + 1) (count + 1) middle (bodyFinished_tail state entry pointer sourceEnd count label tail stored)
        (by simp only [List.length_cons] at ends; omega)
        held.2.2.2.2.2.1 held.2.2.2.2.1 held.1 held.2.1 held.2.2.2.1 held.2.2.1
        (by simp only [List.length_cons] at countFits; omega)
        (by simp only [middle, bodyFinished_heap, Array.size_push]; simp only [List.length_cons] at heapFits; omega)
    have trace := first.append rest
    have ticks : 8 + (8 * tail.length + 3) = 8 * (label :: tail).length + 3 := by simp only [List.length_cons]; omega
    have peak : max (state.liveWords + 1) (middle.liveWords + tail.length) =
        state.liveWords + (label :: tail).length := by rw [middleLive]; simp only [List.length_cons]; omega
    refine ⟨final, by simpa only [ticks, peak] using trace,
      by simpa only [middle, bodyFinished_heap, copiedHeap] using heap,
      finalPointer, ?_, finalZero, finalOne,
      finalSix.trans (bodyFinished_decrement state entry pointer sourceEnd count label),
      finalSeven.trans (bodyFinished_recordAddress state entry pointer sourceEnd count label), finalRunning, finalPC,
      stack.trans held.2.2.2.2.2.2.1, output.trans held.2.2.2.2.2.2.2⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalCount

def SetupAt (program : Program width 8) (entry positiveHeader : Nat) : Prop :=
  ∀ phase : Fin 3, program[entry + phase.val]? = some ((setupCode width positiveHeader)[phase.val])

def setupFinished (state : Controller.Cost.State width 8) (positiveHeader pointer : Nat) : Controller.Cost.State width 8 :=
  let s1 := state.advance.put 0 (word width positiveHeader)
  let s2 := s1.advance.put 0 (word width pointer)
  s2.advance.put 4 (word width 0)

/-- The body cursor comes from its physical heap header, not a supplied count. -/
theorem setup_execution (program : Program width 8) (entry positiveHeader pointer : Nat)
    (present : SetupAt program entry positiveHeader) (state : Controller.Cost.State width 8)
    (cursor : Controller.Horn.SourceScan.CursorStored pointer positiveHeader state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 3 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (setupFinished state positiveHeader pointer) 3 state.liveWords := by
  let s1 := state.advance.put 0 (word width positiveHeader)
  let s2 := s1.advance.put 0 (word width pointer)
  let s3 := s2.advance.put 4 (word width 0)
  have p1 : s1.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, Controller.Cost.State.put, Nat.add_assoc] using advance_position s1 (entry + 1) p1 (by omega)
  have t1 : programStep program state = some s1 := by
    have read : program[state.pc.val]? = some (.constant 0 (word width positiveHeader)) := by
      rw [position, word_val (width := width) entry (by omega)]
      simpa [setupCode] using present 0
    unfold programStep
    rw [read]
    change step (.constant 0 (word width positiveHeader)) state = _
    simp [step, running, s1]
  have t2 : programStep program s1 = some s2 := by
    have read : program[s1.pc.val]? = some (.load 0 0) := by
      rw [p1, word_val (width := width) (entry + 1) (by omega)]
      simpa [setupCode] using present 1
    unfold programStep
    rw [read]
    change step (.load 0 0) s1 = _
    have held : (s1.reg 0).val = positiveHeader := by
      simp [s1, Controller.Cost.State.put, word_val (width := width) positiveHeader (cursor.bound.trans heapFits)]
    have bound : positiveHeader < s1.heap.size := cursor.bound
    simp only [step, show s1.halted = false from running, Bool.false_eq_true, ite_false, held, dite_eq_left bound]
    change some (s1.advance.put 0 (state.heap[positiveHeader]'cursor.bound)) = some s2
    rw [cursor.value]
  have t3 : programStep program s2 = some s3 := by
    have read : program[s2.pc.val]? = some (.constant 4 (word width 0)) := by
      rw [p2, word_val (width := width) (entry + 2) (by omega)]
      simpa [setupCode] using present 2
    unfold programStep
    rw [read]
    change step (.constant 4 (word width 0)) s2 = _
    simp [step, s3, s2, s1, Controller.Cost.State.put, Controller.Cost.State.advance, running]
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s3)))
  simpa [setupFinished, s3, s2, s1, Controller.Cost.State.liveWords, Controller.Cost.State.advance, Controller.Cost.State.put] using trace

def FinishAt (program : Program width 8) (entry : Nat) : Prop :=
  program[entry]? = some (.store 7 4)

def finishStored (state : Controller.Cost.State width 8) (countHeader : Nat) (bound : countHeader < state.heap.size) : Controller.Cost.State width 8 :=
  { state.advance with heap := state.heap.set countHeader (state.reg 4) bound }

/-- The actual preserved record address receives the incremented body counter. -/
theorem finish_execution (program : Program width 8) (entry countHeader : Nat)
    (present : FinishAt program entry) (state : Controller.Cost.State width 8)
    (bound : countHeader < state.heap.size) (position : state.pc = word width entry)
    (recordAddress : state.reg 7 = word width countHeader)
    (running : state.halted = false) (capacity : entry < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (finishStored state countHeader bound) 1 state.liveWords := by
  have transition : programStep program state = some (finishStored state countHeader bound) := by
    unfold programStep
    rw [position, word_val (width := width) entry capacity, present]
    change step (.store 7 4) state = _
    simp only [step, running, Bool.false_eq_true, ite_false, recordAddress,
      word_val (width := width) countHeader (bound.trans heapFits), dite_eq_left bound]
    rfl
  simpa [finishStored, Controller.Cost.State.liveWords, Controller.Cost.State.advance] using
    Execution.cons transition (Execution.refl (finishStored state countHeader bound))

/-- Reading the persistent count header returns the actual counter register. -/
theorem finishStored_count (state : Controller.Cost.State width 8) (countHeader : Nat)
    (bound : countHeader < state.heap.size) :
    (finishStored state countHeader bound).heap[countHeader]'(by simpa [finishStored] using bound) =
      state.reg 4 := by
  simp [finishStored]

/-- The count store preserves every other existing heap cell. -/
theorem finishStored_frame (state : Controller.Cost.State width 8) (countHeader : Nat)
    (bound : countHeader < state.heap.size) (index : Nat) (valid : index < state.heap.size)
    (different : countHeader ≠ index) :
    (finishStored state countHeader bound).heap[index]'(by simpa [finishStored] using valid) =
      state.heap[index] :=
  Array.getElem_set_ne bound valid different

/-- Writing the output count preserves the next stage's common registers. -/
theorem finishStored_control (state : Controller.Cost.State width 8) (countHeader : Nat)
    (bound : countHeader < state.heap.size)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1)) (running : state.halted = false) :
    (finishStored state countHeader bound).reg 2 = word width 0 ∧
    (finishStored state countHeader bound).reg 5 = word width 1 ∧
    (finishStored state countHeader bound).reg 6 = word width (2 ^ width - 1) ∧
    (finishStored state countHeader bound).halted = false ∧
    (finishStored state countHeader bound).stack = state.stack ∧
    (finishStored state countHeader bound).output = state.output := by
  simp [finishStored, Controller.Cost.State.put, Controller.Cost.State.advance, zero, one, decrement, running]

/-- The record count address comes from an actual persistent heap cursor. -/
def recordAddressCode (width recordCursorHeader : Nat) : Program width 8 :=
  #[.constant 7 (word width recordCursorHeader), .load 7 7, .add 7 7 5, .add 7 7 5]

@[simp] theorem recordAddressCode_size (width recordCursorHeader : Nat) :
    (recordAddressCode width recordCursorHeader).size = 4 := rfl

def RecordAddressAt (program : Program width 8) (entry recordCursorHeader : Nat) : Prop :=
  ∀ phase : Fin 4, program[entry + phase.val]? = some ((recordAddressCode width recordCursorHeader)[phase.val])

def recordAddressFinished (state : Controller.Cost.State width 8) (recordCursorHeader recordStart : Nat) : Controller.Cost.State width 8 :=
  let s1 := state.advance.put 7 (word width recordCursorHeader)
  let s2 := s1.advance.put 7 (word width recordStart)
  let s3 := s2.advance.put 7 (word width (recordStart + 1))
  s3.advance.put 7 (word width (recordStart + 2))

/-- Four fetched instructions load the current record start and compute its
count field. Neither an output offset nor a normalized body length is an
immediate operand of this program. -/
theorem record_address_execution (program : Program width 8) (entry recordCursorHeader recordStart : Nat)
    (present : RecordAddressAt program entry recordCursorHeader) (state : Controller.Cost.State width 8)
    (cursor : Controller.Horn.SourceScan.CursorStored recordStart recordCursorHeader state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (one : state.reg 5 = word width 1) (capacity : entry + 4 < 2 ^ width)
    (recordFits : recordStart + 2 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (recordAddressFinished state recordCursorHeader recordStart) 4 state.liveWords := by
  let s1 := state.advance.put 7 (word width recordCursorHeader)
  let s2 := s1.advance.put 7 (word width recordStart)
  let s3 := s2.advance.put 7 (word width (recordStart + 1))
  let s4 := s3.advance.put 7 (word width (recordStart + 2))
  have p1 : s1.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, Controller.Cost.State.put, Nat.add_assoc] using advance_position s1 (entry + 1) p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa [s3, Controller.Cost.State.put, Nat.add_assoc] using advance_position s2 (entry + 2) p2 (by omega)
  have t1 : programStep program state = some s1 := by
    have read : program[state.pc.val]? = some (.constant 7 (word width recordCursorHeader)) := by
      rw [position, word_val (width := width) entry (by omega)]
      simpa [recordAddressCode] using present 0
    unfold programStep
    rw [read]
    change step (.constant 7 (word width recordCursorHeader)) state = _
    simp [step, running, s1]
  have t2 : programStep program s1 = some s2 := by
    have read : program[s1.pc.val]? = some (.load 7 7) := by
      rw [p1, word_val (width := width) (entry + 1) (by omega)]
      simpa [recordAddressCode] using present 1
    unfold programStep
    rw [read]
    change step (.load 7 7) s1 = _
    have held : (s1.reg 7).val = recordCursorHeader := by
      simp [s1, Controller.Cost.State.put, word_val (width := width) recordCursorHeader (cursor.bound.trans heapFits)]
    have bound : recordCursorHeader < s1.heap.size := cursor.bound
    simp only [step, show s1.halted = false from running, Bool.false_eq_true, ite_false, held, dite_eq_left bound]
    change some (s1.advance.put 7 (state.heap[recordCursorHeader]'cursor.bound)) = some s2
    rw [cursor.value]
  have t3 : programStep program s2 = some s3 := by
    have read : program[s2.pc.val]? = some (.add 7 7 5) := by
      rw [p2, word_val (width := width) (entry + 2) (by omega)]
      simpa [recordAddressCode] using present 2
    unfold programStep
    rw [read]
    change step (.add 7 7 5) s2 = _
    simp [step, s3, s2, s1, Controller.Cost.State.put, Controller.Cost.State.advance, running, one,
      word_val (width := width) recordStart (by omega), word_val (width := width) 1 (by omega)]
  have t4 : programStep program s3 = some s4 := by
    have read : program[s3.pc.val]? = some (.add 7 7 5) := by
      rw [p3, word_val (width := width) (entry + 3) (by omega)]
      simpa [recordAddressCode] using present 3
    unfold programStep
    rw [read]
    change step (.add 7 7 5) s3 = _
    simp [step, s4, s3, s2, s1, Controller.Cost.State.put, Controller.Cost.State.advance, running, one,
      word_val (width := width) (recordStart + 1) (by omega), word_val (width := width) 1 (by omega), Nat.add_assoc]
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.refl s4))))
  simpa [recordAddressFinished, s4, s3, s2, s1, Controller.Cost.State.liveWords, Controller.Cost.State.advance, Controller.Cost.State.put] using trace

@[simp] theorem recordAddressFinished_value (state : Controller.Cost.State width 8) (recordCursorHeader recordStart : Nat) :
    (recordAddressFinished state recordCursorHeader recordStart).reg 7 = word width (recordStart + 2) := by
  simp [recordAddressFinished, Controller.Cost.State.put]

/-- Three actual allocations store the physically selected tag, head and zero
counter. The tag and head registers are established by source-row dispatch. -/
def headerCode (width : Nat) : Program width 8 := #[.allocate 1, .allocate 3, .allocate 2]

@[simp] theorem headerCode_size (width : Nat) : (headerCode width).size = 3 := rfl

def HeaderAt (program : Program width 8) (entry : Nat) : Prop :=
  ∀ phase : Fin 3, program[entry + phase.val]? = some ((headerCode width)[phase.val])

def headerFinished (state : Controller.Cost.State width 8) : Controller.Cost.State width 8 :=
  let s1 := { state.advance with heap := state.heap.push (state.reg 1) }
  let s2 := { s1.advance with heap := s1.heap.push (state.reg 3) }
  { s2.advance with heap := s2.heap.push (state.reg 2) }

/-- The selected tag/head/count header is really appended to the heap. -/
theorem header_execution (program : Program width 8) (entry : Nat)
    (present : HeaderAt program entry) (state : Controller.Cost.State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 3 < 2 ^ width) (heapFits : state.heap.size + 3 < 2 ^ width) :
    Execution program state (headerFinished state) 3 (state.liveWords + 3) := by
  let s1 := { state.advance with heap := state.heap.push (state.reg 1) }
  let s2 := { s1.advance with heap := s1.heap.push (state.reg 3) }
  let s3 := { s2.advance with heap := s2.heap.push (state.reg 2) }
  have p1 : s1.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa [s2, Controller.Cost.State.put, Nat.add_assoc] using advance_position s1 (entry + 1) p1 (by omega)
  have t1 : programStep program state = some s1 := by
    have read : program[state.pc.val]? = some (.allocate 1) := by
      rw [position, word_val (width := width) entry (by omega)]
      simpa [headerCode] using present 0
    unfold programStep
    rw [read]
    change step (.allocate 1) state = _
    simp [step, running, s1, show state.heap.size < 2 ^ width by omega]
  have t2 : programStep program s1 = some s2 := by
    have read : program[s1.pc.val]? = some (.allocate 3) := by
      rw [p1, word_val (width := width) (entry + 1) (by omega)]
      simpa [headerCode] using present 1
    unfold programStep
    rw [read]
    change step (.allocate 3) s1 = _
    have fits : s1.heap.size < 2 ^ width := by simp only [s1, Array.size_push]; omega
    simp [step, s2, s1, Controller.Cost.State.advance, running, show state.heap.size + 1 < 2 ^ width by omega]
  have t3 : programStep program s2 = some s3 := by
    have read : program[s2.pc.val]? = some (.allocate 2) := by
      rw [p2, word_val (width := width) (entry + 2) (by omega)]
      simpa [headerCode] using present 2
    unfold programStep
    rw [read]
    change step (.allocate 2) s2 = _
    have fits : s2.heap.size < 2 ^ width := by simp only [s2, s1, Array.size_push]; omega
    simp [step, s3, s2, s1, Controller.Cost.State.advance, running, show state.heap.size + 1 + 1 < 2 ^ width by omega]
  have trace := Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s3)))
  have l1 : s1.liveWords = state.liveWords + 1 := by simp only [s1, Controller.Cost.State.advance, Controller.Cost.State.liveWords, Array.size_push]; omega
  have l2 : s2.liveWords = state.liveWords + 2 := by simp only [s2, s1, Controller.Cost.State.advance, Controller.Cost.State.liveWords, Array.size_push]; omega
  have l3 : s3.liveWords = state.liveWords + 3 := by simp only [s3, s2, s1, Controller.Cost.State.advance, Controller.Cost.State.liveWords, Array.size_push]; omega
  have peak0 : max state.liveWords (state.liveWords + 3) = state.liveWords + 3 := Nat.max_eq_right (by omega)
  have peak1 : max (state.liveWords + 1) (state.liveWords + 3) = state.liveWords + 3 := Nat.max_eq_right (by omega)
  have peak2 : max (state.liveWords + 2) (state.liveWords + 3) = state.liveWords + 3 := Nat.max_eq_right (by omega)
  change Execution program state s3 3 (state.liveWords + 3)
  simpa only [l1, l2, l3, peak0, peak1, peak2] using trace

/-- The next record cursor is computed from the actual count-cell address and
actual body visit counter. Its only immediate is the persistent cursor header. -/
def cursorUpdateCode (width recordCursorHeader : Nat) : Program width 8 :=
  #[.add 1 7 5, .add 1 1 4, .constant 0 (word width recordCursorHeader), .store 0 1]

@[simp] theorem cursorUpdateCode_size (width recordCursorHeader : Nat) :
    (cursorUpdateCode width recordCursorHeader).size = 4 := rfl


def CursorUpdateAt (program : Program width 8) (entry header : Nat) : Prop :=
  ∀ phase : Fin 4, program[entry + phase.val]? = some ((cursorUpdateCode width header)[phase.val])

def cursorUpdateFinished (state : Controller.Cost.State width 8)
    (header countAddress count : Nat) (bound : header < state.heap.size) : Controller.Cost.State width 8 :=
  let a := state.advance.put 1 (word width (countAddress + 1))
  let b := a.advance.put 1 (word width (countAddress + 1 + count))
  let c := b.advance.put 0 (word width header)
  { c.advance with heap := state.heap.set header (word width (countAddress + 1 + count)) bound }

/-- The record endpoint is computed from the live count address and live visit
counter, and stored through the persistent physical cursor header. -/
theorem cursor_update_execution (program : Program width 8) (entry header countAddress count : Nat)
    (present : CursorUpdateAt program entry header) (state : Controller.Cost.State width 8)
    (bound : header < state.heap.size) (position : state.pc = word width entry)
    (address : state.reg 7 = word width countAddress)
    (counter : state.reg 4 = word width count) (one : state.reg 5 = word width 1)
    (running : state.halted = false) (capacity : entry + 4 < 2 ^ width)
    (endFits : countAddress + 1 + count < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (cursorUpdateFinished state header countAddress count bound) 4 state.liveWords := by
  let a := state.advance.put 1 (word width (countAddress + 1))
  let b := a.advance.put 1 (word width (countAddress + 1 + count))
  let c := b.advance.put 0 (word width header)
  let final := cursorUpdateFinished state header countAddress count bound
  have apc : a.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have bpc : b.pc = word width (entry + 2) := by
    simpa [b, Controller.Cost.State.put, Nat.add_assoc] using advance_position a (entry + 1) apc (by omega)
  have cpc : c.pc = word width (entry + 3) := by
    simpa [c, Controller.Cost.State.put, Nat.add_assoc] using advance_position b (entry + 2) bpc (by omega)
  have t0 : programStep program state = some a := by
    have read : program[state.pc.val]? = some (.add 1 7 5) := by
      rw [position, word_val (width := width) entry (by omega)]
      simpa [cursorUpdateCode] using present 0
    unfold programStep
    rw [read]
    change step (.add 1 7 5) state = _
    simp [step, a, running, address, one,
      word_val (width := width) countAddress (by omega), word_val (width := width) 1 (by omega)]
  have t1 : programStep program a = some b := by
    have read : program[a.pc.val]? = some (.add 1 1 4) := by
      rw [apc, word_val (width := width) (entry + 1) (by omega)]
      simpa [cursorUpdateCode] using present 1
    unfold programStep
    rw [read]
    change step (.add 1 1 4) a = _
    simp [step, b, a, Controller.Cost.State.put, Controller.Cost.State.advance, running, counter,
      word_val (width := width) (countAddress + 1) (by omega), word_val (width := width) count (by omega)]
  have t2 : programStep program b = some c := by
    have read : program[b.pc.val]? = some (.constant 0 (word width header)) := by
      rw [bpc, word_val (width := width) (entry + 2) (by omega)]
      simpa [cursorUpdateCode] using present 2
    unfold programStep
    rw [read]
    change step (.constant 0 (word width header)) b = _
    simp [step, c, b, a, Controller.Cost.State.put, Controller.Cost.State.advance, running]
  have t3 : programStep program c = some final := by
    have read : program[c.pc.val]? = some (.store 0 1) := by
      rw [cpc, word_val (width := width) (entry + 3) (by omega)]
      simpa [cursorUpdateCode] using present 3
    unfold programStep
    rw [read]
    change step (.store 0 1) c = _
    have cursorAddress : (c.reg 0).val = header := by
      simp [c, Controller.Cost.State.put, word_val (width := width) header (bound.trans heapFits)]
    have value : c.reg 1 = word width (countAddress + 1 + count) := by
      simp [c, b, Controller.Cost.State.put, Controller.Cost.State.advance]
    have storeBound : header < c.heap.size := bound
    simp only [step, show c.halted = false from running, Bool.false_eq_true, ite_false,
      cursorAddress, dite_eq_left storeBound, value]
    rfl
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl final))))
  simpa [final, cursorUpdateFinished, c, b, a, Controller.Cost.State.liveWords,
    Controller.Cost.State.put, Controller.Cost.State.advance] using trace

end Controller.Horn.RuleCopy
