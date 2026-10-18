module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexScanCold
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-! The positive scratch buffer becomes a fixed-capacity FIFO. A fetched guard
checks the variable-off cell; its successful branch marks the variable before
writing the queue slot. Original rule and incidence-link storage is untouched. -/
namespace Controller.Horn.WorklistMark
open Controller.Cost Controller.Horn.WorklistStorage
variable {width n : Nat}

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

def queueStart (base : Nat) : Nat := base + 3 * n + 4

def code (width entry exit : Nat) : Program width 8 :=
  #[.load 4 3, .branchZero 4 (word width (entry + 3)), .branchZero 2 (word width exit),
    .store 3 5, .store 0 1, .add 0 0 5, .branchZero 2 (word width exit)]

@[simp] theorem code_size (width entry exit : Nat) : (code width entry exit).size = 7 := rfl
@[simp] theorem code_words (width entry exit : Nat) : programWords (code width entry exit) = 28 := rfl

def At (program : Program width 8) (entry exit : Nat) : Prop :=
  ∀ phase : Fin 7, program[entry + phase.val]? = (code width entry exit)[phase.val]?

structure Stored (enqueued : List (Fin n)) (base : Nat) (heap : Array (Word width)) : Prop where
  nodup : enqueued.Nodup
  fits : base + 4 * n + 4 ≤ heap.size
  flags : ∀ label : Fin n,
    heap[offAddress base label]'(by have := label.isLt; unfold offAddress; omega) =
      word width (if label ∈ enqueued then 1 else 0)
  queue : Controller.Horn.ResetTouched.LabelsStored enqueued (queueStart (n := n) base) heap

/-- Every successful mark corresponds to a distinct finite channel, so the
preallocated n-slot FIFO suffices for all future enqueues. -/
theorem enqueue_bound (enqueued : List (Fin n)) (unique : enqueued.Nodup) : enqueued.length ≤ n := by
  simpa using unique.length_le_card

theorem fresh_enqueue_bound (enqueued : List (Fin n)) (unique : enqueued.Nodup)
    (label : Fin n) (fresh : label ∉ enqueued) : enqueued.length + 1 ≤ n := by
  have distinct : (enqueued ++ [label]).Nodup := by
    simpa only [List.concat_eq_append] using List.Nodup.concat fresh unique
  simpa using enqueue_bound _ distinct

/-- Marking and enqueueing change exactly the off cell and the unused next FIFO
cell; this low-scratch frame preserves every original rule and link cell. -/
def committedHeap (state : State width 8) (base : Nat) (enqueued : List (Fin n)) (label : Fin n)
    (offBound : offAddress base label < state.heap.size)
    (queueBound : queueStart (n := n) base + enqueued.length < state.heap.size) : Array (Word width) :=
  (state.heap.set (offAddress base label) (word width 1) offBound).set
    (queueStart (n := n) base + enqueued.length) (word width label.val) (by simpa using queueBound)

@[simp] theorem committed_size (state : State width 8) (base : Nat) (enqueued : List (Fin n))
    (label : Fin n) (offBound : offAddress base label < state.heap.size)
    (queueBound : queueStart (n := n) base + enqueued.length < state.heap.size) :
    (committedHeap state base enqueued label offBound queueBound).size = state.heap.size := by
  simp [committedHeap]

theorem committed_high_frame (state : State width 8) (base : Nat) (enqueued : List (Fin n))
    (label : Fin n) (unique : enqueued.Nodup) (fresh : label ∉ enqueued)
    (offBound : offAddress base label < state.heap.size)
    (queueBound : queueStart (n := n) base + enqueued.length < state.heap.size)
    (position : Nat) (above : base + 5 * n + 4 ≤ position) :
    (committedHeap state base enqueued label offBound queueBound)[position]? = state.heap[position]? := by
  have tail := fresh_enqueue_bound enqueued unique label fresh
  have offDifferent : offAddress base label ≠ position := by have := label.isLt; unfold offAddress; omega
  have queueDifferent : queueStart (n := n) base + enqueued.length ≠ position := by unfold queueStart; omega
  simp [committedHeap, Array.getElem?_set, offDifferent, queueDifferent]

/-- The fetched guard reads the actual off word. A successful guard enters the
mark store; queue insertion follows that store in the same program. -/
theorem fresh_guard (program : Program width 8) (entry exit base : Nat) (state : State width 8)
    (label : Fin n) (present : At program entry exit)
    (offBound : offAddress base label < state.heap.size)
    (off : state.heap[offAddress base label]'offBound = word width 0)
    (held : state.reg 3 = word width (offAddress base label))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 7 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    let loaded := state.advance.put 4 (word width 0)
    let final := Controller.Horn.RuleDispatch.branchFinished loaded 4 (entry + 3)
    Execution program state final 2 state.liveWords ∧ final.pc = word width (entry + 3) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output := by
  dsimp only
  let loaded := state.advance.put 4 (word width 0)
  have loadAt : program[entry]? = some (.load 4 3) := by simpa [code] using present ⟨0, by decide⟩
  have branchAt : program[entry + 1]? = some (.branchZero 4 (word width (entry + 3))) := by
    simpa [code] using present ⟨1, by decide⟩
  have first : programStep program state = some loaded := by
    unfold programStep
    rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega), loadAt]
    simp [step, held, loaded, running, offBound, off,
      show (word width (offAddress base label)).val = offAddress base label from Nat.mod_eq_of_lt (by omega)]
  have nextPosition : loaded.pc = word width (entry + 1) := by
    simp [loaded, State.put, State.advance, position,
      show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have second := Controller.Horn.RuleDispatch.branch_execution program (entry + 1) (entry + 3) 4
    branchAt loaded nextPosition (by simpa [loaded, State.put, State.advance] using running) (by omega)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame loaded 4 (entry + 3)
  refine ⟨by simpa [loaded, State.liveWords, State.put, State.advance] using Execution.cons first second, ?_,
    frame.2.1, frame.2.2.1, frame.2.2.2.1⟩
  simp [Controller.Horn.RuleDispatch.branchFinished, loaded, State.put, word]

/-- The successful path stores the off mark before the FIFO label, increments
the physical tail and returns. No allocation or caller stack change occurs. -/
theorem commit_execution (program : Program width 8) (entry exit base : Nat)
    (enqueued : List (Fin n)) (label : Fin n) (state : State width 8)
    (present : At program entry exit)
    (offBound : offAddress base label < state.heap.size)
    (queueBound : queueStart (n := n) base + enqueued.length < state.heap.size)
    (offHeld : state.reg 3 = word width (offAddress base label))
    (tailHeld : state.reg 0 = word width (queueStart (n := n) base + enqueued.length))
    (labelHeld : state.reg 1 = word width label.val)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width (entry + 3)) (running : state.halted = false)
    (capacity : entry + 7 < 2 ^ width) (exitFits : exit < 2 ^ width)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = committedHeap state base enqueued label offBound queueBound ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width (queueStart (n := n) base + enqueued.length + 1) ∧
      final.pc = word width exit ∧ final.halted = false := by
  let offAddressWord := offAddress base label
  let tailAddress := queueStart (n := n) base + enqueued.length
  let marked : State width 8 := { state.advance with heap := state.heap.set offAddressWord (word width 1) offBound }
  let queued : State width 8 := { marked.advance with
    heap := marked.heap.set tailAddress (word width label.val) (by simpa [marked] using queueBound) }
  let advanced := queued.advance.put 0 (word width (tailAddress + 1))
  let final := Controller.Horn.RuleDispatch.branchFinished advanced 2 exit
  have storeMark : program[entry + 3]? = some (.store 3 5) := by simpa [code] using present ⟨3, by decide⟩
  have storeQueue : program[entry + 4]? = some (.store 0 1) := by simpa [code] using present ⟨4, by decide⟩
  have increment : program[entry + 5]? = some (.add 0 0 5) := by simpa [code] using present ⟨5, by decide⟩
  have returnAt : program[entry + 6]? = some (.branchZero 2 (word width exit)) := by simpa [code] using present ⟨6, by decide⟩
  have pcFits (phase : Nat) (bound : phase ≤ 7) : entry + phase < 2 ^ width := by omega
  have addrFits : offAddressWord < 2 ^ width := by dsimp [offAddressWord]; omega
  have tailFits : tailAddress < 2 ^ width := by dsimp [tailAddress]; omega
  have oneFits : 1 < 2 ^ width := by omega
  have markedPosition : marked.pc = word width (entry + 4) := by
    simp [marked, State.advance, position, word_val (width := width) (entry + 3) (pcFits 3 (by decide)), Nat.add_assoc]
  have queuedPosition : queued.pc = word width (entry + 5) := by
    simp [queued, State.advance, markedPosition, word_val (width := width) (entry + 4) (pcFits 4 (by decide)), Nat.add_assoc]
  have advancedPosition : advanced.pc = word width (entry + 6) := by
    simp [advanced, State.put, State.advance, queuedPosition, word_val (width := width) (entry + 5) (pcFits 5 (by decide)), Nat.add_assoc]
  have first : programStep program state = some marked := by
    unfold programStep
    rw [position, show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (pcFits 3 (by decide)), storeMark]
    simp [step, running, offBound, offHeld, one, marked,
      word_val (width := width) (offAddress base label) addrFits, offAddressWord]
  have second : programStep program marked = some queued := by
    unfold programStep
    rw [markedPosition, show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (pcFits 4 (by decide)), storeQueue]
    simp [step, running, queueBound, marked, queued, tailHeld, labelHeld, State.advance,
      word_val (width := width) (queueStart (n := n) base + enqueued.length) tailFits, tailAddress]
  have third : programStep program queued = some advanced := by
    unfold programStep
    rw [queuedPosition, show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (pcFits 5 (by decide)), increment]
    simp [step, running, queued, marked, advanced, State.advance, State.put, tailHeld, one,
      word_val (width := width) (queueStart (n := n) base + enqueued.length) tailFits,
      word_val (width := width) 1 oneFits, tailAddress]
  have fourth := Controller.Horn.RuleDispatch.branch_execution program (entry + 6) exit 2 returnAt advanced
    advancedPosition (by simpa [advanced, queued, marked, State.put, State.advance] using running) (pcFits 6 (by decide))
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame advanced 2 exit
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [final, advanced, queued, marked, State.liveWords, State.put, State.advance] using
      Execution.cons first (Execution.cons second (Execution.cons third fourth))
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).heap = _
    rw [frame.2.1]
    rfl
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).heap.size = _
    rw [frame.2.1]
    simp [advanced, queued, marked, State.put, State.advance]
  · exact frame.2.2.1
  · exact frame.2.2.2.1
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).reg 0 = _
    rw [frame.1]
    simp [advanced, State.put, tailAddress]
  · simp [final, Controller.Horn.RuleDispatch.branchFinished, advanced, queued, marked,
      State.put, State.advance, zero, word]
  · change (Controller.Horn.RuleDispatch.branchFinished advanced 2 exit).halted = false
    rw [frame.2.2.2.2.1]
    exact running

/-- The physical off flags and FIFO entries represent precisely the newly
marked prefix, so a later guard for the same label cannot enqueue it again. -/
theorem committed_stored (enqueued : List (Fin n)) (base : Nat) (state : State width 8)
    (stored : Stored enqueued base state.heap) (label : Fin n) (fresh : label ∉ enqueued)
    (offBound : offAddress base label < state.heap.size)
    (queueBound : queueStart (n := n) base + enqueued.length < state.heap.size) :
    Stored (enqueued ++ [label]) base (committedHeap state base enqueued label offBound queueBound) := by
  have unique : (enqueued ++ [label]).Nodup := by
    simpa only [List.concat_eq_append] using List.Nodup.concat fresh stored.nodup
  have queueAfterOff : base + 2 * n ≤ queueStart (n := n) base := by unfold queueStart; omega
  refine ⟨unique, by simpa only [committed_size] using stored.fits, ?_, ?_⟩
  · intro query
    have queryBound : offAddress base query < state.heap.size := by
      have := stored.fits; have := query.isLt; unfold offAddress; omega
    have queueDifferent : queueStart (n := n) base + enqueued.length ≠ offAddress base query := by
      have := query.isLt; unfold offAddress queueStart; omega
    by_cases same : query = label
    · subst query
      simp [committedHeap, Array.getElem_set, queueDifferent]
    · have different : offAddress base label ≠ offAddress base query := by
        intro equal; apply same; apply Fin.ext; unfold offAddress at equal; omega
      simpa [committedHeap, Array.getElem_set, queueDifferent, different, same] using stored.flags query
  · have heapFits := stored.fits
    have totalBound := fresh_enqueue_bound enqueued stored.nodup label fresh
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, committed_size]
      unfold queueStart
      omega
    · intro index
      by_cases old : index.val < enqueued.length
      · have positionDifferent : queueStart (n := n) base + enqueued.length ≠ queueStart (n := n) base + index.val := by omega
        have offDifferent : offAddress base label ≠ queueStart (n := n) base + index.val := by
          have := label.isLt; unfold offAddress queueStart; omega
        simpa [committedHeap, Array.getElem_set, positionDifferent, offDifferent, (Nat.ne_of_lt old).symm,
          List.getElem_append_left old] using stored.queue.entry ⟨index.val, old⟩
      · have position : index.val = enqueued.length := by have := index.isLt; simp only [List.length_append, List.length_singleton] at this; omega
        have value : (enqueued ++ [label])[index.val] = label := by
          rw [List.getElem_append_right (show enqueued.length ≤ index.val by omega)]
          simp [position]
        simp [committedHeap, Array.getElem_set, position, value]

end Controller.Horn.WorklistMark
