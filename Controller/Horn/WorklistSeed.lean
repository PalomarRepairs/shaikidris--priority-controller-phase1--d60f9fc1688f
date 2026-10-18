module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistFIFO
public import Controller.Horn.WorklistEnqueue

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The initial scan visits each original packed record once. Zero-body negative
rules seed the variable FIFO; zero-body positive rules reach the conflict entry. -/
namespace Controller.Horn.WorklistSeed
open Controller.Cost Controller.Horn.WorklistStorage Controller.Horn.WorklistMark
open Controller.Horn.WorklistBucketReady
variable {width n : Nat}

/-- Tail initialization uses the retired scratch header and the preallocated FIFO. -/
def setupCode (width base scan : Nat) : Program width 8 :=
  #[.constant 3 (word width (tailSlot (n := n) base)),
    .constant 0 (word width (queueStart (n := n) base)), .store 3 0,
    .branchZero 2 (word width scan)]

/-- The cold endpoint supplies the original endpoint in global source header
zero. Copy it into the seed comparison header even when the original formula
has no rows, and explicitly initialize the cursor and decrement register. -/
def coldSetupCode (width base recordStart scan : Nat) : Program width 8 :=
  #[.constant 1 (word width recordStart),
    .constant 6 (word width (2 ^ width - 1)),
    .constant 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := n) base)),
    .load 0 2, .store 3 0] ++ setupCode (n := n) width base scan

@[simp] theorem cold_setup_size (width base recordStart scan : Nat) :
    (coldSetupCode (n := n) width base recordStart scan).size = 9 := by
  simp [coldSetupCode, setupCode]

/-- The count load selects the ready adapter only for an original empty support.
The successor cursor is saved before the adapter reuses the working registers. -/
def code (width base entry done conflict : Nat) : Program width 8 :=
  #[.constant 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := n) base)),
    .load 4 3, .xor 3 1 4, .branchZero 3 (word width done),
    .add 3 1 5, .add 3 3 5, .load 7 3, .branchZero 7 (word width (entry + 13)),
    .add 1 1 7, .add 1 1 5, .add 1 1 5, .add 1 1 5,
    .branchZero 2 (word width entry),
    .copy 4 1, .add 4 4 5, .add 4 4 5, .add 4 4 5] ++
  Controller.Horn.WorklistBucketReady.code (n := n) width base (entry + 17) (entry + 45) conflict (entry + 43) ++
  #[.copy 1 0, .branchZero 2 (word width entry),
    .copy 1 4, .branchZero 2 (word width entry)]

@[simp] theorem setup_size (width base scan : Nat) :
    (setupCode (n := n) width base scan).size = 4 := rfl
@[simp] theorem code_size (width base entry done conflict : Nat) :
    (code (n := n) width base entry done conflict).size = 47 := by
  simp [code]

def At (program : Program width 8) (base entry done conflict : Nat) : Prop :=
  ∀ phase : Fin 47, program[entry + phase.val]? =
    (code (n := n) width base entry done conflict)[phase.val]?

/-- The original-row endpoint comparison is a fetched subprogram of the seed scan. -/
theorem test_at (program : Program width 8) (base entry done conflict : Nat)
    (present : At (n := n) program base entry done conflict) :
    Controller.Horn.IndexScan.TestAt program entry
      (Controller.Horn.WorklistFIFO.headSlot (n := n) base) done 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [code] using present ⟨0, by decide⟩
  · simpa [code] using present ⟨1, by decide⟩
  · simpa [code] using present ⟨2, by decide⟩
  · simpa [code] using present ⟨3, by decide⟩

/-- Ready firing/enqueue executes the accepted fixed adapter inside the same
seed program; both return addresses remain in that program. -/
theorem ready_at (program : Program width 8) (base entry done conflict : Nat)
    (present : At (n := n) program base entry done conflict) :
    Controller.Horn.WorklistBucketReady.At (n := n) program base (entry + 17)
      (entry + 45) conflict (entry + 43) := by
  intro phase
  fin_cases phase
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨17, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨18, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨19, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨20, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨21, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨22, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨23, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨24, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨25, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨26, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨27, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨28, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨29, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨30, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨31, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨32, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨33, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨34, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨35, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨36, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨37, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨38, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨39, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨40, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨41, by decide⟩
  · simpa [code, Controller.Horn.WorklistBucketReady.code, Nat.add_assoc] using present ⟨42, by decide⟩

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, word_val entry fits, present]
  rfl

private theorem advance_pc (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word_val entry fits]

/-- Four fetched instructions initialize the FIFO tail without allocating or
changing original records, then enter the original-row seed scan. -/
theorem setup_execution (program : Program width 8) (base entry scan : Nat)
    (state : State width 8)
    (present : ∀ phase : Fin 4, program[entry + phase.val]? =
      (setupCode (n := n) width base scan)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0)
    (capacity : entry + 4 < 2 ^ width)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = state.heap.set (tailSlot (n := n) base)
        (word width (queueStart (n := n) base)) tailBound ∧
      final.pc = word width scan ∧ final.halted = false ∧
      final.reg 1 = state.reg 1 ∧ final.reg 2 = state.reg 2 ∧
      final.reg 5 = state.reg 5 ∧ final.reg 6 = state.reg 6 ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output := by
  let first := state.advance.put 3 (word width (tailSlot (n := n) base))
  let second := first.advance.put 0 (word width (queueStart (n := n) base))
  let third : State width 8 := { second.advance with
    heap := state.heap.set (tailSlot (n := n) base) (word width (queueStart (n := n) base)) tailBound }
  let final : State width 8 := { third.advance with pc := word width scan }
  have pc1 : first.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : second.pc = word width (entry + 2) := by
    simpa [second, State.put, Nat.add_assoc] using advance_pc first (entry + 1) pc1 (by omega)
  have pc3 : third.pc = word width (entry + 3) := by
    simpa [third, Nat.add_assoc] using advance_pc second (entry + 2) pc2 (by omega)
  have step1 : programStep program state = some first := by
    rw [fetched program state entry (.constant 3 (word width (tailSlot (n := n) base))) position
      (by omega) (by simpa [setupCode] using present ⟨0, by decide⟩)]
    simp [step, running, first]
  have step2 : programStep program first = some second := by
    rw [fetched program first (entry + 1) (.constant 0 (word width (queueStart (n := n) base))) pc1
      (by omega) (by simpa [setupCode] using present ⟨1, by decide⟩)]
    simp [step, first, second, State.put, State.advance, running]
  have step3 : programStep program second = some third := by
    rw [fetched program second (entry + 2) (.store 3 0) pc2 (by omega)
      (by simpa [setupCode] using present ⟨2, by decide⟩)]
    have addressFits : tailSlot (n := n) base < 2 ^ width := by omega
    simp [step, first, second, third, State.put, State.advance, running,
      word_val (tailSlot (n := n) base) addressFits, tailBound]
  have step4 : programStep program third = some final := by
    rw [fetched program third (entry + 3) (.branchZero 2 (word width scan)) pc3 (by omega)
      (by simpa [setupCode] using present ⟨3, by decide⟩)]
    simp [step, first, second, third, final, State.put, State.advance, running, zero, word]
  refine ⟨final, ?_, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simpa [first, second, third, final, State.put, State.advance, State.liveWords] using
      Execution.cons step1 (Execution.cons step2 (Execution.cons step3
        (Execution.cons step4 (Execution.refl final))))
  all_goals simp [first, second, third, final, State.put, State.advance]

/-- The seed scanner loads the count from the original packed record, rather
than from an auxiliary incidence table or queue marks. -/
theorem count_load_execution (program : Program width 8) (entry row count : Nat)
    (rule : Controller.Horn.Worklist.Rule (Fin n)) (fired : Bool) (state : State width 8)
    (stored : MutableStored rule row count fired state.heap)
    (present0 : program[entry]? = some (.add 3 1 5))
    (present1 : program[entry + 1]? = some (.add 3 3 5))
    (present2 : program[entry + 2]? = some (.load 7 3))
    (held : state.reg 1 = word width row) (one : state.reg 5 = word width 1)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 3 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.reg 7 = word width count ∧ final.reg 1 = state.reg 1 ∧
      final.reg 2 = state.reg 2 ∧ final.reg 5 = state.reg 5 ∧ final.reg 6 = state.reg 6 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 3) ∧ final.halted = false := by
  have countBound : row + 2 < state.heap.size := by have := stored.fits; omega
  have rowFits : row < 2 ^ width := by omega
  have addressFits : row + 2 < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  let first := state.advance.put 3 (word width (row + 1))
  let second := first.advance.put 3 (word width (row + 2))
  let final := second.advance.put 7 (word width count)
  have pc1 : first.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : second.pc = word width (entry + 2) := by
    simpa [second, State.put, Nat.add_assoc] using advance_pc first (entry + 1) pc1 (by omega)
  have firstStep : programStep program state = some first := by
    rw [fetched program state entry (.add 3 1 5) position (by omega) present0]
    simp [step, running, held, one, word_val row rowFits, word_val 1 oneFits, first]
  have secondStep : programStep program first = some second := by
    rw [fetched program first (entry + 1) (.add 3 3 5) pc1 (by omega) present1]
    have firstAddressFits : row + 1 < 2 ^ width := by omega
    simp [step, first, second, State.put, State.advance, running, one,
      word_val (row + 1) firstAddressFits, word_val 1 oneFits, Nat.add_assoc]
  have thirdStep : programStep program second = some final := by
    rw [fetched program second (entry + 2) (.load 7 3) pc2 (by omega) present2]
    simp [step, first, second, final, State.put, State.advance, running,
      word_val (row + 2) addressFits, countBound, stored.countValue]
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, running⟩
  · simpa [first, second, final, State.put, State.advance, State.liveWords] using
      Execution.cons firstStep (Execution.cons secondStep (Execution.cons thirdStep (Execution.refl final)))
  · simp [first, second, final, State.put, State.advance]
  · simp [first, second, final, State.put, State.advance]
  · simp [first, second, final, State.put, State.advance]
  · simp [first, second, final, State.put, State.advance]
  · simp [first, second, final, State.put, State.advance]
  · simpa [final, State.put, Nat.add_assoc] using advance_pc second (entry + 2) pc2 (by omega)

/-- The ready and skip adapters return their saved original-row successor
through two fetched instructions on the same machine state. -/
theorem cursor_return_execution (program : Program width 8) (entry scan : Nat)
    (source : Fin 8) (state : State width 8)
    (copyAt : program[entry]? = some (.copy 1 source))
    (branchAt : program[entry + 1]? = some (.branchZero 2 (word width scan)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (capacity : entry + 2 < 2 ^ width) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.reg 1 = state.reg source ∧
      (∀ register : Fin 8, register ≠ 1 → final.reg register = state.reg register) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width scan ∧ final.halted = false := by
  let copied := state.advance.put 1 (state.reg source)
  let final : State width 8 := { copied.advance with pc := word width scan }
  have pc1 : copied.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have first : programStep program state = some copied := by
    rw [fetched program state entry (.copy 1 source) position (by omega) copyAt]
    simp [step, copied, running]
  have second : programStep program copied = some final := by
    rw [fetched program copied (entry + 1) (.branchZero 2 (word width scan)) pc1 (by omega) branchAt]
    simp [step, copied, final, State.put, State.advance, running, zero, word]
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, rfl, running⟩
  · simpa [copied, final, State.put, State.advance, State.liveWords] using
      Execution.cons first (Execution.cons second (Execution.refl final))
  · simp [copied, final, State.put, State.advance]
  · intro register different
    simp [copied, final, State.put, State.advance, different]

/-- A nonempty original row advances by its actual stored support length and
three record headers. This is the single initial scan, not a propagation rescan. -/
theorem nonzero_advance_execution (program : Program width 8) (entry scan row count : Nat)
    (state : State width 8)
    (present : ∀ phase : Fin 5, program[entry + phase.val]? =
      (#[.add 1 1 7, .add 1 1 5, .add 1 1 5, .add 1 1 5,
        .branchZero 2 (word width scan)] : Program width 8)[phase.val]?)
    (rowHeld : state.reg 1 = word width row) (countHeld : state.reg 7 = word width count)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 5 < 2 ^ width) (successorFits : row + 3 + count < 2 ^ width) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.reg 1 = word width (row + 3 + count) ∧
      (∀ register : Fin 8, register ≠ 1 → final.reg register = state.reg register) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width scan ∧ final.halted = false := by
  let first := state.advance.put 1 (word width (row + count))
  let second := first.advance.put 1 (word width (row + count + 1))
  let third := second.advance.put 1 (word width (row + count + 2))
  let fourth := third.advance.put 1 (word width (row + count + 3))
  let final : State width 8 := { fourth.advance with pc := word width scan }
  have pc1 : first.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : second.pc = word width (entry + 2) := by
    simpa [second, State.put, Nat.add_assoc] using advance_pc first (entry + 1) pc1 (by omega)
  have pc3 : third.pc = word width (entry + 3) := by
    simpa [third, State.put, Nat.add_assoc] using advance_pc second (entry + 2) pc2 (by omega)
  have pc4 : fourth.pc = word width (entry + 4) := by
    simpa [fourth, State.put, Nat.add_assoc] using advance_pc third (entry + 3) pc3 (by omega)
  have rowFits : row < 2 ^ width := by omega
  have countFits : count < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have step1 : programStep program state = some first := by
    rw [fetched program state entry (.add 1 1 7) position (by omega)
      (by simpa using present ⟨0, by decide⟩)]
    simp [step, running, rowHeld, countHeld, word_val row rowFits, word_val count countFits, first]
  have step2 : programStep program first = some second := by
    rw [fetched program first (entry + 1) (.add 1 1 5) pc1 (by omega)
      (by simpa using present ⟨1, by decide⟩)]
    have valueFits : row + count < 2 ^ width := by omega
    simp [step, first, second, State.put, State.advance, running, one,
      word_val (row + count) valueFits, word_val 1 oneFits]
  have step3 : programStep program second = some third := by
    rw [fetched program second (entry + 2) (.add 1 1 5) pc2 (by omega)
      (by simpa using present ⟨2, by decide⟩)]
    have valueFits : row + (count + 1) < 2 ^ width := by omega
    simp [step, first, second, third, State.put, State.advance, running, one,
      word_val (row + (count + 1)) valueFits, word_val 1 oneFits, Nat.add_assoc]
  have step4 : programStep program third = some fourth := by
    rw [fetched program third (entry + 3) (.add 1 1 5) pc3 (by omega)
      (by simpa using present ⟨3, by decide⟩)]
    have valueFits : row + (count + 2) < 2 ^ width := by omega
    simp [step, first, second, third, fourth, State.put, State.advance, running, one,
      word_val (row + (count + 2)) valueFits, word_val 1 oneFits, Nat.add_assoc]
  have step5 : programStep program fourth = some final := by
    rw [fetched program fourth (entry + 4) (.branchZero 2 (word width scan)) pc4 (by omega)
      (by simpa using present ⟨4, by decide⟩)]
    simp [step, first, second, third, fourth, final, State.put, State.advance, running, zero, word]
  refine ⟨final, ?_, ?_, ?_, rfl, rfl, rfl, rfl, running⟩
  · simpa [first, second, third, fourth, final, State.put, State.advance, State.liveWords] using
      Execution.cons step1 (Execution.cons step2 (Execution.cons step3
        (Execution.cons step4 (Execution.cons step5 (Execution.refl final)))))
  · simp [first, second, third, fourth, final, State.put, State.advance, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  · intro register different
    simp [first, second, third, fourth, final, State.put, State.advance, different]

/-- Forced queue labels are false in every model of the original compiled rows. -/
def QueueForced (clauses : List (Controller.CNF.Clause (Fin n))) (queue : List (Fin n)) : Prop :=
  ∀ assignment : Fin n → Bool,
    (∀ index : Fin clauses.length,
      (Controller.Horn.Worklist.compileClause clauses[index.val]).Holds assignment) →
    ∀ label ∈ queue, assignment label = false

/-- Enabled count-zero rows already scanned have their actual fired tag cleared. -/
def SeedComplete (clauses : List (Controller.CNF.Clause (Fin n)))
    (scanned : Nat) (fired : Fin clauses.length → Bool) : Prop :=
  ∀ index : Fin clauses.length, index.val < scanned →
    (Controller.Horn.Worklist.compileClause clauses[index.val]).enabled = true →
    (Controller.Horn.Worklist.compileClause clauses[index.val]).positives.length = 0 →
    fired index = true

/-- An empty original negative support forces its head without consulting pending
marks or changing any propagation count. -/
theorem empty_negative_forced (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Fin clauses.length) (head : Fin n) (labels : List (Fin n))
    (original : Controller.Horn.Worklist.compileClause clauses[index.val] = .negative head labels)
    (empty : labels.length = 0) (assignment : Fin n → Bool)
    (models : ∀ row : Fin clauses.length,
      (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment) :
    assignment head = false := by
  have holds := models index
  rw [original] at holds
  have nil : labels = [] := List.length_eq_zero_iff.mp empty
  simpa [Controller.Horn.Worklist.Rule.Holds, nil] using holds

/-- Mark-before-enqueue preserves the original-model forcing property. -/
theorem queue_after_forced (clauses : List (Controller.CNF.Clause (Fin n)))
    (queue : List (Fin n)) (head : Fin n) (forced : QueueForced clauses queue)
    (headForced : ∀ assignment : Fin n → Bool,
      (∀ index : Fin clauses.length,
        (Controller.Horn.Worklist.compileClause clauses[index.val]).Holds assignment) →
      assignment head = false) : QueueForced clauses (queueAfter queue head) := by
  intro assignment models label member
  by_cases stale : head ∈ queue
  · exact forced assignment models label (by simpa [queueAfter, stale] using member)
  · have cases : label ∈ queue ∨ label = head := by simpa [queueAfter, stale] using member
    rcases cases with old | same
    · exact forced assignment models label old
    · simpa [same] using headForced assignment models

/-- Empty positive rows are conflicts even when the formula has no variables. -/
theorem empty_positive_conflict (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Fin clauses.length) (labels : List (Fin n))
    (original : Controller.Horn.Worklist.compileClause clauses[index.val] = .positive labels)
    (empty : labels.length = 0) :
    ¬ ∃ assignment : Fin n → Bool, ∀ row : Fin clauses.length,
      (Controller.Horn.Worklist.compileClause clauses[row.val]).Holds assignment := by
  rintro ⟨assignment, models⟩
  have holds := models index
  rw [original] at holds
  have nil : labels = [] := List.length_eq_zero_iff.mp empty
  simpa [Controller.Horn.Worklist.Rule.Holds, nil] using holds

/-- Firing the current empty negative row completes exactly the next original
row prefix. Earlier fired tags are retained. -/
theorem seed_complete_fire (clauses : List (Controller.CNF.Clause (Fin n)))
    (index : Fin clauses.length) (fired : Fin clauses.length → Bool)
    (complete : SeedComplete clauses index.val fired) :
    SeedComplete clauses (index.val + 1) (fun other => if other = index then true else fired other) := by
  intro other before enabled empty
  by_cases same : other = index
  · simp only [same, ite_true]
  · have values : other.val ≠ index.val := fun eq => same (Fin.ext eq)
    have old : other.val < index.val := by omega
    simpa only [ite_eq_right same] using complete other old enabled empty

/-- The actual ready adapter fires an original empty negative record, preserves
all original counts and links, and extends the forced FIFO and completed prefix.
Counts here are the initial original support lengths; pending marks do not
participate in them. -/
theorem negative_seed_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry skip conflict nextEntry next : Nat) (program : Program width 8)
    (queue : List (Fin n)) (fired : Fin clauses.length → Bool)
    (index : Fin clauses.length) (head : Fin n) (labels : List (Fin n)) (state : State width 8)
    (original : Controller.Horn.Worklist.compileClause clauses[index.val] = .negative head labels)
    (empty : labels.length = 0) (unfired : fired index = false)
    (spine : Controller.Horn.WorklistPropagation.Spine clauses recordStart recordEnd base state.heap)
    (fifo : Stored queue base state.heap)
    (rows : ∀ other : Fin clauses.length,
      MutableStored (Controller.Horn.Worklist.compileClause clauses[other.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)
        (Controller.Horn.Worklist.compileClause clauses[other.val]).positives.length (fired other) state.heap)
    (forced : QueueForced clauses queue) (complete : SeedComplete clauses index.val fired)
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : Controller.Horn.WorklistBucketReady.At (n := n) program base entry skip conflict nextEntry)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[tailSlot (n := n) base]'tailBound = word width (queueStart (n := n) base + queue.length))
    (rowHeld : state.reg 1 = word width (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val))
    (nextHeld : state.reg 4 = word width next) (one : state.reg 5 = word width 1)
    (zero : state.reg 2 = word width 0) (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final (if head ∈ queue then 22 else 25) state.liveWords ∧
      Controller.Horn.WorklistPropagation.Spine clauses recordStart recordEnd base final.heap ∧
      Stored (queueAfter queue head) base final.heap ∧
      (∀ other : Fin clauses.length,
        MutableStored (Controller.Horn.Worklist.compileClause clauses[other.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart other.val)
          (Controller.Horn.Worklist.compileClause clauses[other.val]).positives.length
          (if other = index then true else fired other) final.heap) ∧
      QueueForced clauses (queueAfter queue head) ∧
      SeedComplete clauses (index.val + 1) (fun other => if other = index then true else fired other) ∧
      final.reg 0 = word width next ∧ final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.reg 6 = word width (2 ^ width - 1) ∧ final.heap.size = state.heap.size ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width nextEntry ∧ final.halted = false := by
  have countZero : (Controller.Horn.Worklist.compileClause clauses[index.val]).positives.length = 0 := by
    simpa only [original, Controller.Horn.Worklist.Rule.positives] using empty
  obtain ⟨final, trace, finalSpine, finalFifo, finalRows, nextValue, finalZero, finalOne,
      finalDecrement, size, stack, output, pc, live⟩ :=
    Controller.Horn.WorklistBucketFrame.negative_original_framed clauses recordStart recordEnd base entry skip conflict
      nextEntry next program queue (fun other => (Controller.Horn.Worklist.compileClause clauses[other.val]).positives.length)
      fired index head labels state original countZero unfired spine fifo rows separated present
      tailBound tailValue rowHeld nextHeld one zero decrement position running capacity room
  refine ⟨final, trace, finalSpine, finalFifo, finalRows, ?_, seed_complete_fire clauses index fired complete,
    nextValue, finalZero, finalOne, finalDecrement, size, stack, output, pc, live⟩
  apply queue_after_forced clauses queue head forced
  intro assignment models
  exact empty_negative_forced clauses index head labels original empty assignment models

/-- The same seed negative trace retains the original record-end header while
its tag, next cursor, tail, off flag and queue cell are written. -/
theorem negative_record_end_frame (program : Program width 8)
    (base entry skip conflict continuation row next : Nat) (queue : List (Fin n))
    (head : Fin n) (labels : List (Fin n)) (state final : State width 8)
    (stored : MutableStored (.negative head labels) row 0 false state.heap)
    (present : Controller.Horn.WorklistBucketReady.At (n := n) program base entry skip conflict continuation)
    (fifo : Stored queue base state.heap) (separated : base + 5 * n + 4 ≤ row)
    (tailBound : tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[tailSlot (n := n) base]'tailBound = word width (queueStart (n := n) base + queue.length))
    (rowHeld : state.reg 1 = word width row) (nextHeld : state.reg 4 = word width next)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 26 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (actual : Execution program state final (if head ∈ queue then 22 else 25) state.liveWords) :
    final.heap[Controller.Horn.WorklistFIFO.headSlot (n := n) base]? =
      state.heap[Controller.Horn.WorklistFIFO.headSlot (n := n) base]? := by
  obtain ⟨same, trace, _, _, _, _, _, _, _, _, _, _, _, writes, _⟩ :=
    Controller.Horn.WorklistBucketNegative.negative_tail_framed program base entry skip conflict continuation
      row next queue head labels state present fifo stored separated tailBound tailValue rowHeld nextHeld
      one zero decrement position running capacity room
  have endpoint := Controller.Horn.JoinedRuleFrame.execution_endpoint_unique actual trace
  rw [endpoint]
  apply writes
  · unfold Controller.Horn.WorklistFIFO.headSlot; omega
  · unfold nextSlot Controller.Horn.WorklistFIFO.headSlot; omega
  · unfold tailSlot Controller.Horn.WorklistFIFO.headSlot; omega
  · have headBound := head.isLt
    unfold offAddress Controller.Horn.WorklistFIFO.headSlot
    omega
  · unfold queueStart Controller.Horn.WorklistFIFO.headSlot
    omega

/-- Clean off cells and the original full physical index provide the actual
empty queue storage before the first seed mark. -/
theorem empty_fifo_of_cold (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordEnd : Nat) (heap : Array (Word width))
    (physical : Controller.Horn.IndexScan.PhysicalIndex clauses
      (Controller.Horn.IndexScanCold.recordStart width clauses) recordEnd
      (Controller.Horn.SourceSerialize.base clauses)
      (Controller.Horn.IndexScan.occurrences clauses (Controller.Horn.IndexScanCold.recordStart width clauses)).length heap)
    (clean : Controller.Horn.WorklistEnqueue.CleanOff (n := n) (Controller.Horn.SourceSerialize.base clauses) heap) :
    Stored ([] : List (Fin n)) (Controller.Horn.SourceSerialize.base clauses) heap := by
  have startBelow : Controller.Horn.IndexScanCold.recordStart width clauses ≤ recordEnd := by
    rw [physical.originalEnd]
    exact Controller.Horn.NormalizeLoop.recordOffset_above clauses _ _
  have fits : Controller.Horn.SourceSerialize.base clauses + 4 * n + 4 ≤ heap.size := by
    have endpoint := physical.endpoint
    unfold Controller.Horn.IndexScanCold.recordStart Controller.Horn.NormalizeCold.words at startBelow
    simp only [Controller.Horn.SourceSerialize.heap_size] at startBelow
    omega
  refine ⟨List.nodup_nil, fits, ?_, ?_⟩
  · intro label
    have bound : offAddress (Controller.Horn.SourceSerialize.base clauses) label < heap.size := by
      have := label.isLt
      unfold offAddress
      omega
    have value := clean label
    simpa only [Array.getElem?_eq_getElem bound, Option.some.injEq, List.not_mem_nil, ite_false] using value
  · refine ⟨?_, ?_⟩
    · unfold queueStart
      simp only [List.length_nil]
      omega
    · intro index
      exact Fin.elim0 index

open Controller.Horn.IndexScanCold Controller.Horn.IndexScanWhole in
/-- The single original normalization/index trace retains its actual header and
live register facts needed by the seed setup. It does not rerun normalization or
supply an incidence table at the seed boundary. -/
theorem cold_seed_input (clauses : List (Controller.CNF.Clause (Fin n)))
    (state : State width 8) (suffix : List (Word width))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := width) clauses).toList ++ suffix)
    (position : state.pc = word width 0) (running : state.halted = false)
    (dual : ∀ index : Fin clauses.length, Controller.Horn.DualHornClause clauses[index.val])
    (codeFits : (program width clauses).size < 2 ^ width)
    (heapFits : recordStart width clauses + 3 * clauses.length + 3 * (clauses.map List.length).sum < 2 ^ width) :
    ∃ final : State width 8, ∃ recordEnd ticks peak : Nat,
      Execution (program width clauses) state final ticks peak ∧
      Controller.Horn.IndexScan.PhysicalIndex clauses (recordStart width clauses) recordEnd
        (Controller.Horn.SourceSerialize.base clauses)
        (Controller.Horn.IndexScan.occurrences clauses (recordStart width clauses)).length final.heap ∧
      Controller.Horn.SourceScan.CursorStored recordEnd 0 final.heap ∧
      Stored ([] : List (Fin n)) (Controller.Horn.SourceSerialize.base clauses) final.heap ∧
      final.pc = word width (program width clauses).size ∧ final.halted = false ∧
      final.reg 2 = word width 0 ∧ final.reg 5 = word width 1 ∧
      final.heap.size < 2 ^ width ∧ final.stack = suffix ∧ final.output = state.output ∧
      ticks ≤ 25 * n + 83 * (clauses.map List.length).sum + 95 * clauses.length + 66 ∧
      peak ≤ state.liveWords + 5 * n + 4 + 3 * clauses.length + 3 * (clauses.map List.length).sum := by
  obtain ⟨normalized, marks, normalizeTicks, normalizePeak, normalizeTrace, invariant,
      normalizePosition, normalizeStack, normalizeOutput, normalizeCost, normalizeStorage⟩ :=
    Controller.Horn.NormalizeCold.execution clauses state suffix emptyHeap input position running dual
      (by have := program_size (width := width) clauses; unfold entry at this; omega)
      (by unfold recordStart at heapFits; omega)
  have physical := Controller.Horn.IndexScan.initial clauses (Controller.Horn.SourceSerialize.layout clauses)
    (recordStart width clauses) marks normalized invariant
  have header : Controller.Horn.SourceScan.CursorStored normalized.heap.size 0 normalized.heap := by
    simpa [Controller.Horn.SourceSerialize.layout] using invariant.recordCursor
  have endpoints := invariant.records.endpoint
  have packed := packed_endpoint clauses (recordStart width clauses)
  have incidences := occurrences_length_le clauses (recordStart width clauses)
  have scanRoom : normalized.heap.size +
      2 * (Controller.Horn.IndexScan.occurrences clauses (recordStart width clauses)).length < 2 ^ width := by
    change normalized.heap.size = Controller.Horn.NormalizeLoop.recordOffset clauses (recordStart width clauses) clauses.length at endpoints
    omega
  obtain ⟨final, scanTrace, result, finalClean⟩ := Controller.Horn.WorklistEnqueue.all_rows_clean
    (program width clauses) clauses (recordStart width clauses) normalized.heap.size
    (Controller.Horn.SourceSerialize.base clauses) (entry width clauses) normalized
    (index_at clauses) physical header (cold_base_positive clauses) normalizePosition
    invariant.input.running invariant.input.zero invariant.input.one
    (Controller.Horn.WorklistEnqueue.normalized_clean_off clauses (Controller.Horn.SourceSerialize.layout clauses)
      (recordStart width clauses) clauses.length marks normalized invariant)
    (by simpa only [program_size] using codeFits) scanRoom
  let full := (append_execution _ _ normalizeTrace).append scanTrace
  refine ⟨final, normalized.heap.size, normalizeTicks +
    (16 * (Controller.Horn.IndexScan.occurrences clauses (recordStart width clauses)).length + 18 * clauses.length + 6),
    max normalizePeak (normalized.liveWords + 2 * (Controller.Horn.IndexScan.occurrences clauses (recordStart width clauses)).length),
    full, result.physical, result.header, empty_fifo_of_cold clauses _ _ result.physical finalClean,
    ?_, result.running, result.zero.trans invariant.input.zero, result.one.trans invariant.input.one,
    ?_, result.stack.trans normalizeStack, result.output.trans normalizeOutput, ?_, ?_⟩
  · simpa only [program_size] using result.position
  · have growth := result.growth
    omega
  · omega
  · have resident := normalizeTrace.final_storage_le
    omega

end Controller.Horn.WorklistSeed
