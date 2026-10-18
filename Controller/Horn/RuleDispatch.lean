module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.RuleCopy

@[expose] public section

/-!
# Physical rule selection from normalized scratch headers

The routine reads the tautology flag and negative-buffer cursor. It selects a
record tag and, when needed, loads the first negative label from actual storage.
A separate tag-zero bypass prevents a tautological scratch row from copying its
possibly nonempty positive buffer into an inert record.
-/
namespace Controller.Horn.RuleDispatch

open Controller.Cost Controller.Horn.Worklist.IndexedNormalize

/-- Supported normalized rows have at most one negative head unless inert. -/
def Supported (row : Row n) : Prop := row.tautology = true ∨ row.negative.length ≤ 1

/-- Selection reads only allocated headers and an actual negative-label cell.
The runtime tag-zero bypass is composed after the record header is allocated. -/
def code (width n entry base exit : Nat) : Program width 8 :=
  #[.constant 0 (word width (base + 2 * n + 3)), .load 1 0,
    .branchZero 1 (word width (entry + 6)),
    .constant 1 (word width 0), .constant 3 (word width 0),
    .branchZero 2 (word width exit),
    .constant 0 (word width (base + 2 * n + 1)), .load 0 0,
    .constant 1 (word width (base + 4 * n + 4)), .xor 1 0 1,
    .branchZero 1 (word width (entry + 14)),
    .load 3 0, .constant 1 (word width 2), .branchZero 2 (word width exit),
    .constant 3 (word width 0), .constant 1 (word width 1),
    .branchZero 2 (word width exit)]

@[simp] theorem code_size (width n entry base exit : Nat) :
    (code width n entry base exit).size = 17 := rfl

def CodeAt (program : Program width 8) (entry base exit : Nat) (n : Nat) : Prop :=
  ∀ phase : Fin 17, program[entry + phase.val]? = some ((code width n entry base exit)[phase.val])

/-- Every inert record initializes its actual visit counter and branches around
positive-buffer traversal. Active records continue to the physical setup. -/
def skipCode (width activeExit : Nat) : Program width 8 :=
  #[.constant 4 (word width 0), .branchZero 1 (word width activeExit)]

@[simp] theorem skipCode_size (width activeExit : Nat) :
    (skipCode width activeExit).size = 2 := rfl

def SkipAt (program : Program width 8) (entry activeExit : Nat) : Prop :=
  program[entry]? = some (.constant 4 (word width 0)) ∧
  program[entry + 1]? = some (.branchZero 1 (word width activeExit))

private theorem word_val (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem advance_position (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word_val (width := width) entry fits]

/-- A selected inert tag executes the real zero-count bypass. -/
theorem skip_execution (program : Program width 8) (entry activeExit : Nat)
    (present : SkipAt program entry activeExit) (state : State width 8)
    (position : state.pc = word width entry) (tagZero : state.reg 1 = word width 0)
    (running : state.halted = false) (capacity : entry + 2 < 2 ^ width) :
    Execution program state
      { (state.advance.put 4 (word width 0)).advance with pc := word width activeExit }
      2 state.liveWords := by
  let middle := state.advance.put 4 (word width 0)
  let final := { middle.advance with pc := word width activeExit }
  have middlePC : middle.pc = word width (entry + 1) :=
    advance_position state entry position (by omega)
  have first : programStep program state = some middle := by
    unfold programStep
    rw [position, word_val (width := width) entry (by omega), present.1]
    change step (.constant 4 (word width 0)) state = _
    simp [step, middle, running]
  have second : programStep program middle = some final := by
    unfold programStep
    rw [middlePC, word_val (width := width) (entry + 1) (by omega), present.2]
    change step (.branchZero 1 (word width activeExit)) middle = _
    simp [step, middle, final, State.put, State.advance, running, tagZero, word]
  have trace := Execution.cons first (Execution.cons second (Execution.refl final))
  simpa [final, middle, State.liveWords, State.put, State.advance] using trace

/-- The bypass preserves the allocated record and all source/scratch cells. -/
theorem skip_frame (state : State width 8) (activeExit : Nat) :
    let final := { (state.advance.put 4 (word width 0)).advance with pc := word width activeExit }
    final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
    final.reg 4 = word width 0 ∧
    (∀ register : Fin 8, register ≠ 4 → final.reg register = state.reg register) ∧
    final.halted = state.halted := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [State.put, State.advance]
  · intro register different
    simp [State.put, State.advance, different]


def flagFinished {n : Nat} (state : State width 8) (base : Nat) (flag : Bool) : State width 8 :=
  (state.advance.put 0 (word width (base + 2 * n + 3))).advance.put 1
    (Controller.Horn.MarkStorage.encode width flag)

/-- The selection flag is fetched from the actual RowStored heap cell. -/
theorem flag_execution (program : Program width 8) (entry base exit pcur ncur tcur : Nat)
    (present : CodeAt program entry base exit n) (state : State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 17 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (flagFinished (n := n) state base row.tautology) 2 state.liveWords := by
  let middle := state.advance.put 0 (word width (base + 2 * n + 3))
  let final := flagFinished (n := n) state base row.tautology
  have middlePC : middle.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have first : programStep program state = some middle := by
    have fetched : program[state.pc.val]? = some (.constant 0 (word width (base + 2 * n + 3))) := by
      rw [position, word_val (width := width) entry (by omega)]
      simpa [code] using present 0
    unfold programStep
    rw [fetched]
    change step (.constant 0 (word width (base + 2 * n + 3))) state = _
    simp [step, middle, running]
  have second : programStep program middle = some final := by
    have fetched : program[middle.pc.val]? = some (.load 1 0) := by
      rw [middlePC, word_val (width := width) (entry + 1) (by omega)]
      simpa [code] using present 1
    unfold programStep
    rw [fetched]
    change step (.load 1 0) middle = _
    have address : (middle.reg 0).val = base + 2 * n + 3 := by
      simp [middle, State.put, word_val (width := width) _ (stored.flagBound.trans heapFits)]
    have bound : base + 2 * n + 3 < middle.heap.size := stored.flagBound
    simp only [step, show middle.halted = false from running, Bool.false_eq_true, ite_false,
      address, dite_eq_left bound]
    change some (middle.advance.put 1 (state.heap[base + 2 * n + 3]'stored.flagBound)) = some final
    rw [stored.flag]
    rfl
  have trace := Execution.cons first (Execution.cons second (Execution.refl final))
  simpa [final, flagFinished, middle, State.liveWords, State.put, State.advance] using trace

theorem flagFinished_frame (state : State width 8) (base : Nat) (flag : Bool) :
    (flagFinished (n := n) state base flag).heap = state.heap ∧
    (flagFinished (n := n) state base flag).stack = state.stack ∧
    (flagFinished (n := n) state base flag).output = state.output ∧
    (flagFinished (n := n) state base flag).reg 1 = Controller.Horn.MarkStorage.encode width flag ∧
    (∀ register : Fin 8, register ≠ 0 → register ≠ 1 →
      (flagFinished (n := n) state base flag).reg register = state.reg register) ∧
    (flagFinished (n := n) state base flag).halted = state.halted := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [flagFinished, State.put]
  · intro register zero one
    simp [flagFinished, State.put, State.advance, zero, one]


def negativeFinished {n : Nat} (state : State width 8) (base cursor : Nat) : State width 8 :=
  (state.advance.put 0 (word width (base + 2 * n + 1))).advance.put 0 (word width cursor)

/-- The negative cursor is read physically, not supplied as a loaded length. -/
theorem negative_execution (program : Program width 8) (entry base exit pcur ncur tcur : Nat)
    (present : CodeAt program entry base exit n) (state : State width 8) (row : Row n)
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur state.heap)
    (position : state.pc = word width (entry + 6)) (running : state.halted = false)
    (capacity : entry + 17 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (negativeFinished (n := n) state base ncur) 2 state.liveWords := by
  let middle := state.advance.put 0 (word width (base + 2 * n + 1))
  let final := negativeFinished (n := n) state base ncur
  have middlePC : middle.pc = word width (entry + 7) := by
    simpa [middle, State.put, Nat.add_assoc] using advance_position state (entry + 6) position (by omega)
  have first : programStep program state = some middle := by
    have fetched : program[state.pc.val]? = some (.constant 0 (word width (base + 2 * n + 1))) := by
      rw [position, word_val (width := width) (entry + 6) (by omega)]
      simpa [code] using present 6
    unfold programStep
    rw [fetched]
    change step (.constant 0 (word width (base + 2 * n + 1))) state = _
    simp [step, middle, running]
  have second : programStep program middle = some final := by
    have fetched : program[middle.pc.val]? = some (.load 0 0) := by
      rw [middlePC, word_val (width := width) (entry + 7) (by omega)]
      simpa [code] using present 7
    unfold programStep
    rw [fetched]
    change step (.load 0 0) middle = _
    have address : (middle.reg 0).val = base + 2 * n + 1 := by
      simp [middle, State.put, word_val (width := width) _ (stored.negative.bound.trans heapFits)]
    have bound : base + 2 * n + 1 < middle.heap.size := stored.negative.bound
    simp only [step, show middle.halted = false from running, Bool.false_eq_true, ite_false,
      address, dite_eq_left bound]
    change some (middle.advance.put 0 (state.heap[base + 2 * n + 1]'stored.negative.bound)) = some final
    rw [stored.negative.value]
    rfl
  have trace := Execution.cons first (Execution.cons second (Execution.refl final))
  simpa [final, negativeFinished, middle, State.liveWords, State.put, State.advance] using trace

theorem negativeFinished_frame (state : State width 8) (base cursor : Nat) :
    (negativeFinished (n := n) state base cursor).heap = state.heap ∧
    (negativeFinished (n := n) state base cursor).stack = state.stack ∧
    (negativeFinished (n := n) state base cursor).output = state.output ∧
    (negativeFinished (n := n) state base cursor).reg 0 = word width cursor ∧
    (∀ register : Fin 8, register ≠ 0 →
      (negativeFinished (n := n) state base cursor).reg register = state.reg register) ∧
    (negativeFinished (n := n) state base cursor).halted = state.halted := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [negativeFinished, State.put]
  · intro register zero
    simp [negativeFinished, State.put, State.advance, zero]


def TailAt (program : Program width 8) (entry exit : Nat)
    (first second : Fin 8) (left right : Word width) : Prop :=
  program[entry]? = some (.constant first left) ∧
  program[entry + 1]? = some (.constant second right) ∧
  program[entry + 2]? = some (.branchZero 2 (word width exit))

def tailFinished (state : State width 8) (exit : Nat)
    (first second : Fin 8) (left right : Word width) : State width 8 :=
  { ((state.advance.put first left).advance.put second right).advance with pc := word width exit }

/-- The tag/head constants and exit branch are three actual fetched operations. -/
theorem tail_execution (program : Program width 8) (entry exit : Nat)
    (first second : Fin 8) (left right : Word width)
    (present : TailAt program entry exit first second left right) (state : State width 8)
    (position : state.pc = word width entry) (zero : state.reg 2 = word width 0)
    (firstSafe : first ≠ 2) (secondSafe : second ≠ 2)
    (running : state.halted = false) (capacity : entry + 3 < 2 ^ width) :
    Execution program state (tailFinished state exit first second left right) 3 state.liveWords := by
  let a := state.advance.put first left
  let b := a.advance.put second right
  let final := tailFinished state exit first second left right
  have apc : a.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have bpc : b.pc = word width (entry + 2) := by
    simpa [b, State.put, Nat.add_assoc] using advance_position a (entry + 1) apc (by omega)
  have t0 : programStep program state = some a := by
    unfold programStep
    rw [position, word_val (width := width) entry (by omega), present.1]
    change step (.constant first left) state = _
    simp [step, a, running]
  have t1 : programStep program a = some b := by
    unfold programStep
    rw [apc, word_val (width := width) (entry + 1) (by omega), present.2.1]
    change step (.constant second right) a = _
    simp [step, b, a, State.put, State.advance, running]
  have t2 : programStep program b = some final := by
    unfold programStep
    rw [bpc, word_val (width := width) (entry + 2) (by omega), present.2.2]
    change step (.branchZero 2 (word width exit)) b = _
    have zeroHeld : b.reg 2 = word width 0 := by
      simp [b, a, State.put, State.advance, Ne.symm firstSafe, Ne.symm secondSafe, zero]
    simp only [step, show b.halted = false from running, Bool.false_eq_true, ite_false, zeroHeld]
    simp [word, final, tailFinished, b, a]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl final)))
  simpa [final, tailFinished, b, a, State.liveWords, State.put, State.advance] using trace

/-- The inert branch of the complete selector provides the physical tail. -/
theorem inert_tail_at (program : Program width 8) (entry base exit : Nat)
    (present : CodeAt program entry base exit n) :
    TailAt program (entry + 3) exit 1 3 (word width 0) (word width 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [code] using present 3
  · simpa [code, Nat.add_assoc] using present 4
  · simpa [code, Nat.add_assoc] using present 5

/-- The headless positive branch also supplies its fetched tail. -/
theorem positive_tail_at (program : Program width 8) (entry base exit : Nat)
    (present : CodeAt program entry base exit n) :
    TailAt program (entry + 14) exit 3 1 (word width 0) (word width 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [code] using present 14
  · simpa [code, Nat.add_assoc] using present 15
  · simpa [code, Nat.add_assoc] using present 16


def branchFinished (state : State width 8) (register : Fin 8) (target : Nat) : State width 8 :=
  if (state.reg register).val = 0 then { state.advance with pc := word width target } else state.advance

/-- A fetched conditional follows its actual source register. -/
theorem branch_execution (program : Program width 8) (entry target : Nat) (register : Fin 8)
    (present : program[entry]? = some (.branchZero register (word width target)))
    (state : State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (entryFits : entry < 2 ^ width) :
    Execution program state (branchFinished state register target) 1 state.liveWords := by
  have transition : programStep program state = some (branchFinished state register target) := by
    unfold programStep
    rw [position, word_val (width := width) entry entryFits, present]
    change step (.branchZero register (word width target)) state = _
    simp [step, branchFinished, running]
  have live : (branchFinished state register target).liveWords = state.liveWords := by
    unfold branchFinished
    split <;> rfl
  simpa [live] using Execution.cons transition (Execution.refl (branchFinished state register target))

theorem flag_branch_at (program : Program width 8) (entry base exit : Nat)
    (present : CodeAt program entry base exit n) :
    program[entry + 2]? = some (.branchZero 1 (word width (entry + 6))) := by
  simpa [code] using present 2

theorem negative_branch_at (program : Program width 8) (entry base exit : Nat)
    (present : CodeAt program entry base exit n) :
    program[entry + 10]? = some (.branchZero 1 (word width (entry + 14))) := by
  simpa [code] using present 10

/-- The physical flag chooses exactly the stored inert or active program entry. -/
theorem flag_branch_position (state : State width 8) (entry : Nat) (flag : Bool)
    (position : state.pc = word width (entry + 2))
    (held : state.reg 1 = Controller.Horn.MarkStorage.encode width flag)
    (capacity : entry + 17 < 2 ^ width) :
    (branchFinished state 1 (entry + 6)).pc =
      word width (entry + if flag then 3 else 6) := by
  cases flag <;>
    simp [branchFinished, State.advance, held, Controller.Horn.MarkStorage.encode, position,
      word_val (width := width) 0 (by omega), word_val (width := width) 1 (by omega),
      word_val (width := width) (entry + 2) (by omega)]


/-- The comparison uses the physically read cursor and allocated buffer end. -/
theorem compare_execution (program : Program width 8) (entry base exit cursor : Nat)
    (present : CodeAt program entry base exit n) (state : State width 8)
    (position : state.pc = word width (entry + 8)) (held : state.reg 0 = word width cursor)
    (running : state.halted = false) (capacity : entry + 17 < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) (endFits : base + 4 * n + 4 < 2 ^ width) :
    Execution program state (Controller.Horn.RuleCopy.bodyTest state cursor (base + 4 * n + 4))
      2 state.liveWords := by
  let a := state.advance.put 1 (word width (base + 4 * n + 4))
  let final := Controller.Horn.RuleCopy.bodyTest state cursor (base + 4 * n + 4)
  have apc : a.pc = word width (entry + 9) := by
    simpa [a, State.put, Nat.add_assoc] using advance_position state (entry + 8) position (by omega)
  have first : programStep program state = some a := by
    have fetched : program[state.pc.val]? = some (.constant 1 (word width (base + 4 * n + 4))) := by
      rw [position, word_val (width := width) (entry + 8) (by omega)]
      simpa [code] using present 8
    unfold programStep
    rw [fetched]
    change step (.constant 1 (word width (base + 4 * n + 4))) state = _
    simp [step, a, running]
  have second : programStep program a = some final := by
    have fetched : program[a.pc.val]? = some (.xor 1 0 1) := by
      rw [apc, word_val (width := width) (entry + 9) (by omega)]
      simpa [code] using present 9
    unfold programStep
    rw [fetched]
    change step (.xor 1 0 1) a = _
    simp [step, final, Controller.Horn.RuleCopy.bodyTest, a, State.put, State.advance,
      running, held, word_val (width := width) cursor cursorFits,
      word_val (width := width) (base + 4 * n + 4) endFits]
  have trace := Execution.cons first (Execution.cons second (Execution.refl final))
  simpa [final, Controller.Horn.RuleCopy.bodyTest, a, State.liveWords, State.put, State.advance] using trace

/-- The stored list and actual cursor give exactly the empty-buffer test. -/
theorem negative_empty_iff (row : Row n) (base pcur ncur tcur : Nat) (heap : Array (Word width))
    (stored : Controller.Horn.LiteralDispatch.RowStored row base pcur ncur tcur heap) :
    ncur = base + 4 * n + 4 ↔ row.negative = [] := by
  have ends := stored.negative.buffer.ends
  constructor
  · intro equal
    have length : row.negative.length = 0 := by omega
    simpa using length
  · intro empty
    simp only [empty, List.length_nil, Nat.add_zero] at ends
    exact ends

/-- XOR control reaches the headless or physical-head branch exactly. -/
theorem negative_branch_position (state : State width 8) (entry cursor limit : Nat)
    (position : state.pc = word width (entry + 10))
    (held : state.reg 1 = word width (Nat.xor cursor limit))
    (capacity : entry + 17 < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) (limitFits : limit < 2 ^ width) :
    (branchFinished state 1 (entry + 14)).pc =
      word width (entry + if cursor = limit then 14 else 11) := by
  have xorFits := Nat.xor_lt_two_pow cursorFits limitFits
  by_cases equal : cursor = limit
  · simp [branchFinished, held, equal, Nat.xor_self, word_val (width := width) 0 (by omega)]
  · have different : Nat.xor cursor limit ≠ 0 := fun zero =>
      equal ((Controller.Horn.ResetPointer.xor_zero_iff _ _).mp zero)
    have actualValue : (word width (Nat.xor cursor limit)).val = Nat.xor cursor limit :=
      word_val (width := width) (Nat.xor cursor limit) (by simpa using xorFits)
    have valDifferent : (word width (Nat.xor cursor limit)).val ≠ 0 := by
      rw [actualValue]
      exact different
    unfold branchFinished
    rw [held, ite_eq_right valDifferent]
    simp [equal, State.advance, position, word_val (width := width) (entry + 10) (by omega), Nat.add_assoc]


def headFinished (state : State width 8) (exit : Nat) (label : Fin n) : State width 8 :=
  { ((state.advance.put 3 (word width label.val)).advance.put 1 (word width 2)).advance with pc := word width exit }

/-- The negative head is loaded from the actual first stored label cell. -/
theorem head_execution (program : Program width 8) (entry base exit cursor : Nat)
    (present : CodeAt program entry base exit n) (state : State width 8)
    (label : Fin n) (tail : List (Fin n))
    (stored : Controller.Horn.ResetTouched.LabelsStored (label :: tail) cursor state.heap)
    (position : state.pc = word width (entry + 11)) (held : state.reg 0 = word width cursor)
    (zero : state.reg 2 = word width 0) (running : state.halted = false)
    (capacity : entry + 17 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width) :
    Execution program state (headFinished state exit label) 3 state.liveWords := by
  let a := state.advance.put 3 (word width label.val)
  let b := a.advance.put 1 (word width 2)
  let final := headFinished state exit label
  have bound : cursor < state.heap.size := by
    have := stored.fits
    simp only [List.length_cons] at this
    omega
  have apc : a.pc = word width (entry + 12) := by
    simpa [a, State.put, Nat.add_assoc] using advance_position state (entry + 11) position (by omega)
  have bpc : b.pc = word width (entry + 13) := by
    simpa [b, State.put, Nat.add_assoc] using advance_position a (entry + 12) apc (by omega)
  have first : programStep program state = some a := by
    have fetched : program[state.pc.val]? = some (.load 3 0) := by
      rw [position, word_val (width := width) (entry + 11) (by omega)]
      simpa [code] using present 11
    unfold programStep
    rw [fetched]
    change step (.load 3 0) state = _
    simp only [step, running, Bool.false_eq_true, ite_false, held,
      word_val (width := width) cursor (bound.trans heapFits), dite_eq_left bound]
    rw [stored.head]
  have second : programStep program a = some b := by
    have fetched : program[a.pc.val]? = some (.constant 1 (word width 2)) := by
      rw [apc, word_val (width := width) (entry + 12) (by omega)]
      simpa [code] using present 12
    unfold programStep
    rw [fetched]
    change step (.constant 1 (word width 2)) a = _
    simp [step, b, a, State.put, State.advance, running]
  have third : programStep program b = some final := by
    have fetched : program[b.pc.val]? = some (.branchZero 2 (word width exit)) := by
      rw [bpc, word_val (width := width) (entry + 13) (by omega)]
      simpa [code] using present 13
    unfold programStep
    rw [fetched]
    change step (.branchZero 2 (word width exit)) b = _
    have zeroHeld : b.reg 2 = word width 0 := by simp [b, a, State.put, State.advance, zero]
    simp only [step, show b.halted = false from running, Bool.false_eq_true, ite_false, zeroHeld]
    simp [word, final, headFinished, b, a]
  have trace := Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl final)))
  simpa [final, headFinished, b, a, State.liveWords, State.put, State.advance] using trace


theorem flagFinished_position (state : State width 8) (entry base : Nat) (flag : Bool)
    (position : state.pc = word width entry) (capacity : entry + 17 < 2 ^ width) :
    (flagFinished (n := n) state base flag).pc = word width (entry + 2) := by
  simp only [flagFinished, State.put, State.advance, position,
    word_val (width := width) entry (by omega), word_val (width := width) (entry + 1) (by omega),
    Nat.add_assoc, Nat.reduceAdd]

theorem negativeFinished_position (state : State width 8) (entry base cursor : Nat)
    (position : state.pc = word width (entry + 6)) (capacity : entry + 17 < 2 ^ width) :
    (negativeFinished (n := n) state base cursor).pc = word width (entry + 8) := by
  simp only [negativeFinished, State.put, State.advance, position,
    word_val (width := width) (entry + 6) (by omega),
    word_val (width := width) (entry + 7) (by omega), Nat.add_assoc, Nat.reduceAdd]

theorem compare_position (state : State width 8) (entry cursor limit : Nat)
    (position : state.pc = word width (entry + 8)) (capacity : entry + 17 < 2 ^ width) :
    (Controller.Horn.RuleCopy.bodyTest state cursor limit).pc = word width (entry + 10) := by
  simp only [Controller.Horn.RuleCopy.bodyTest, State.put, State.advance, position,
    word_val (width := width) (entry + 8) (by omega),
    word_val (width := width) (entry + 9) (by omega), Nat.add_assoc, Nat.reduceAdd]

theorem branchFinished_frame (state : State width 8) (register : Fin 8) (target : Nat) :
    (branchFinished state register target).reg = state.reg ∧
    (branchFinished state register target).heap = state.heap ∧
    (branchFinished state register target).stack = state.stack ∧
    (branchFinished state register target).output = state.output ∧
    (branchFinished state register target).halted = state.halted ∧
    (branchFinished state register target).liveWords = state.liveWords := by
  unfold branchFinished
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Controller.Horn.RuleDispatch
