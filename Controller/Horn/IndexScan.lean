module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.IndexBuild

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The incidence-index program scans the immutable physical normalized records
before propagation changes their count or scheduling fields. Its specifications
refer to original source clauses; no incidence list is supplied to the machine. -/
namespace Controller.Horn.IndexScan
open Controller.Cost Controller.Horn.WorklistStorage
variable {width n : Nat}

/-- The positive scratch header is reused to save the current physical body end.
Record header zero retains the end of all normalized records. -/
def setupPrefix (width base recordStart entry : Nat) : Program width 8 :=
  #[.constant 1 (word width recordStart), .load 7 2,
    .constant 3 (word width 0), .load 4 3, .xor 3 1 4,
    .branchZero 3 (word width (entry + 32)),
    .copy 0 1, .add 0 0 5, .add 0 0 5, .load 4 0,
    .add 0 0 5, .add 4 0 4,
    .constant 3 (word width (base + 2 * n)), .store 3 4,
    .constant 3 (word width (base + 2 * n)), .load 4 3,
    .xor 3 0 4, .branchZero 3 (word width (entry + 30))]

def suffix (width entry : Nat) : Program width 8 :=
  #[.branchZero 2 (word width (entry + 14)), .copy 1 0,
    .branchZero 2 (word width (entry + 2))]

def code (width base recordStart entry : Nat) : Program width 8 :=
  setupPrefix (n := n) width base recordStart entry ++ Controller.Horn.IndexBuild.code width base ++ suffix width entry

@[simp] theorem prefix_size (width base recordStart entry : Nat) :
    (setupPrefix (n := n) width base recordStart entry).size = 18 := rfl
@[simp] theorem suffix_size (width entry : Nat) : (suffix width entry).size = 3 := rfl
@[simp] theorem code_size (width base recordStart entry : Nat) :
    (code (n := n) width base recordStart entry).size = 32 := by simp [code]
@[simp] theorem code_words (width base recordStart entry : Nat) :
    programWords (code (n := n) width base recordStart entry) = 128 := by simp [programWords]

/-- Every phase is fetched from the same relocated 32-instruction program. -/
def At (program : Program width 8) (entry base recordStart : Nat) : Prop :=
  ∀ phase : Fin 32, program[entry + phase.val]? =
    (code (n := n) width base recordStart entry)[phase.val]?

/-- The incidence routine is genuinely embedded at phase eighteen; this is not
an execution on a substituted standalone helper program. -/
theorem kernel_at (program : Program width 8) (entry base recordStart : Nat)
    (present : At (n := n) program entry base recordStart) :
    Controller.Horn.IndexBuild.At program (entry + 18) base := by
  intro phase
  have fetched := present ⟨18 + phase.val, by have := phase.isLt; omega⟩
  have encoded : (code (n := n) width base recordStart entry)[18 + phase.val]? =
      some (Controller.Horn.IndexBuild.code width base)[phase.val] := by
    unfold code
    rw [Array.getElem?_append_left (by have := phase.isLt; simp only [Array.size_append, prefix_size, Controller.Horn.IndexBuild.code_size]; omega)]
    rw [Array.getElem?_append_right (by simp only [prefix_size]; omega)]
    simp only [prefix_size, Nat.add_sub_cancel_left]
    rw [Array.getElem?_eq_getElem (by simpa using phase.isLt)]
    rfl
  rw [encoded] at fetched
  simpa only [Nat.add_assoc] using fetched

def rowSnapshot (state : State width 8) (pc : Nat) (r0 r3 r4 : Word width)
    (heap : Array (Word width)) : State width 8 :=
  { state with
    pc := word width pc
    halted := false
    heap := heap
    reg := fun register => if register = 0 then r0 else if register = 3 then r3
      else if register = 4 then r4 else state.reg register }

private theorem word_value (value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

/-- The saved body endpoint is calculated from the physically loaded immutable
count header, and written by the fetched store before the body test. -/
def rowFinished (state : State width 8) (entry base offset count : Nat)
    (headerBound : base + 2 * n < state.heap.size) : State width 8 :=
  rowSnapshot state (entry + 14) (word width (offset + 3)) (word width (base + 2 * n))
    (word width (offset + 3 + count))
    (state.heap.set (base + 2 * n) (word width (offset + 3 + count)) headerBound)

theorem row_setup_execution (program : Program width 8) (entry base recordStart offset : Nat)
    (rule : Controller.Horn.Worklist.Rule (Fin n)) (state : State width 8)
    (present : At (n := n) program entry base recordStart)
    (stored : Controller.Horn.RuleCopy.Stored rule offset state.heap)
    (headerBound : base + 2 * n < state.heap.size)
    (cursorHeld : state.reg 1 = word width offset) (one : state.reg 5 = word width 1)
    (position : state.pc = word width (entry + 6)) (running : state.halted = false)
    (capacity : entry + 32 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    Execution program state (rowFinished state entry base offset rule.positives.length headerBound)
      8 state.liveWords := by
  have offsetFits : offset < 2 ^ width := by have := stored.fits; omega
  have oneFits : 1 < 2 ^ width := by have := stored.fits; omega
  have countBound : offset + 2 < state.heap.size := by have := stored.fits; omega
  have countCell := stored.countValue
  have pcFits (phase : Nat) (bound : phase ≤ 32) : entry + phase < 2 ^ width := by omega
  have pointerFits (phase : Nat) (bound : phase ≤ 3) : offset + phase < 2 ^ width := by
    have := stored.fits
    omega
  have endFits : offset + 3 + rule.positives.length < 2 ^ width := by have := stored.fits; omega
  have headerFits : base + 2 * n < 2 ^ width := by omega
  let s1 := rowSnapshot state (entry + 7) (word width offset) (state.reg 3) (state.reg 4) (state.heap)
  let s2 := rowSnapshot state (entry + 8) (word width (offset + 1)) (state.reg 3) (state.reg 4) (state.heap)
  let s3 := rowSnapshot state (entry + 9) (word width (offset + 2)) (state.reg 3) (state.reg 4) (state.heap)
  let s4 := rowSnapshot state (entry + 10) (word width (offset + 2)) (state.reg 3) (word width rule.positives.length) (state.heap)
  let s5 := rowSnapshot state (entry + 11) (word width (offset + 3)) (state.reg 3) (word width rule.positives.length) (state.heap)
  let s6 := rowSnapshot state (entry + 12) (word width (offset + 3)) (state.reg 3) (word width (offset + 3 + rule.positives.length)) (state.heap)
  let s7 := rowSnapshot state (entry + 13) (word width (offset + 3)) (word width (base + 2 * n)) (word width (offset + 3 + rule.positives.length)) (state.heap)
  let s8 := rowSnapshot state (entry + 14) (word width (offset + 3)) (word width (base + 2 * n)) (word width (offset + 3 + rule.positives.length)) (state.heap.set (base + 2 * n) (word width (offset + 3 + rule.positives.length)) headerBound)
  have f0 := present ⟨6, by decide⟩
  simp [code, setupPrefix, suffix] at f0
  have t0 : programStep program state = some s1 := by
    simp [programStep, step, rowSnapshot, State.advance, State.put, s1, f0, position, running, cursorHeld, one, countBound, countCell, headerBound, word_value (width := width) (entry + 6) (pcFits 6 (by omega)), word_value (width := width) (offset + 1) (pointerFits 1 (by omega)), word_value (width := width) (offset + 2) (pointerFits 2 (by omega)), word_value (width := width) (offset + 3) (pointerFits 3 (by omega)), word_value (width := width) offset offsetFits, word_value (width := width) 1 oneFits, word_value (width := width) rule.positives.length stored.countFits, word_value (width := width) (base + 2 * n) headerFits, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [rowSnapshot, State.put, State.advance]))
  have f1 := present ⟨7, by decide⟩
  simp [code, setupPrefix, suffix] at f1
  have t1 : programStep program s1 = some s2 := by
    simp [programStep, step, rowSnapshot, State.advance, State.put, s1, s2, f1, position, running, cursorHeld, one, countBound, countCell, headerBound, word_value (width := width) (entry + 7) (pcFits 7 (by omega)), word_value (width := width) (offset + 1) (pointerFits 1 (by omega)), word_value (width := width) (offset + 2) (pointerFits 2 (by omega)), word_value (width := width) (offset + 3) (pointerFits 3 (by omega)), word_value (width := width) offset offsetFits, word_value (width := width) 1 oneFits, word_value (width := width) rule.positives.length stored.countFits, word_value (width := width) (base + 2 * n) headerFits, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [rowSnapshot, State.put, State.advance]))
  have f2 := present ⟨8, by decide⟩
  simp [code, setupPrefix, suffix] at f2
  have t2 : programStep program s2 = some s3 := by
    simp [programStep, step, rowSnapshot, State.advance, State.put, s2, s3, f2, position, running, cursorHeld, one, countBound, countCell, headerBound, word_value (width := width) (entry + 8) (pcFits 8 (by omega)), word_value (width := width) (offset + 1) (pointerFits 1 (by omega)), word_value (width := width) (offset + 2) (pointerFits 2 (by omega)), word_value (width := width) (offset + 3) (pointerFits 3 (by omega)), word_value (width := width) offset offsetFits, word_value (width := width) 1 oneFits, word_value (width := width) rule.positives.length stored.countFits, word_value (width := width) (base + 2 * n) headerFits, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [rowSnapshot, State.put, State.advance]))
  have f3 := present ⟨9, by decide⟩
  simp [code, setupPrefix, suffix] at f3
  have t3 : programStep program s3 = some s4 := by
    simp [programStep, step, rowSnapshot, State.advance, State.put, s3, s4, f3, position, running, cursorHeld, one, countBound, countCell, headerBound, word_value (width := width) (entry + 9) (pcFits 9 (by omega)), word_value (width := width) (offset + 1) (pointerFits 1 (by omega)), word_value (width := width) (offset + 2) (pointerFits 2 (by omega)), word_value (width := width) (offset + 3) (pointerFits 3 (by omega)), word_value (width := width) offset offsetFits, word_value (width := width) 1 oneFits, word_value (width := width) rule.positives.length stored.countFits, word_value (width := width) (base + 2 * n) headerFits, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [rowSnapshot, State.put, State.advance]))
  have f4 := present ⟨10, by decide⟩
  simp [code, setupPrefix, suffix] at f4
  have t4 : programStep program s4 = some s5 := by
    simp [programStep, step, rowSnapshot, State.advance, State.put, s4, s5, f4, position, running, cursorHeld, one, countBound, countCell, headerBound, word_value (width := width) (entry + 10) (pcFits 10 (by omega)), word_value (width := width) (offset + 1) (pointerFits 1 (by omega)), word_value (width := width) (offset + 2) (pointerFits 2 (by omega)), word_value (width := width) (offset + 3) (pointerFits 3 (by omega)), word_value (width := width) offset offsetFits, word_value (width := width) 1 oneFits, word_value (width := width) rule.positives.length stored.countFits, word_value (width := width) (base + 2 * n) headerFits, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [rowSnapshot, State.put, State.advance]))
  have f5 := present ⟨11, by decide⟩
  simp [code, setupPrefix, suffix] at f5
  have t5 : programStep program s5 = some s6 := by
    simp [programStep, step, rowSnapshot, State.advance, State.put, s5, s6, f5, position, running, cursorHeld, one, countBound, countCell, headerBound, word_value (width := width) (entry + 11) (pcFits 11 (by omega)), word_value (width := width) (offset + 1) (pointerFits 1 (by omega)), word_value (width := width) (offset + 2) (pointerFits 2 (by omega)), word_value (width := width) (offset + 3) (pointerFits 3 (by omega)), word_value (width := width) offset offsetFits, word_value (width := width) 1 oneFits, word_value (width := width) rule.positives.length stored.countFits, word_value (width := width) (base + 2 * n) headerFits, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [rowSnapshot, State.put, State.advance]))
  have f6 := present ⟨12, by decide⟩
  simp [code, setupPrefix, suffix] at f6
  have t6 : programStep program s6 = some s7 := by
    simp [programStep, step, rowSnapshot, State.advance, State.put, s6, s7, f6, position, running, cursorHeld, one, countBound, countCell, headerBound, word_value (width := width) (entry + 12) (pcFits 12 (by omega)), word_value (width := width) (offset + 1) (pointerFits 1 (by omega)), word_value (width := width) (offset + 2) (pointerFits 2 (by omega)), word_value (width := width) (offset + 3) (pointerFits 3 (by omega)), word_value (width := width) offset offsetFits, word_value (width := width) 1 oneFits, word_value (width := width) rule.positives.length stored.countFits, word_value (width := width) (base + 2 * n) headerFits, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [rowSnapshot, State.put, State.advance]))
  have f7 := present ⟨13, by decide⟩
  simp [code, setupPrefix, suffix] at f7
  have t7 : programStep program s7 = some s8 := by
    simp [programStep, step, rowSnapshot, State.advance, State.put, s7, s8, f7, position, running, cursorHeld, one, countBound, countCell, headerBound, word_value (width := width) (entry + 13) (pcFits 13 (by omega)), word_value (width := width) (offset + 1) (pointerFits 1 (by omega)), word_value (width := width) (offset + 2) (pointerFits 2 (by omega)), word_value (width := width) (offset + 3) (pointerFits 3 (by omega)), word_value (width := width) offset offsetFits, word_value (width := width) 1 oneFits, word_value (width := width) rule.positives.length stored.countFits, word_value (width := width) (base + 2 * n) headerFits, Nat.add_assoc]
    all_goals first | omega | rfl | (congr 1 <;> try (ext register; fin_cases register <;> simp [rowSnapshot, State.put, State.advance]))
  have live1 : s1.liveWords = state.liveWords := by
    simp [s1, rowSnapshot, State.liveWords]
  have live2 : s2.liveWords = state.liveWords := by
    simp [s2, rowSnapshot, State.liveWords]
  have live3 : s3.liveWords = state.liveWords := by
    simp [s3, rowSnapshot, State.liveWords]
  have live4 : s4.liveWords = state.liveWords := by
    simp [s4, rowSnapshot, State.liveWords]
  have live5 : s5.liveWords = state.liveWords := by
    simp [s5, rowSnapshot, State.liveWords]
  have live6 : s6.liveWords = state.liveWords := by
    simp [s6, rowSnapshot, State.liveWords]
  have live7 : s7.liveWords = state.liveWords := by
    simp [s7, rowSnapshot, State.liveWords]
  have live8 : s8.liveWords = state.liveWords := by
    simp [s8, rowSnapshot, State.liveWords]
  have finalState : s8 = rowFinished state entry base offset rule.positives.length headerBound := rfl
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.refl s8))))))))
  have finalLive : (rowFinished state entry base offset rule.positives.length headerBound).liveWords = state.liveWords := by
    simp [rowFinished, rowSnapshot, State.liveWords]
  rw [finalState] at trace
  simpa only [live1, live2, live3, live4, live5, live6, live7, finalLive, Nat.reduceAdd, Nat.max_self] using trace

/-- The start cursor is determined by the source/scratch layout; the allocation
cursor is read from the physically stored original record end. -/
def started (state : State width 8) (recordStart : Nat) : State width 8 :=
  (state.advance.put 1 (word width recordStart)).advance.put 7 (word width state.heap.size)

theorem startup_execution (program : Program width 8) (entry base recordStart : Nat)
    (state : State width 8) (present : At (n := n) program entry base recordStart)
    (recordEnd : Controller.Horn.SourceScan.CursorStored state.heap.size 0 state.heap)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (capacity : entry + 32 < 2 ^ width)
    (room : state.heap.size < 2 ^ width) :
    Execution program state (started state recordStart) 2 state.liveWords := by
  let middle := state.advance.put 1 (word width recordStart)
  have f0 := present ⟨0, by decide⟩
  have f1 := present ⟨1, by decide⟩
  simp [code, setupPrefix, suffix] at f0 f1
  have middlePC : middle.pc = word width (entry + 1) := by
    simp [middle, State.put, State.advance, position, word_value (width := width) entry (by omega)]
  have first : programStep program state = some middle := by
    unfold programStep
    rw [position, word_value (width := width) entry (by omega), f0]
    simp [step, middle, running]
  have second : programStep program middle = some (started state recordStart) := by
    unfold programStep
    rw [middlePC, word_value (width := width) (entry + 1) (by omega), f1]
    simp [step, started, middle, State.put, State.advance, running, zero, recordEnd.bound,
      recordEnd.value, word_value (width := width) 0 (by omega)]
  have trace := Execution.cons first (Execution.cons second (Execution.refl (started state recordStart)))
  simpa [started, middle, State.liveWords, State.put, State.advance] using trace

theorem started_frame (state : State width 8) (recordStart : Nat) :
    (started state recordStart).heap = state.heap ∧
    (started state recordStart).stack = state.stack ∧
    (started state recordStart).output = state.output ∧
    (started state recordStart).reg 1 = word width recordStart ∧
    (started state recordStart).reg 7 = word width state.heap.size ∧
    (∀ register : Fin 8, register ≠ 1 → register ≠ 7 →
      (started state recordStart).reg register = state.reg register) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [started, State.put, State.advance]
  · simp [started, State.put, State.advance]
  · intro register notOne notSeven
    simp [started, State.put, State.advance, notOne, notSeven]

/-- Four fetched instructions compare an actual cursor with an actual saved
endpoint. Both the outer record test and the inner body test use this code. -/
def TestAt (program : Program width 8) (entry header exit : Nat) (cursor : Fin 8) : Prop :=
  program[entry]? = some (.constant 3 (word width header)) ∧
  program[entry + 1]? = some (.load 4 3) ∧
  program[entry + 2]? = some (.xor 3 cursor 4) ∧
  program[entry + 3]? = some (.branchZero 3 (word width exit))

def testCompared (state : State width 8) (header cursor limit : Nat) : State width 8 :=
  (((state.advance.put 3 (word width header)).advance.put 4 (word width limit)).advance.put 3
    (word width (Nat.xor cursor limit)))

def testFinished (state : State width 8) (header cursor limit exit : Nat) : State width 8 :=
  Controller.Horn.RuleDispatch.branchFinished (testCompared state header cursor limit) 3 exit

private theorem advance_position (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word_value (width := width) entry fits]

theorem test_execution (program : Program width 8) (entry header pointer limit exit : Nat)
    (cursor : Fin 8) (state : State width 8)
    (present : TestAt program entry header exit cursor)
    (position : state.pc = word width entry) (running : state.halted = false)
    (bound : header < state.heap.size) (cell : state.heap[header]'bound = word width limit)
    (held : state.reg cursor = word width pointer) (notThree : cursor ≠ 3) (notFour : cursor ≠ 4)
    (capacity : entry + 4 < 2 ^ width) (headerFits : header < 2 ^ width)
    (pointerFits : pointer < 2 ^ width) (limitFits : limit < 2 ^ width) :
    Execution program state (testFinished state header pointer limit exit) 4 state.liveWords := by
  let a := state.advance.put 3 (word width header)
  let b := a.advance.put 4 (word width limit)
  let c := testCompared state header pointer limit
  have apc : a.pc = word width (entry + 1) := advance_position state entry position (by omega)
  have bpc : b.pc = word width (entry + 2) := by
    simpa [b, State.put, Nat.add_assoc] using advance_position a (entry + 1) apc (by omega)
  have cpc : c.pc = word width (entry + 3) := by
    simpa [c, testCompared, b, a, State.put, Nat.add_assoc] using
      advance_position b (entry + 2) bpc (by omega)
  have first : programStep program state = some a := by
    unfold programStep
    rw [position, word_value (width := width) entry (by omega), present.1]
    simp [step, a, running]
  have second : programStep program a = some b := by
    unfold programStep
    rw [apc, word_value (width := width) (entry + 1) (by omega), present.2.1]
    simp [step, b, a, State.put, State.advance, running, bound, cell,
      word_value (width := width) header headerFits]
  have third : programStep program b = some c := by
    unfold programStep
    rw [bpc, word_value (width := width) (entry + 2) (by omega), present.2.2.1]
    simp [step, c, testCompared, b, a, State.put, State.advance, running, held, notThree, notFour,
      word_value (width := width) pointer pointerFits, word_value (width := width) limit limitFits]
  have fourth := Controller.Horn.RuleDispatch.branch_execution program (entry + 3) exit 3
    present.2.2.2 c cpc (by simp [c, testCompared, State.put, State.advance, running]) (by omega)
  have trace := Execution.cons first (Execution.cons second (Execution.cons third fourth))
  simpa [testFinished, c, testCompared, b, a, State.liveWords, State.put, State.advance] using trace

/-- The exit condition is equality of decoded physical cursor words, not a
semantic remaining-length parameter. -/
theorem test_position (state : State width 8) (entry header pointer limit exit : Nat)
    (position : state.pc = word width entry)
    (capacity : entry + 4 < 2 ^ width)
    (pointerFits : pointer < 2 ^ width) (limitFits : limit < 2 ^ width) :
    (testFinished state header pointer limit exit).pc =
      word width (if pointer = limit then exit else entry + 4) := by
  have xorFits := Nat.xor_lt_two_pow pointerFits limitFits
  have pc : (testCompared state header pointer limit).pc = word width (entry + 3) := by
    simp [testCompared, State.put, State.advance, position,
      word_value (width := width) entry (by omega),
      word_value (width := width) (entry + 1) (by omega),
      word_value (width := width) (entry + 2) (by omega), Nat.add_assoc]
  have held : (testCompared state header pointer limit).reg 3 = word width (Nat.xor pointer limit) := by
    simp [testCompared, State.put]
  by_cases equal : pointer = limit
  · have zeroHeld : ((testCompared state header pointer limit).reg 3).val = 0 := by
      rw [held]
      simp [equal, Nat.xor_self, word]
    unfold testFinished Controller.Horn.RuleDispatch.branchFinished
    rw [ite_eq_left zeroHeld]
    simp [equal]
  · have different : Nat.xor pointer limit ≠ 0 := fun zero =>
      equal ((Controller.Horn.ResetPointer.xor_zero_iff _ _).mp zero)
    have value : (word width (Nat.xor pointer limit)).val = Nat.xor pointer limit :=
      word_value (width := width) (Nat.xor pointer limit) (by simpa using xorFits)
    have notZero : ((testCompared state header pointer limit).reg 3).val ≠ 0 := by
      rw [held, value]
      exact different
    unfold testFinished Controller.Horn.RuleDispatch.branchFinished
    rw [ite_eq_right notZero]
    simp [equal, State.advance, pc, word_value (width := width) (entry + 3) (by omega), Nat.add_assoc]

/-- A source-normalized row contributes its exact physical record offset and
retained positive incidences, including the distinct offsets of repeated rows. -/
def occurrences : List (Controller.CNF.Clause (Fin n)) → Nat → List (Nat × Fin n)
  | [], _ => []
  | clause :: rest, offset =>
      let rule := Controller.Horn.Worklist.compileClause clause
      rule.positives.map (fun label => (offset, label)) ++
        occurrences rest (offset + 3 + rule.positives.length)

/-- Every retained incidence names a real original packed record before its
fixed end; this is stronger than merely fitting a machine word. -/
theorem occurrence_row_bound (clauses : List (Controller.CNF.Clause (Fin n)))
    (start row : Nat) (label : Fin n) (member : (row, label) ∈ occurrences clauses start) :
    row < Controller.Horn.NormalizeLoop.recordOffset clauses start clauses.length := by
  induction clauses generalizing start with
  | nil => simp [occurrences] at member
  | cons clause rest ih =>
      let rule := Controller.Horn.Worklist.compileClause clause
      have split : (row, label) ∈ rule.positives.map (fun channel => (start, channel)) ∨
          (row, label) ∈ occurrences rest (start + 3 + rule.positives.length) := by
        simpa only [occurrences, rule, List.mem_append] using member
      rcases split with first | tail
      · obtain ⟨channel, _, pair⟩ := List.mem_map.mp first
        have equal : start = row := congrArg Prod.fst pair
        simp only [Controller.Horn.NormalizeLoop.recordOffset, List.take_length,
          List.map_cons, List.sum_cons]
        omega
      · have bound := ih (start + 3 + rule.positives.length) tail
        unfold Controller.Horn.NormalizeLoop.recordOffset at bound ⊢
        simp only [List.take_length, List.map_cons, List.sum_cons] at bound ⊢
        dsimp only [rule] at bound
        omega

/-- Ghost bucket heads follow the actual chronological two-word allocations. -/
def heads (start : Nat) : List (Nat × Fin n) → Fin n → Nat
  | [], _ => 0
  | incidence :: rest, label =>
      let tailHead := heads (start + 2) rest label
      if tailHead = 0 then (if incidence.2 = label then start else 0) else tailHead

/-- One chronological node replaces exactly its own bucket head. -/
theorem heads_append (start : Nat) (positive : 0 < start) (items : List (Nat × Fin n))
    (row : Nat) (label query : Fin n) :
    heads start (items ++ [(row, label)]) query =
      if query = label then start + 2 * items.length else heads start items query := by
  induction items generalizing start with
  | nil =>
      by_cases same : query = label
      · subst query
        simp [heads]
      · simp [heads, same, Ne.symm same]
  | cons incidence rest ih =>
      have tail := ih (start + 2) (by omega)
      have allocated : start + 2 + 2 * rest.length ≠ 0 := by omega
      by_cases same : query = label
      · subst query
        simp only [List.cons_append, heads, List.length_cons] at ⊢
        rw [tail]
        simp [allocated]
        all_goals omega
      · simp only [List.cons_append, heads, List.length_cons]
        rw [tail]
        simp only [ite_eq_right same]

/-- A real bucket head is nil or lies inside the prefix already allocated.
This supplies the kernel's previous-pointer bound from the index invariant. -/
theorem heads_bound (start : Nat) (positive : 0 < start) (items : List (Nat × Fin n))
    (label : Fin n) : heads start items label < start + 2 * items.length := by
  induction items generalizing start with
  | nil => simp only [heads, List.length_nil, Nat.mul_zero, Nat.add_zero]; exact positive
  | cons incidence rest ih =>
      have tail := ih (start + 2) (by omega)
      simp only [heads, List.length_cons]
      split
      · split <;> omega
      · omega

/-- Existing physical records are transported only through an exact old-cell
frame; their immutable fields are never reconstructed from mutable counts. -/
theorem record_frame (rule : Controller.Horn.Worklist.Rule (Fin n))
    (offset : Nat) (before after : Array (Word width))
    (stored : Controller.Horn.RuleCopy.Stored rule offset before)
    (growth : before.size ≤ after.size)
    (frame : ∀ index, offset ≤ index → index < before.size → after[index]? = before[index]?) :
    Controller.Horn.RuleCopy.Stored rule offset after := by
  have cell (index : Nat) (above : offset ≤ index) (inside : index < before.size) :
      after[index]'(by omega) = before[index]'inside := by
    have exactCell := frame index above inside
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem inside] at exactCell
    exact Option.some.inj exactCell
  refine ⟨by have := stored.fits; omega, stored.countFits, ?_, ?_, ?_, ?_⟩
  · exact (cell offset (by omega) (by have := stored.fits; omega)).trans stored.tagValue
  · exact (cell (offset + 1) (by omega) (by have := stored.fits; omega)).trans stored.headValue
  · exact (cell (offset + 2) (by omega) (by have := stored.fits; omega)).trans stored.countValue
  · refine ⟨by have := stored.body.fits; omega, ?_⟩
    intro position
    exact (cell (offset + 3 + position.val) (by omega)
      (by have := stored.body.fits; have := position.isLt; omega)).trans (stored.body.entry position)

/-- Each allocated node points strictly backward to the last earlier occurrence
in the same bucket. The decoded row address is an original record offset. -/
structure PhysicalIndex (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base processed : Nat) (heap : Array (Word width)) : Prop where
  prefixBound : processed ≤ (occurrences clauses recordStart).length
  endpoint : heap.size = recordEnd + 2 * processed
  headValues : ∀ label : Fin n,
    heap[headAddress base label]? =
      some (word width (heads recordEnd ((occurrences clauses recordStart).take processed) label))
  nodes : ∀ index : Fin processed,
    NodeStored
      ((occurrences clauses recordStart)[index.val]'(by have := index.isLt; omega)).1
      (heads recordEnd ((occurrences clauses recordStart).take index.val)
        ((occurrences clauses recordStart)[index.val]'(by have := index.isLt; omega)).2)
      (recordEnd + 2 * index.val) heap
  records : ∀ index : Fin clauses.length,
    Controller.Horn.RuleCopy.Stored (Controller.Horn.Worklist.compileClause clauses[index.val])
      (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) heap
  originalEnd : recordEnd = Controller.Horn.NormalizeLoop.recordOffset clauses recordStart clauses.length
  separation : base + 2 * n + 1 ≤ recordStart
  positiveEnd : 0 < recordEnd

/-- The cold normalizer gives the empty physical index without an additional
channel scan or a preloaded normalized-incidence table. -/
theorem initial (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses) (recordStart : Nat)
    (marks : Controller.Horn.Worklist.IndexedNormalize.Marks n) (state : State width 8)
    (stored : Controller.Horn.NormalizeLoop.Invariant clauses layout recordStart clauses.length marks state) :
    PhysicalIndex clauses recordStart state.heap.size layout.base 0 state.heap := by
  refine ⟨by omega, by omega, ?_, ?_, ?_, stored.records.endpoint, ?_, ?_⟩
  · intro label
    simpa [heads] using (scratch_zero stored label).1
  · intro index
    exact Fin.elim0 index
  · intro index
    exact stored.records.entry index
  · have := stored.recordsAbove
    omega
  · have lower := stored.recordsAbove
    have endpoint := stored.records.endpoint
    unfold Controller.Horn.NormalizeLoop.recordOffset at endpoint
    omega

end Controller.Horn.IndexScan
