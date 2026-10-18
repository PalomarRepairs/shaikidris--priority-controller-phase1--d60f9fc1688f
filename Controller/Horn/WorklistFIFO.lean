module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Horn.WorklistBucketComplete

@[expose] public section

/-! FIFO cursors are fetched from preallocated scratch headers. The next
active label and bucket pointer are read from the existing queue and original
head cells; advancing the cursor allocates no storage. -/
namespace Controller.Horn.WorklistFIFO
open Controller.Cost Controller.Horn.WorklistPropagation
variable {width n : Nat}

def headSlot (base : Nat) : Nat := base + 2 * n
def activeSlot (base : Nat) : Nat := base + 2 * n + 2

def fetchCode (width base entry done bucket : Nat) : Program width 8 :=
  #[.constant 0 (word width (headSlot (n := n) base)), .load 0 0,
    .constant 3 (word width (Controller.Horn.WorklistBucketReady.tailSlot (n := n) base)), .load 4 3,
    .xor 3 0 4, .branchZero 3 (word width done), .load 1 0,
    .constant 3 (word width (activeSlot (n := n) base)), .store 3 1,
    .add 3 1 1, .constant 7 (word width base), .add 3 3 7,
    .load 0 3, .branchZero 2 (word width bucket)]

def FetchAt (program : Program width 8) (base entry done bucket : Nat) : Prop :=
  ∀ phase : Fin 14, program[entry + phase.val]? = (fetchCode (n := n) width base entry done bucket)[phase.val]?

def advanceCode (width base fetch : Nat) : Program width 8 :=
  #[.constant 3 (word width (headSlot (n := n) base)), .load 0 3, .add 0 0 5,
    .store 3 0, .branchZero 2 (word width fetch)]

def AdvanceAt (program : Program width 8) (base entry fetch : Nat) : Prop :=
  ∀ phase : Fin 5, program[entry + phase.val]? = (advanceCode (n := n) width base fetch)[phase.val]?

@[simp] theorem fetch_size (width base entry done bucket : Nat) : (fetchCode (n := n) width base entry done bucket).size = 14 := rfl
@[simp] theorem advance_size (width base fetch : Nat) : (advanceCode (n := n) width base fetch).size = 5 := rfl

private theorem word_val (value : Nat) (fits : value < 2 ^ width) : (word width value).val = value := Nat.mod_eq_of_lt fits
private theorem fetched (program : Program width 8) (state : State width 8) (entry : Nat)
    (instruction : Instruction width 8) (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) : programStep program state = step instruction state := by
  unfold programStep
  rw [position, word_val entry fits, present]
  rfl
private theorem advance_pc (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word_val entry fits]

def headLoaded (state : State width 8) (base pointer : Nat) : State width 8 :=
  ((state.advance.put 0 (word width (headSlot (n := n) base))).advance.put 0 (word width pointer))

/-- Two fetched instructions load the actual saved FIFO head cursor. -/
theorem head_load_execution (program : Program width 8) (base entry done bucket pointer : Nat) (state : State width 8)
    (present : FetchAt (n := n) program base entry done bucket)
    (bound : headSlot (n := n) base < state.heap.size)
    (cell : state.heap[headSlot (n := n) base]'bound = word width pointer)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 14 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    Execution program state (headLoaded (n := n) state base pointer) 2 state.liveWords ∧
      (headLoaded (n := n) state base pointer).pc = word width (entry + 2) ∧
      (headLoaded (n := n) state base pointer).reg 0 = word width pointer ∧
      (∀ register : Fin 8, register ≠ 0 → (headLoaded (n := n) state base pointer).reg register = state.reg register) := by
  let first := state.advance.put 0 (word width (headSlot (n := n) base))
  have pc : first.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have transition0 : programStep program state = some first := by
    rw [fetched program state entry (.constant 0 (word width (headSlot (n := n) base))) position (by omega)
      (by simpa [fetchCode] using present ⟨0, by decide⟩)]
    simp [step, first, running]
  have transition1 : programStep program first = some (headLoaded (n := n) state base pointer) := by
    rw [fetched program first (entry + 1) (.load 0 0) pc (by omega)
      (by simpa [fetchCode] using present ⟨1, by decide⟩)]
    simp [step, first, headLoaded, State.put, State.advance, running, bound, cell,
      word_val (width := width) (headSlot (n := n) base) (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [headLoaded, first, State.put, State.advance, State.liveWords] using
      Execution.cons transition0 (Execution.cons transition1 (Execution.refl _))
  · simpa only [headLoaded, first, State.put] using advance_pc first (entry + 1) pc (by omega)
  · simp [headLoaded, State.put]
  · intro register different
    simp [headLoaded, State.put, State.advance, different]

/-- The fixed FIFO comparison uses the stored tail word, including pending
labels, and never receives a semantic remaining-length counter. -/
theorem header_test_execution (program : Program width 8) (base entry done bucket pointer tail : Nat)
    (state : State width 8) (present : FetchAt (n := n) program base entry done bucket)
    (headBound : headSlot (n := n) base < state.heap.size)
    (headValue : state.heap[headSlot (n := n) base]'headBound = word width pointer)
    (tailBound : Controller.Horn.WorklistBucketReady.tailSlot (n := n) base < state.heap.size)
    (tailValue : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]'tailBound = word width tail)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 14 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (pointerFits : pointer < 2 ^ width) (tailFits : tail < 2 ^ width) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.pc = word width (if pointer = tail then done else entry + 6) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      final.reg 0 = word width pointer ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → register ≠ 4 → final.reg register = state.reg register) := by
  obtain ⟨first, pc, held, frame⟩ := head_load_execution program base entry done bucket pointer state present headBound headValue position running capacity room
  let loaded := headLoaded (n := n) state base pointer
  have loadedHeap : loaded.heap = state.heap := rfl
  have loadedRunning : loaded.halted = false := running
  have testAt : IndexScan.TestAt program (entry + 2) (Controller.Horn.WorklistBucketReady.tailSlot (n := n) base) done 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [fetchCode] using present ⟨2, by decide⟩
    · simpa [fetchCode, Nat.add_assoc] using present ⟨3, by decide⟩
    · simpa [fetchCode, Nat.add_assoc] using present ⟨4, by decide⟩
    · simpa [fetchCode, Nat.add_assoc] using present ⟨5, by decide⟩
  let final := IndexScan.testFinished loaded (Controller.Horn.WorklistBucketReady.tailSlot (n := n) base) pointer tail done
  have last := IndexScan.test_execution program (entry + 2) (Controller.Horn.WorklistBucketReady.tailSlot (n := n) base)
    pointer tail done 0 loaded testAt pc loadedRunning tailBound tailValue held (by decide) (by decide)
    (by omega) (by omega) pointerFits tailFits
  have finalPC := IndexScan.test_position loaded (entry + 2) (Controller.Horn.WorklistBucketReady.tailSlot (n := n) base)
    pointer tail done pc (by omega) pointerFits tailFits
  have branchFrame := Controller.Horn.RuleDispatch.branchFinished_frame
    (IndexScan.testCompared loaded (Controller.Horn.WorklistBucketReady.tailSlot (n := n) base) pointer tail) 3 done
  have loadedLive : loaded.liveWords = state.liveWords := rfl
  have registers : final.reg = (IndexScan.testCompared loaded (Controller.Horn.WorklistBucketReady.tailSlot (n := n) base) pointer tail).reg := branchFrame.1
  refine ⟨final, ?_, by simpa only [Nat.add_assoc, Nat.reduceAdd] using finalPC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [loadedLive, Nat.max_self, Nat.reduceAdd] using first.append last
  · exact branchFrame.2.1
  · exact branchFrame.2.2.1
  · exact branchFrame.2.2.2.1
  · exact branchFrame.2.2.2.2.1.trans running
  · rw [registers]
    simp [IndexScan.testCompared, State.put, State.advance, loaded, headLoaded]
  · intro register notZero notThree notFour
    rw [registers]
    simp [IndexScan.testCompared, State.put, State.advance, loaded, headLoaded, notZero, notThree, notFour]

/-- Five fetched instructions advance the saved physical queue cursor and
return to the fixed FIFO fetch entry. -/
theorem head_advance_execution (program : Program width 8) (base entry fetch pointer : Nat) (state : State width 8)
    (present : AdvanceAt (n := n) program base entry fetch)
    (bound : headSlot (n := n) base < state.heap.size)
    (cell : state.heap[headSlot (n := n) base]'bound = word width pointer)
    (one : state.reg 5 = word width 1) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 5 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (nextFits : pointer + 1 < 2 ^ width) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.heap = state.heap.set (headSlot (n := n) base) (word width (pointer + 1)) bound ∧
      final.reg 0 = word width (pointer + 1) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 3 → final.reg register = state.reg register) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width fetch ∧ final.halted = false := by
  let s1 := state.advance.put 3 (word width (headSlot (n := n) base))
  let s2 := s1.advance.put 0 (word width pointer)
  let s3 := s2.advance.put 0 (word width (pointer + 1))
  let s4 : State width 8 := { s3.advance with heap := state.heap.set (headSlot (n := n) base) (word width (pointer + 1)) bound }
  let final := Controller.Horn.RuleDispatch.branchFinished s4 2 fetch
  have pc1 : s1.pc = word width (entry + 1) := advance_pc state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by simpa only [s4, Nat.add_assoc, Nat.reduceAdd] using advance_pc s3 (entry + 3) pc3 (by omega)
  have first : programStep program state = some s1 := by
    rw [fetched program state entry (.constant 3 (word width (headSlot (n := n) base))) position (by omega)
      (by simpa [advanceCode] using present ⟨0, by decide⟩)]
    simp [step, s1, running]
  have second : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.load 0 3) pc1 (by omega)
      (by simpa [advanceCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, State.put, State.advance, running, bound, cell,
      word_val (width := width) (headSlot (n := n) base) (by omega)]
  have third : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 0 0 5) pc2 (by omega)
      (by simpa [advanceCode] using present ⟨2, by decide⟩)]
    simp [step, s1, s2, s3, State.put, State.advance, running, one,
      word_val (width := width) pointer (by omega), word_val (width := width) 1 (by omega)]
  have fourth : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.store 3 0) pc3 (by omega)
      (by simpa [advanceCode] using present ⟨3, by decide⟩)]
    simp [step, s1, s2, s3, s4, State.put, State.advance, running, bound,
      word_val (width := width) (headSlot (n := n) base) (by omega)]
  have last := Controller.Horn.RuleDispatch.branch_execution program (entry + 4) fetch 2
    (by simpa [advanceCode] using present ⟨4, by decide⟩) s4 pc4 running (by omega)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame s4 2 fetch
  have finalPC : final.pc = word width fetch := by
    have zeroHeld : s4.reg 2 = word width 0 := by simp [s4, s3, s2, s1, State.put, State.advance, zero]
    simp [final, Controller.Horn.RuleDispatch.branchFinished, zeroHeld, word]
  refine ⟨final, ?_, frame.2.1, ?_, ?_, ?_, frame.2.2.1, frame.2.2.2.1, finalPC, frame.2.2.2.2.1.trans running⟩
  · simpa [final, s4, s3, s2, s1, State.put, State.advance, State.liveWords] using
      Execution.cons first (Execution.cons second (Execution.cons third (Execution.cons fourth last)))
  · rw [frame.1]
    simp [s4, s3, State.put, State.advance]
  · intro register notZero notThree
    rw [frame.1]
    simp [s4, s3, s2, s1, State.put, State.advance, notZero, notThree]
  · rw [frame.2.1]
    simp [s4]

/-- The actual FIFO header store preserves the original spine, all queue/off
cells, and every source row. Its range is derived from cold scratch layout. -/
theorem head_store_frame (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (queue : List (Fin n)) (counts : Fin clauses.length → Nat)
    (fired : Fin clauses.length → Bool) (heap : Array (Word width)) (value : Word width)
    (spine : Spine clauses recordStart recordEnd base heap)
    (fifo : Controller.Horn.WorklistMark.Stored queue base heap)
    (rows : ∀ index : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) (counts index) (fired index) heap)
    (separated : base + 5 * n + 4 ≤ recordStart) :
    let changed := heap.set (headSlot (n := n) base) value (by have := fifo.fits; unfold headSlot; omega)
    Spine clauses recordStart recordEnd base changed ∧ Controller.Horn.WorklistMark.Stored queue base changed ∧
      (∀ index : Fin clauses.length,
        Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) (counts index) (fired index) changed) := by
  have bound : headSlot (n := n) base < heap.size := by have := fifo.fits; unfold headSlot; omega
  have endLower : recordStart ≤ recordEnd := by
    rw [spine.originalEnd]
    unfold Controller.Horn.NormalizeLoop.recordOffset
    omega
  refine ⟨Controller.Horn.WorklistBucketChain.spine_store clauses recordStart recordEnd base
    (headSlot (n := n) base) heap spine bound (by unfold headSlot; omega)
    (by unfold headSlot; omega) value,
    Controller.Horn.WorklistBucketChain.fifo_store queue base (headSlot (n := n) base) heap fifo bound
      (Or.inl ⟨by unfold headSlot; omega, by unfold headSlot Controller.Horn.WorklistMark.queueStart; omega⟩) value, ?_⟩
  intro index
  apply Controller.Horn.WorklistBucketChain.mutable_store_outside
    (Controller.Horn.Worklist.compileClause clauses[index.val])
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) (counts index)
    (headSlot (n := n) base) (fired index) heap (rows index) bound ?_ value
  left
  have lower : recordStart ≤ Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val := by
    unfold Controller.Horn.NormalizeLoop.recordOffset
    omega
  unfold headSlot
  omega

/-- Eight fetched instructions read one actual queued label, save it in the
scratch active header, and load its original immutable bucket head. -/
theorem label_bucket_execution (program : Program width 8) (base entry done bucket pointer next : Nat)
    (queue : List (Fin n)) (label : Fin n) (state : State width 8)
    (present : FetchAt (n := n) program base entry done bucket)
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (pointerBound : pointer < state.heap.size)
    (labelValue : state.heap[pointer]'pointerBound = word width label.val)
    (bucketValue : state.heap[Controller.Horn.WorklistStorage.headAddress base label]'(by have := fifo.fits; have := label.isLt; unfold Controller.Horn.WorklistStorage.headAddress; omega) = word width next)
    (held : state.reg 0 = word width pointer) (zero : state.reg 2 = word width 0)
    (position : state.pc = word width (entry + 6)) (running : state.halted = false)
    (capacity : entry + 14 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ final, Execution program state final 8 state.liveWords ∧
      final.heap = state.heap.set (activeSlot (n := n) base) (word width label.val) (by have := fifo.fits; unfold activeSlot; omega) ∧
      final.reg 0 = word width next ∧ final.reg 1 = word width label.val ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 3 → register ≠ 7 → final.reg register = state.reg register) ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width bucket ∧ final.halted = false := by
  have slotBound : activeSlot (n := n) base < state.heap.size := by have := fifo.fits; unfold activeSlot; omega
  have headBound : Controller.Horn.WorklistStorage.headAddress base label < state.heap.size := by
    have := fifo.fits; have := label.isLt; unfold Controller.Horn.WorklistStorage.headAddress; omega
  have slotDifferent : activeSlot (n := n) base ≠ Controller.Horn.WorklistStorage.headAddress base label := by
    have := label.isLt; unfold activeSlot Controller.Horn.WorklistStorage.headAddress; omega
  have labelFits : label.val < 2 ^ width := by have := fifo.fits; have := label.isLt; omega
  have doubledFits : 2 * label.val < 2 ^ width := by have := fifo.fits; have := label.isLt; omega
  have baseFits : base < 2 ^ width := by have := fifo.fits; omega
  let s1 := state.advance.put 1 (word width label.val)
  let s2 := s1.advance.put 3 (word width (activeSlot (n := n) base))
  let s3 : State width 8 := { s2.advance with heap := state.heap.set (activeSlot (n := n) base) (word width label.val) slotBound }
  let s4 := s3.advance.put 3 (word width (2 * label.val))
  let s5 := s4.advance.put 7 (word width base)
  let s6 := s5.advance.put 3 (word width (Controller.Horn.WorklistStorage.headAddress base label))
  let s7 := s6.advance.put 0 (word width next)
  let final := Controller.Horn.RuleDispatch.branchFinished s7 2 bucket
  have pc1 : s1.pc = word width (entry + 7) := by simpa only [s1, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc state (entry + 6) position (by omega)
  have pc2 : s2.pc = word width (entry + 8) := by simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s1 (entry + 7) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 9) := by simpa only [s3, Nat.add_assoc, Nat.reduceAdd] using advance_pc s2 (entry + 8) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 10) := by simpa only [s4, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s3 (entry + 9) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 11) := by simpa only [s5, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s4 (entry + 10) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 12) := by simpa only [s6, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s5 (entry + 11) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 13) := by simpa only [s7, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_pc s6 (entry + 12) pc6 (by omega)
  have t1 : programStep program state = some s1 := by
    rw [fetched program state (entry + 6) (.load 1 0) position (by omega) (by simpa [fetchCode] using present ⟨6, by decide⟩)]
    simp [step, running, held, word_val (width := width) pointer (by omega), pointerBound, labelValue, s1]
  have t2 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 7) (.constant 3 (word width (activeSlot (n := n) base))) pc1 (by omega) (by simpa [fetchCode] using present ⟨7, by decide⟩)]
    simp [step, s1, s2, State.put, State.advance, running]
  have t3 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 8) (.store 3 1) pc2 (by omega) (by simpa [fetchCode] using present ⟨8, by decide⟩)]
    simp [step, s1, s2, s3, State.put, State.advance, running, slotBound,
      word_val (width := width) (activeSlot (n := n) base) (by omega)]
  have t4 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 9) (.add 3 1 1) pc3 (by omega) (by simpa [fetchCode] using present ⟨9, by decide⟩)]
    simp [step, s1, s2, s3, s4, State.put, State.advance, running, word_val (width := width) label.val labelFits, two_mul]
  have t5 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 10) (.constant 7 (word width base)) pc4 (by omega) (by simpa [fetchCode] using present ⟨10, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, State.put, State.advance, running]
  have t6 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 11) (.add 3 3 7) pc5 (by omega) (by simpa [fetchCode] using present ⟨11, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, State.put, State.advance, running,
      word_val (width := width) (2 * label.val) doubledFits, word_val (width := width) base baseFits,
      Controller.Horn.WorklistStorage.headAddress, Nat.add_comm]
  have savedHead : s6.heap[Controller.Horn.WorklistStorage.headAddress base label]'(by simpa [s6, s5, s4, s3, State.put, State.advance] using headBound) = word width next := by
    exact (Array.getElem_set_ne slotBound headBound slotDifferent).trans bucketValue
  have headAfter : (state.heap.set (activeSlot (n := n) base) (word width label.val) slotBound)[Controller.Horn.WorklistStorage.headAddress base label]'(by simpa using headBound) = word width next :=
    (Array.getElem_set_ne slotBound headBound slotDifferent).trans bucketValue
  have t7 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 12) (.load 0 3) pc6 (by omega) (by simpa [fetchCode] using present ⟨12, by decide⟩)]
    simp [step, s6, s7, State.put, State.advance, headAfter,
      word_val (width := width) (Controller.Horn.WorklistStorage.headAddress base label) (by omega),
      s5, s4, s3, s2, s1, running, headBound]
  have last := Controller.Horn.RuleDispatch.branch_execution program (entry + 13) bucket 2
    (by simpa [fetchCode] using present ⟨13, by decide⟩) s7 pc7 (by simp [s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running]) (by omega)
  have frame := Controller.Horn.RuleDispatch.branchFinished_frame s7 2 bucket
  have finalPC : final.pc = word width bucket := by
    have zeroHeld : s7.reg 2 = word width 0 := by simp [s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, zero]
    simp [final, Controller.Horn.RuleDispatch.branchFinished, zeroHeld, word]
  refine ⟨final, ?_, frame.2.1, ?_, ?_, ?_, ?_, frame.2.2.1, frame.2.2.2.1, finalPC, frame.2.2.2.2.1.trans running⟩
  · simpa [final, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, State.liveWords] using
      Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 last))))))
  · rw [frame.1]; simp [s7, State.put]
  · rw [frame.1]; simp [s7, s6, s5, s4, s3, s2, s1, State.put, State.advance]
  · intro register notZero notLabel notThree notBase
    rw [frame.1]
    simp [s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, notZero, notLabel, notThree, notBase]
  · rw [frame.2.1]; simp [s7, s6, s5, s4, s3, State.put, State.advance]

theorem active_store_frame (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base : Nat) (queue : List (Fin n)) (counts : Fin clauses.length → Nat)
    (fired : Fin clauses.length → Bool) (heap : Array (Word width)) (value : Word width)
    (spine : Spine clauses recordStart recordEnd base heap)
    (fifo : Controller.Horn.WorklistMark.Stored queue base heap)
    (rows : ∀ index : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) (counts index) (fired index) heap)
    (separated : base + 5 * n + 4 ≤ recordStart) :
    let changed := heap.set (activeSlot (n := n) base) value (by have := fifo.fits; unfold activeSlot; omega)
    Spine clauses recordStart recordEnd base changed ∧ Controller.Horn.WorklistMark.Stored queue base changed ∧
      (∀ index : Fin clauses.length,
        Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
          (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) (counts index) (fired index) changed) := by
  have bound : activeSlot (n := n) base < heap.size := by have := fifo.fits; unfold activeSlot; omega
  have endLower : recordStart ≤ recordEnd := by
    rw [spine.originalEnd]
    unfold Controller.Horn.NormalizeLoop.recordOffset
    omega
  refine ⟨Controller.Horn.WorklistBucketChain.spine_store clauses recordStart recordEnd base
    (activeSlot (n := n) base) heap spine bound (by unfold activeSlot; omega)
    (by unfold activeSlot; omega) value,
    Controller.Horn.WorklistBucketChain.fifo_store queue base (activeSlot (n := n) base) heap fifo bound
      (Or.inl ⟨by unfold activeSlot; omega, by unfold activeSlot Controller.Horn.WorklistMark.queueStart; omega⟩) value, ?_⟩
  intro index
  apply Controller.Horn.WorklistBucketChain.mutable_store_outside
    (Controller.Horn.Worklist.compileClause clauses[index.val])
    (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val) (counts index)
    (activeSlot (n := n) base) (fired index) heap (rows index) bound ?_ value
  left
  have lower : recordStart ≤ Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val := by
    unfold Controller.Horn.NormalizeLoop.recordOffset
    omega
  unfold activeSlot
  omega

/-- Fourteen fetched instructions turn the actual saved FIFO head and
original bucket-head cell into the complete initial physical bucket invariant. -/
theorem fetch_execution (clauses : List (Controller.CNF.Clause (Fin n)))
    (recordStart recordEnd base entry done bucket : Nat) (program : Program width 8)
    (queue : List (Fin n)) (head : Nat) (fired : Fin clauses.length → Bool) (state : State width 8)
    (spine : Spine clauses recordStart recordEnd base state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored queue base state.heap)
    (rows : ∀ index : Fin clauses.length,
      Controller.Horn.WorklistStorage.MutableStored (Controller.Horn.Worklist.compileClause clauses[index.val])
        (Controller.Horn.NormalizeLoop.recordOffset clauses recordStart index.val)
        (Controller.Horn.WorklistPropagation.remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take head))
        (fired index) state.heap)
    (firedZero : Controller.Horn.WorklistPropagationStep.FiredZero clauses recordStart queue head none [] fired)
    (headBound : head < queue.length)
    (headValue : state.heap[headSlot (n := n) base]? = some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + head)))
    (tailValue : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
      some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + queue.length)))
    (separated : base + 5 * n + 4 ≤ recordStart)
    (present : FetchAt (n := n) program base entry done bucket)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (decrement : state.reg 6 = word width (2 ^ width - 1))
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 14 < 2 ^ width) (room : state.heap.size < 2 ^ width) :
    ∃ active final, queue[head]? = some active ∧ Execution program state final 14 state.liveWords ∧
      Controller.Horn.WorklistBucketRun.Snapshot clauses recordStart recordEnd base bucket queue head active [] fired
        (IndexScan.occurrences clauses recordStart).length final ∧
      final.heap.size = state.heap.size ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.heap[headSlot (n := n) base]? = some (word width (Controller.Horn.WorklistMark.queueStart (n := n) base + head)) := by
  let active : Fin n := queue[head]
  let pointer := Controller.Horn.WorklistMark.queueStart (n := n) base + head
  let tail := Controller.Horn.WorklistMark.queueStart (n := n) base + queue.length
  have headSlotBound : headSlot (n := n) base < state.heap.size := by have := fifo.fits; unfold headSlot; omega
  have tailSlotBound : Controller.Horn.WorklistBucketReady.tailSlot (n := n) base < state.heap.size := by
    have := fifo.fits; unfold Controller.Horn.WorklistBucketReady.tailSlot; omega
  have pointerBound : pointer < state.heap.size := by have := fifo.queue.fits; dsimp [pointer]; omega
  have tailFits : tail < 2 ^ width := by have := fifo.queue.fits; dsimp [tail]; omega
  have headCell : state.heap[headSlot (n := n) base]'headSlotBound = word width pointer := by
    simpa only [Array.getElem?_eq_getElem headSlotBound, Option.some.injEq] using headValue
  have tailCell : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]'tailSlotBound = word width tail := by
    simpa only [Array.getElem?_eq_getElem tailSlotBound, Option.some.injEq] using tailValue
  obtain ⟨tested, first, testPC, testHeap, testStack, testOutput, testRunning, held, testRegs⟩ :=
    header_test_execution program base entry done bucket pointer tail state present headSlotBound headCell tailSlotBound tailCell
      position running capacity room (by omega) tailFits
  have different : pointer ≠ tail := by dsimp [pointer, tail]; omega
  have bodyPC : tested.pc = word width (entry + 6) := by simpa only [ite_eq_right different] using testPC
  have labelCell : tested.heap[pointer]'(by simpa only [testHeap] using pointerBound) = word width active.val := by
    simpa only [testHeap] using fifo.queue.entry ⟨head, headBound⟩
  have bucketBound : Controller.Horn.WorklistStorage.headAddress base active < state.heap.size := by
    have := fifo.fits; have := active.isLt; unfold Controller.Horn.WorklistStorage.headAddress; omega
  have bucketCell : tested.heap[Controller.Horn.WorklistStorage.headAddress base active]'(by simpa only [testHeap] using bucketBound) =
      word width (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) active) := by
    have value := spine.heads active
    simpa only [testHeap, Array.getElem?_eq_getElem bucketBound, Option.some.injEq] using value
  obtain ⟨final, last, finalHeap, finalNext, finalActive, finalRegs, size, stack, output, pc, live⟩ :=
    label_bucket_execution program base entry done bucket pointer
      (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) active) queue active tested present
      (by simpa only [testHeap] using fifo) (by simpa only [testHeap] using pointerBound) labelCell bucketCell held
      ((testRegs 2 (by decide) (by decide) (by decide)).trans zero) bodyPC testRunning capacity
      (by simpa only [testHeap] using room)
  have testedLive : tested.liveWords = state.liveWords := by unfold State.liveWords; rw [testHeap, testStack, testOutput]
  have actualHeap : final.heap = state.heap.set (activeSlot (n := n) base) (word width active.val)
      (by have := fifo.fits; unfold activeSlot; omega) := by simpa only [testHeap] using finalHeap
  obtain ⟨finalSpine, finalFifo, finalRows⟩ := active_store_frame clauses recordStart recordEnd base queue
    (fun index => Controller.Horn.WorklistPropagation.remaining (Controller.Horn.Worklist.compileClause clauses[index.val]) (queue.take head))
    fired state.heap (word width active.val) spine fifo rows separated
  have current : queue[head]? = some active := by simp only [List.getElem?_eq_getElem headBound]; rfl
  have fresh : active ∉ queue.take head := by
    have taken : (queue.take (head + 1)).Nodup := fifo.nodup.take
    rw [List.take_add_one, current] at taken
    have disjoint := (List.nodup_append.mp taken).2.2
    intro member
    exact disjoint active member active (by simp) rfl
  have invariant : Invariant clauses recordStart recordEnd base queue head (some active) []
      (IndexScan.heads recordEnd (IndexScan.occurrences clauses recordStart) active) fired final.heap := by
    refine ⟨?_, ?_, by omega, current.symm, by simp, ?_, ?_, ?_, ?_⟩
    · simpa only [actualHeap] using finalSpine
    · simpa only [actualHeap] using finalFifo
    · intro label member
      have equal : label = active := by simpa using member
      subst label
      exact ⟨[], rfl, LinkPrefix.nil _⟩
    · intro label member
      have equal : label = active := by simpa using member
      subst label
      exact List.getElem_mem headBound
    · intro label member
      have equal : label = active := by simpa using member
      subst label
      exact fresh
    · intro index
      simpa only [actualHeap, processedForRow, List.not_mem_nil, ite_false, List.append_nil] using finalRows index
  have finalFired : Controller.Horn.WorklistPropagationStep.FiredZero clauses recordStart queue head (some active) [] fired := by
    simpa only [Controller.Horn.WorklistPropagationStep.FiredZero, processedForRow, List.not_mem_nil, ite_false, List.append_nil] using firedZero
  have slotBound : activeSlot (n := n) base < state.heap.size := by have := fifo.fits; unfold activeSlot; omega
  have headFrame : final.heap[headSlot (n := n) base]? = state.heap[headSlot (n := n) base]? := by
    rw [actualHeap]
    exact Array.getElem?_set_ne slotBound (by unfold activeSlot headSlot; omega)
  have tailFrame : final.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? =
      state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := n) base]? := by
    rw [actualHeap]
    exact Array.getElem?_set_ne slotBound (by unfold activeSlot Controller.Horn.WorklistBucketReady.tailSlot; omega)
  refine ⟨active, final, current, ?_, ?_, size.trans (congrArg Array.size testHeap), stack.trans testStack,
    output.trans testOutput, headFrame.trans headValue⟩
  · simpa only [testedLive, Nat.max_self, Nat.reduceAdd] using first.append last
  · refine ⟨Nat.le_refl _, ?_, finalFired, tailFrame.trans tailValue, ?_, ?_, ?_, ?_, pc, live, ?_⟩
    · simpa only [List.take_length] using invariant
    · simpa only [List.take_length] using finalNext
    · exact (finalRegs 2 (by decide) (by decide) (by decide) (by decide)).trans ((testRegs 2 (by decide) (by decide) (by decide)).trans zero)
    · exact (finalRegs 5 (by decide) (by decide) (by decide) (by decide)).trans ((testRegs 5 (by decide) (by decide) (by decide)).trans one)
    · exact (finalRegs 6 (by decide) (by decide) (by decide) (by decide)).trans ((testRegs 6 (by decide) (by decide) (by decide)).trans decrement)
    · simpa only [size, testHeap] using room

end Controller.Horn.WorklistFIFO

