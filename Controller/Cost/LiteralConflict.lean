module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSteps

@[expose] public section

/-! Fetched contradiction checks on two stored sign bits. A check writes its
separate flag only when both signs are present and preserves all other cells. -/
namespace Controller.Cost.LiteralConflict
open Controller.Cost.RawTransferLoops Controller.Cost.GateProgram

def readCode (width address done : Nat) : Program width 8 :=
  #[.constant 0 (word width address), .load 1 0, .branchZero 1 (word width done)]

@[simp] theorem readCode_size : (readCode width address done).size = 3 := rfl

theorem read_execution (resident : Program width 8) (state : State width 8)
    (entry address done : Nat) (value : Bool)
    (physical : CodeAt resident entry (readCode width address done))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 3 < 2 ^ width) (booleanRoom : 1 < 2 ^ width)
    (addressRoom : address < 2 ^ width) (inside : address < state.heap.size)
    (stored : state.heap[address] = boolWord width value) :
    ∃ final, Execution resident state final 3 state.liveWords ∧
      final.pc = word width (if value then entry + 3 else done) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → final.reg index = state.reg index) := by
  obtain ⟨addressed, first, ap, av, ah, ast, ao, ar, af⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry address 0 state position running (by omega)
      (by simpa [readCode] using physical ⟨0, by simp⟩)
  have addressValue : (addressed.reg 0).val = address := by rw [av]; exact Nat.mod_eq_of_lt addressRoom
  obtain ⟨loaded, second, lp, lv, lh, lst, lo, lr, lf⟩ :=
    EnumerationSteps.load_execution resident addressed (entry + 1) 1 0 ap ar (by omega)
      (by rw [addressValue, ah]; exact inside)
      (by simpa [readCode] using physical ⟨1, by simp⟩)
  have loadedValue : loaded.reg 1 = boolWord width value := by rw [lv]; simpa [addressValue, ah] using stored
  have addressedLive : addressed.liveWords = state.liveWords := by simp only [State.liveWords, ah, ast, ao]
  have loadedLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, lh, lst, lo, ah, ast, ao]
  have finish : ∀ final, Execution resident loaded final 1 loaded.liveWords →
      final.pc = word width (if value then entry + 3 else done) →
      final.heap = loaded.heap → final.stack = loaded.stack → final.output = loaded.output →
      final.halted = false → (∀ index, final.reg index = loaded.reg index) →
      ∃ final, Execution resident state final 3 state.liveWords ∧
        final.pc = word width (if value then entry + 3 else done) ∧
        final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
        final.halted = false ∧
        (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → final.reg index = state.reg index) := by
    intro final third fp fh fs fo fr ff
    refine ⟨final, ?_, fp, fh.trans (lh.trans ah), fs.trans (lst.trans ast), fo.trans (lo.trans ao), fr, ?_⟩
    · simpa only [addressedLive, loadedLive, Nat.max_self, Nat.reduceAdd] using first.append (second.append third)
    · intro index notZero notOne
      rw [ff, lf index notOne, af index notZero]
  cases value with
  | false =>
    obtain ⟨final, trace, pc, heap, stack, output, active, frame⟩ :=
      EnumerationSteps.branch_taken resident loaded (entry + 2) done 1 lp lr (by omega)
        (by rw [loadedValue]; simp [boolWord, word])
        (by simpa [readCode] using physical ⟨2, by simp⟩)
    exact finish final trace pc heap stack output active frame
  | true =>
    obtain ⟨final, trace, pc, heap, stack, output, active, frame⟩ :=
      EnumerationSteps.branch_skipped resident loaded (entry + 2) done 1 lp lr (by omega)
        (by rw [loadedValue]; simp [boolWord, word, Nat.mod_eq_of_lt booleanRoom])
        (by simpa [readCode] using physical ⟨2, by simp⟩)
    exact finish final trace (by simpa [Nat.add_assoc] using pc) heap stack output active frame

def code (width entry positive negative flag : Nat) : Program width 8 :=
  readCode width positive (entry + 9) ++
    (readCode width negative (entry + 9) ++
      #[.constant 0 (word width flag), .constant 1 (boolWord width true), .store 0 1])

@[simp] theorem code_size : (code width entry positive negative flag).size = 9 := rfl

theorem execution (resident : Program width 8) (state : State width 8)
    (entry positive negative flag : Nat) (left right : Bool)
    (physical : CodeAt resident entry (code width entry positive negative flag))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 < 2 ^ width) (booleanRoom : 1 < 2 ^ width)
    (heapRoom : state.heap.size < 2 ^ width)
    (positiveBound : positive < state.heap.size) (negativeBound : negative < state.heap.size)
    (flagBound : flag < state.heap.size)
    (positiveStored : state.heap[positive] = boolWord width left)
    (negativeStored : state.heap[negative] = boolWord width right) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 9 ∧
      final.pc = word width (entry + 9) ∧
      final.heap = (if left && right then state.heap.set flag (boolWord width true) else state.heap) ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → final.reg index = state.reg index) := by
  have all := physical
  unfold code at all
  have firstAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have restAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  have restAt' : CodeAt resident (entry + 3)
      (readCode width negative (entry + 9) ++
        #[.constant 0 (word width flag), .constant 1 (boolWord width true), .store 0 1]) := by simpa using restAt
  have secondAt := RawSharedOrdered.takePrefix resident (entry + 3) _ _ restAt'
  have storeAt := RawSharedOrdered.takeSuffix resident (entry + 3) _ _ restAt'
  obtain ⟨tested, firstTrace, firstPC, firstHeap, firstStack, firstOutput, firstRunning, firstFrame⟩ :=
    read_execution resident state entry positive (entry + 9) left firstAt position running
      (by omega) booleanRoom (by omega) positiveBound positiveStored
  cases left with
  | false =>
    exact ⟨tested, 3, firstTrace, by decide, firstPC, firstHeap, firstStack, firstOutput, firstRunning, firstFrame⟩
  | true =>
    obtain ⟨testedRight, secondTrace, secondPC, secondHeap, secondStack, secondOutput, secondRunning, secondFrame⟩ :=
      read_execution resident tested (entry + 3) negative (entry + 9) right secondAt firstPC firstRunning
        (by omega) booleanRoom (by omega) (by rw [firstHeap]; exact negativeBound)
        (by simpa only [firstHeap] using negativeStored)
    have firstLive : tested.liveWords = state.liveWords := by simp only [State.liveWords, firstHeap, firstStack, firstOutput]
    have secondLive : testedRight.liveWords = state.liveWords := by
      simp only [State.liveWords, secondHeap, secondStack, secondOutput, firstHeap, firstStack, firstOutput]
    have combined := firstTrace.append secondTrace
    rw [firstLive, Nat.max_self] at combined
    cases right with
    | false =>
      refine ⟨testedRight, 6, combined, by decide, secondPC, secondHeap.trans firstHeap,
        secondStack.trans firstStack, secondOutput.trans firstOutput, secondRunning, ?_⟩
      intro index notZero notOne
      rw [secondFrame index notZero notOne, firstFrame index notZero notOne]
    | true =>
      obtain ⟨addressed, aTrace, aPC, aValue, aHeap, aStack, aOutput, aRunning, aFrame⟩ :=
        SharedEvaluationReclaim.constant_execution resident (entry + 6) flag 0 testedRight
          (by simpa [Nat.add_assoc] using secondPC) secondRunning (by omega)
          (by simpa using storeAt ⟨0, by simp⟩)
      obtain ⟨valued, vTrace, vPC, vValue, vHeap, vStack, vOutput, vRunning, vFrame⟩ :=
        SharedEvaluationReclaim.constant_execution resident (entry + 7) 1 1 addressed
          (by simpa [Nat.add_assoc] using aPC) aRunning (by omega)
          (by simpa [Nat.add_assoc, boolWord] using storeAt ⟨1, by simp⟩)
      have addressValue : (valued.reg 0).val = flag := by
        rw [vFrame 0 (by decide), aValue]; exact Nat.mod_eq_of_lt (by omega)
      obtain ⟨final, sTrace, sPC, sHeap, sStack, sOutput, sRunning, sFrame⟩ :=
        EnumerationSteps.store_execution resident valued (entry + 8) 0 1
          (by simpa [Nat.add_assoc] using vPC) vRunning (by omega)
          (by rw [addressValue, vHeap, aHeap, secondHeap, firstHeap]; exact flagBound)
          (by simpa [Nat.add_assoc] using storeAt ⟨2, by simp⟩)
      have aLive : addressed.liveWords = state.liveWords := by
        simp only [State.liveWords, aHeap, aStack, aOutput, secondHeap, secondStack, secondOutput, firstHeap, firstStack, firstOutput]
      have vLive : valued.liveWords = state.liveWords := by
        simp only [State.liveWords, vHeap, vStack, vOutput, aHeap, aStack, aOutput, secondHeap, secondStack, secondOutput,
          firstHeap, firstStack, firstOutput]
      refine ⟨final, 9, ?_, by decide, ?_, ?_, sStack.trans (vStack.trans (aStack.trans (secondStack.trans firstStack))),
        sOutput.trans (vOutput.trans (aOutput.trans (secondOutput.trans firstOutput))), sRunning, ?_⟩
      · simpa only [secondLive, aLive, vLive, Nat.max_self, Nat.reduceAdd] using
          combined.append (aTrace.append (vTrace.append sTrace))
      · simpa [Nat.add_assoc] using sPC
      · simp [sHeap, addressValue, vValue, vHeap, aHeap, secondHeap, firstHeap, boolWord]
      · intro index notZero notOne
        rw [sFrame, vFrame index notOne, aFrame index notZero,
          secondFrame index notZero notOne, firstFrame index notZero notOne]

def mark (heap : Array (Word width)) (flag : Nat) (value : Bool) : Array (Word width) :=
  if value then heap.setIfInBounds flag (boolWord width true) else heap

@[simp] theorem mark_size (heap : Array (Word width)) (flag : Nat) (value : Bool) :
    (mark heap flag value).size = heap.size := by cases value <;> simp [mark]

theorem mark_twice (heap : Array (Word width)) (flag : Nat) (left right : Bool) :
    mark (mark heap flag left) flag right = mark heap flag (left || right) := by
  cases left <;> cases right <;> simp [mark, Array.setIfInBounds_setIfInBounds]

theorem mark_frame (heap : Array (Word width)) (flag address : Nat) (value : Bool) (different : flag ≠ address) :
    (mark heap flag value)[address]? = heap[address]? := by
  cases value <;> simp [mark, different]

def scanCode (width flag : Nat) : Nat → List (Nat × Nat) → Program width 8
  | _, [] => #[]
  | entry, (positive, negative) :: rest => code width entry positive negative flag ++ scanCode width flag (entry + 9) rest

@[simp] theorem scanCode_size (width flag entry : Nat) (pairs : List (Nat × Nat)) :
    (scanCode width flag entry pairs).size = 9 * pairs.length := by
  induction pairs generalizing entry with
  | nil => rfl
  | cons pair rest ih => cases pair; simp [scanCode, ih]; omega

def collision (values : Nat → Bool) (pairs : List (Nat × Nat)) : Bool :=
  pairs.any fun pair => values pair.1 && values pair.2

theorem scan_execution (resident : Program width 8) (state : State width 8)
    (entry flag : Nat) (pairs : List (Nat × Nat)) (values : Nat → Bool)
    (physical : CodeAt resident entry (scanCode width flag entry pairs))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 * pairs.length < 2 ^ width) (booleanRoom : 1 < 2 ^ width)
    (heapRoom : state.heap.size < 2 ^ width) (flagBound : flag < state.heap.size)
    (readable : ∀ pair ∈ pairs, pair.1 < state.heap.size ∧ pair.2 < state.heap.size)
    (separate : ∀ pair ∈ pairs, flag ≠ pair.1 ∧ flag ≠ pair.2)
    (sources : ∀ pair ∈ pairs,
      state.heap[pair.1]? = some (boolWord width (values pair.1)) ∧
      state.heap[pair.2]? = some (boolWord width (values pair.2))) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 9 * pairs.length ∧
      final.pc = word width (entry + 9 * pairs.length) ∧
      final.heap = mark state.heap flag (collision values pairs) ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → final.reg index = state.reg index) := by
  induction pairs generalizing state entry with
  | nil => exact ⟨state, 0, Execution.refl state, by simp, by simpa using position,
      by simp [mark, collision], rfl, rfl, running, fun _ _ _ => rfl⟩
  | cons pair rest ih =>
    rcases pair with ⟨positive, negative⟩
    have firstAt := RawSharedOrdered.takePrefix resident entry _ _ physical
    have tailAt := RawSharedOrdered.takeSuffix resident entry _ _ physical
    have bounds := readable (positive, negative) (by simp)
    have cells := sources (positive, negative) (by simp)
    obtain ⟨next, firstTicks, firstTrace, firstTime, firstPC, firstHeap, firstStack, firstOutput,
        firstRunning, firstFrame⟩ :=
      execution resident state entry positive negative flag (values positive) (values negative) firstAt position running
        (by simp only [List.length_cons] at room; omega) booleanRoom heapRoom bounds.1 bounds.2 flagBound
        (by simpa only [Array.getElem?_eq_getElem bounds.1, Option.some.injEq] using cells.1)
        (by simpa only [Array.getElem?_eq_getElem bounds.2, Option.some.injEq] using cells.2)
    have nextHeap : next.heap = mark state.heap flag (values positive && values negative) := by
      simpa [mark, Array.setIfInBounds_def, flagBound] using firstHeap
    have nextSize : next.heap.size = state.heap.size := by rw [nextHeap, mark_size]
    obtain ⟨final, tailTicks, tailTrace, tailTime, finalPC, finalHeap, finalStack, finalOutput,
        finalRunning, finalFrame⟩ :=
      ih next (entry + 9) (by simpa only [scanCode, code_size] using tailAt) firstPC firstRunning
        (by simp only [List.length_cons] at room; omega) (by rw [nextSize]; exact heapRoom)
        (by rw [nextSize]; exact flagBound)
        (fun pair member => by rw [nextSize]; exact readable pair (by simp [member]))
        (fun pair member => separate pair (by simp [member]))
        (by
          intro pair member
          have distinct := separate pair (by simp [member])
          rw [nextHeap, mark_frame _ _ _ _ distinct.1, mark_frame _ _ _ _ distinct.2]
          exact sources pair (by simp [member]))
    have nextLive : next.liveWords = state.liveWords := by simp only [State.liveWords, nextSize, firstStack, firstOutput]
    refine ⟨final, firstTicks + tailTicks, ?_, ?_, ?_, ?_, finalStack.trans firstStack,
      finalOutput.trans firstOutput, finalRunning, ?_⟩
    · simpa only [nextLive, Nat.max_self] using firstTrace.append tailTrace
    · simp only [List.length_cons]; omega
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC
    · rw [finalHeap, nextHeap, mark_twice]
      rfl
    · intro index notZero notOne
      rw [finalFrame index notZero notOne, firstFrame index notZero notOne]

theorem mark_flag (heap : Array (Word width)) (flag : Nat) (old value : Bool)
    (inside : flag < heap.size) (stored : heap[flag] = boolWord width old) :
    (mark heap flag value)[flag]'(by simpa using inside) = boolWord width (old || value) := by
  cases value <;> simp [mark, stored, Array.setIfInBounds_def, inside]

theorem mark_push (heap : Array (Word width)) (old value : Bool) :
    mark (heap.push (boolWord width old)) heap.size value = heap.push (boolWord width (old || value)) := by
  cases value <;> simp [mark, Array.setIfInBounds_def, Array.set_push]

def jobCode (width entry flag zeroAddress : Nat) (pairs : List (Nat × Nat)) : Program width 8 :=
  #[.constant 0 (word width zeroAddress), .load 1 0, .allocate 1] ++ scanCode width flag (entry + 3) pairs

@[simp] theorem jobCode_size (width entry flag zeroAddress : Nat) (pairs : List (Nat × Nat)) :
    (jobCode width entry flag zeroAddress pairs).size = 3 + 9 * pairs.length := by simp [jobCode]

/-- Append a zero/contradiction flag from actual matrix cells. Only the newly
allocated flag can be written by the scan. -/
theorem job_execution (resident : Program width 8) (state : State width 8)
    (entry flag zeroAddress : Nat) (pairs : List (Nat × Nat)) (values : Nat → Bool) (old : Bool)
    (flagPosition : flag = state.heap.size)
    (physical : CodeAt resident entry (jobCode width entry flag zeroAddress pairs))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (3 + 9 * pairs.length) < 2 ^ width) (booleanRoom : 1 < 2 ^ width)
    (heapRoom : state.heap.size + 1 < 2 ^ width)
    (zeroBound : zeroAddress < state.heap.size) (zeroStored : state.heap[zeroAddress] = boolWord width old)
    (readable : ∀ pair ∈ pairs, pair.1 < state.heap.size ∧ pair.2 < state.heap.size)
    (sources : ∀ pair ∈ pairs,
      state.heap[pair.1]? = some (boolWord width (values pair.1)) ∧
      state.heap[pair.2]? = some (boolWord width (values pair.2))) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + 1) ∧
      ticks ≤ 3 + 9 * pairs.length ∧ final.pc = word width (entry + (3 + 9 * pairs.length)) ∧
      final.heap = state.heap.push (boolWord width (old || collision values pairs)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → final.reg index = state.reg index) := by
  have all := physical
  unfold jobCode at all
  have loadAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have scanAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  obtain ⟨addressed, aTrace, aPC, aValue, aHeap, aStack, aOutput, aRunning, aFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry zeroAddress 0 state position running (by omega)
      (by simpa using loadAt ⟨0, by simp⟩)
  have addressValue : (addressed.reg 0).val = zeroAddress := by rw [aValue]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨loaded, lTrace, lPC, lValue, lHeap, lStack, lOutput, lRunning, lFrame⟩ :=
    EnumerationSteps.load_execution resident addressed (entry + 1) 1 0 aPC aRunning (by omega)
      (by rw [addressValue, aHeap]; exact zeroBound)
      (by simpa using loadAt ⟨1, by simp⟩)
  have value : loaded.reg 1 = boolWord width old := by rw [lValue]; simpa [addressValue, aHeap] using zeroStored
  obtain ⟨appended, pTrace, pPC, pHeap, pStack, pOutput, pRunning, pFrame, pLive⟩ :=
    EnumerationSteps.allocate_execution resident loaded (entry + 2) 1
      (by simpa [Nat.add_assoc] using lPC) lRunning (by omega)
      (by rw [lHeap, aHeap]; omega)
      (by simpa using loadAt ⟨2, by simp⟩)
  have appendedHeap : appended.heap = state.heap.push (boolWord width old) := by rw [pHeap, value, lHeap, aHeap]
  have appendedSize : appended.heap.size = state.heap.size + 1 := by rw [appendedHeap]; simp
  obtain ⟨final, tailTicks, tailTrace, tailTime, finalPC, finalHeap, finalStack, finalOutput,
      finalRunning, finalFrame⟩ :=
    scan_execution resident appended (entry + 3) flag pairs values
      (by simpa using scanAt) (by simpa [Nat.add_assoc] using pPC) pRunning (by omega) booleanRoom
      (by rw [appendedSize]; exact heapRoom) (by rw [appendedSize, flagPosition]; omega)
      (fun pair member => by have bounds := readable pair member; rw [appendedSize]; omega)
      (fun pair member => by have bounds := readable pair member; rw [flagPosition]; constructor <;> omega)
      (by
        intro pair member
        have bounds := readable pair member
        rw [appendedHeap, Array.getElem?_push_lt bounds.1, Array.getElem?_push_lt bounds.2]
        simpa only [Array.getElem?_eq_getElem bounds.1, Array.getElem?_eq_getElem bounds.2] using sources pair member)
  have aLive : addressed.liveWords = state.liveWords := by simp only [State.liveWords, aHeap, aStack, aOutput]
  have lLive : loaded.liveWords = state.liveWords := by simp only [State.liveWords, lHeap, lStack, lOutput, aHeap, aStack, aOutput]
  have appendedLive : appended.liveWords = state.liveWords + 1 := pLive.trans (congrArg (· + 1) lLive)
  refine ⟨final, 3 + tailTicks, ?_, by omega, ?_, ?_, finalStack.trans (pStack.trans (lStack.trans aStack)),
    finalOutput.trans (pOutput.trans (lOutput.trans aOutput)), finalRunning, ?_⟩
  · have joined := aTrace.append (lTrace.append (pTrace.append tailTrace))
    simp only [aLive, lLive, appendedLive] at joined
    convert joined using 1 <;> omega
  · simpa [Nat.add_assoc] using finalPC
  · rw [finalHeap, appendedHeap, flagPosition, mark_push]
  · intro index notZero notOne
    rw [finalFrame index notZero notOne, pFrame, lFrame index notOne, aFrame index notZero]

structure Job where
  zeroAddress : Nat
  pairs : List (Nat × Nat)
  deriving DecidableEq, Repr

def work (jobs : List Job) : Nat := (jobs.map fun job => 3 + 9 * job.pairs.length).sum

def flags (width : Nat) (values : Nat → Bool) (jobs : List Job) : List (Word width) :=
  jobs.map fun job => boolWord width (values job.zeroAddress || collision values job.pairs)

def jobsCode (width : Nat) : Nat → Nat → List Job → Program width 8
  | _, _, [] => #[]
  | entry, flag, job :: rest => jobCode width entry flag job.zeroAddress job.pairs ++
      jobsCode width (entry + (3 + 9 * job.pairs.length)) (flag + 1) rest

@[simp] theorem jobsCode_size (width entry flag : Nat) (jobs : List Job) :
    (jobsCode width entry flag jobs).size = work jobs := by
  induction jobs generalizing entry flag with
  | nil => rfl
  | cons job rest ih => simp [jobsCode, ih, work]

theorem jobs_execution (resident : Program width 8) (state : State width 8)
    (entry flag : Nat) (jobs : List Job) (values : Nat → Bool)
    (flagPosition : flag = state.heap.size)
    (physical : CodeAt resident entry (jobsCode width entry flag jobs))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + work jobs < 2 ^ width) (booleanRoom : 1 < 2 ^ width)
    (heapRoom : state.heap.size + jobs.length < 2 ^ width)
    (readable : ∀ job ∈ jobs, job.zeroAddress < state.heap.size ∧
      ∀ pair ∈ job.pairs, pair.1 < state.heap.size ∧ pair.2 < state.heap.size)
    (sources : ∀ job ∈ jobs, state.heap[job.zeroAddress]? = some (boolWord width (values job.zeroAddress)) ∧
      ∀ pair ∈ job.pairs, state.heap[pair.1]? = some (boolWord width (values pair.1)) ∧
        state.heap[pair.2]? = some (boolWord width (values pair.2))) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + jobs.length) ∧
      ticks ≤ work jobs ∧ final.pc = word width (entry + work jobs) ∧
      final.heap = state.heap ++ (flags width values jobs).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → final.reg index = state.reg index) := by
  induction jobs generalizing state entry flag with
  | nil => exact ⟨state, 0, by simpa using Execution.refl (p := resident) state, by simp [work],
      by simpa [work] using position, by simp [flags], rfl, rfl, running, fun _ _ _ => rfl⟩
  | cons job rest ih =>
    have firstAt := RawSharedOrdered.takePrefix resident entry _ _ physical
    have tailAt := RawSharedOrdered.takeSuffix resident entry _ _ physical
    have bounds := readable job (by simp)
    have cells := sources job (by simp)
    have totalWork : work (job :: rest) = 3 + 9 * job.pairs.length + work rest := by simp [work]
    obtain ⟨next, firstTicks, firstTrace, firstTime, firstPC, firstHeap, firstStack, firstOutput,
        firstRunning, firstFrame⟩ :=
      job_execution resident state entry flag job.zeroAddress job.pairs values (values job.zeroAddress)
        flagPosition firstAt position running (by rw [totalWork] at room; omega) booleanRoom
        (by simp only [List.length_cons] at heapRoom; omega) bounds.1
        (by simpa only [Array.getElem?_eq_getElem bounds.1, Option.some.injEq] using cells.1) bounds.2 cells.2
    have nextSize : next.heap.size = state.heap.size + 1 := by rw [firstHeap]; simp
    obtain ⟨final, tailTicks, tailTrace, tailTime, finalPC, finalHeap, finalStack, finalOutput,
        finalRunning, finalFrame⟩ :=
      ih next (entry + (3 + 9 * job.pairs.length)) (flag + 1) (by rw [nextSize, flagPosition])
        (by simpa only [jobsCode, jobCode_size] using tailAt) firstPC firstRunning
        (by rw [totalWork] at room; omega) (by rw [nextSize]; simp only [List.length_cons] at heapRoom; omega)
        (by
          intro remaining member
          have data := readable remaining (by simp [member])
          rw [nextSize]
          refine ⟨by omega, ?_⟩
          intro pair pairMember
          have pairBounds := data.2 pair pairMember
          omega)
        (by
          intro remaining member
          have bounds := readable remaining (by simp [member])
          have cells := sources remaining (by simp [member])
          rw [firstHeap, Array.getElem?_push_lt bounds.1]
          refine ⟨by simpa only [Array.getElem?_eq_getElem bounds.1] using cells.1, ?_⟩
          intro pair pairMember
          have pairBounds := bounds.2 pair pairMember
          rw [Array.getElem?_push_lt pairBounds.1, Array.getElem?_push_lt pairBounds.2]
          simpa only [Array.getElem?_eq_getElem pairBounds.1, Array.getElem?_eq_getElem pairBounds.2] using cells.2 pair pairMember)
    have nextLive : next.liveWords = state.liveWords + 1 := by
      simp only [State.liveWords, nextSize, firstStack, firstOutput]; omega
    refine ⟨final, firstTicks + tailTicks, ?_, by rw [totalWork]; omega, ?_, ?_,
      finalStack.trans firstStack, finalOutput.trans firstOutput, finalRunning, ?_⟩
    · have joined := firstTrace.append tailTrace
      simp only [nextLive] at joined
      simp only [List.length_cons]
      convert joined using 1
      omega
    · simpa only [totalWork, Nat.add_assoc] using finalPC
    · rw [finalHeap, firstHeap]
      apply Array.toList_inj.mp
      simp [flags]
    · intro index notZero notOne
      rw [finalFrame index notZero notOne, firstFrame index notZero notOne]

end Controller.Cost.LiteralConflict
