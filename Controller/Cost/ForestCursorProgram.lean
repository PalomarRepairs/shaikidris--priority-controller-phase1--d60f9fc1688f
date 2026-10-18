module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestMarkerCycle
public import Controller.Cost.ForestGuardRefinement
public import Controller.Cost.ForestCursorCalls

@[expose] public section

/-!
# Physical unweighted forest cursor

The cursor follows stored child positions, updates a separate guard-counter
region, and tests input leaves by indexed heap reads. Its first feasible leaf
retains a shared reversed-route descriptor pointer in a disjoint selector
region. Word representation, parent-pointer descriptors and emitted program
coverage are explicit invariants. Weight arithmetic is a separate contract.
-/
namespace Controller.Cost.ForestCursorProgram

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestMarkerMachine
open Controller.Cost.ForestGuardSchedule

/-- A zero cell falls through; a nonzero cell skips the entire leaf selector.
Register three is the invariant zero register. -/
def zeroTest (width base address failure : ℕ) : ForestCounter.Code width :=
  [.constant 0 (word width address), .load 1 0,
    .branchZero 1 (word width (base + 4)), .branchZero 3 (word width failure)]

@[simp] theorem zeroTest_length (width base address failure : ℕ) :
    (zeroTest width base address failure).length = 4 := rfl

/-- All fetched zero-test instructions leave the heap unchanged. -/
theorem zeroTest_execution (program : Program width 4) (heap : Array (Word width))
    (base address failure : ℕ) (oldAddress oldLoaded temporary value : Word width)
    (fits : base + 4 < 2 ^ width) (failureFits : failure < 2 ^ width)
    (addressFits : address < 2 ^ width) (valid : address < heap.size)
    (held : heap[address] = value)
    (block : BlockAt program base (zeroTest width base address failure)) :
    Execution program (counterState heap base oldAddress oldLoaded temporary)
      (counterState heap (if value.val = 0 then base + 4 else failure)
        (word width address) value temporary)
      (if value.val = 0 then 3 else 4) (5 + heap.size) := by
  have first : program[base]? = some (.constant 0 (word width address)) := by
    simpa [zeroTest] using block 0 (by simp)
  have second : program[base + 1]? = some (.load 1 0) := by
    simpa [zeroTest] using block 1 (by simp)
  have third : program[base + 2]? = some (.branchZero 1 (word width (base + 4))) := by
    simpa [zeroTest] using block 2 (by simp)
  have fourth : program[base + 3]? = some (.branchZero 3 (word width failure)) := by
    simpa [zeroTest] using block 3 (by simp)
  have a := address_transition program heap base address oldAddress oldLoaded temporary (by omega) first
  have b := read_transition program heap (base + 1) address oldLoaded temporary value
    (by omega) addressFits valid held second
  have c := branch_transition program heap (base + 2) (base + 4) 1
    (word width address) value temporary (by omega) third
  have selector : ((counterState heap (base + 2) (word width address) value temporary).reg
      (1 : Fin 4)).val = value.val := rfl
  rw [selector] at c
  by_cases zero : value.val = 0
  · rw [ite_eq_left zero] at c
    have trace := Execution.cons a (Execution.cons b (Execution.cons c (Execution.refl
      (counterState heap (base + 4) (word width address) value temporary))))
    simpa only [ite_eq_left zero, counterState_liveWords, Nat.add_assoc, Nat.zero_add, max_self] using trace
  · rw [ite_eq_right zero] at c
    have d := branch_transition program heap (base + 3) failure 3
      (word width address) value temporary (by omega) fourth
    have registerZero : ((counterState heap (base + 3) (word width address) value temporary).reg
        (3 : Fin 4)).val = 0 := by simp [counterState, word]
    rw [registerZero, ite_eq_left rfl] at d
    simp only [Nat.add_assoc] at c
    have trace := Execution.cons a (Execution.cons b (Execution.cons c (Execution.cons d
      (Execution.refl (counterState heap failure (word width address) value temporary)))))
    simpa only [ite_eq_right zero, counterState_liveWords, Nat.add_assoc, Nat.zero_add, max_self] using trace

/-- A successful first leaf records its descriptor pointer and the found bit. -/
def commitCode (width best found pointer : ℕ) : ForestCounter.Code width :=
  [.constant 2 (word width pointer), .constant 0 (word width best), .store 0 2,
    .constant 2 (word width 1), .constant 0 (word width found), .store 0 2]

@[simp] theorem commitCode_length (width best found pointer : ℕ) :
    (commitCode width best found pointer).length = 6 := rfl

def committedHeap (width : ℕ) (heap : Array (Word width)) (best found pointer : ℕ) :
    Array (Word width) := (heap.setIfInBounds best (word width pointer)).setIfInBounds found (word width 1)

/-- The pointer and found bit are written by six actual fetched instructions. -/
theorem commit_execution (program : Program width 4) (heap : Array (Word width))
    (base best found pointer : ℕ) (address loaded temporary : Word width)
    (fits : base + 6 < 2 ^ width) (bestFits : best < 2 ^ width) (foundFits : found < 2 ^ width)
    (bestValid : best < heap.size) (foundValid : found < heap.size)
    (block : BlockAt program base (commitCode width best found pointer)) :
    Execution program (counterState heap base address loaded temporary)
      (counterState (committedHeap width heap best found pointer) (base + 6)
        (word width found) loaded (word width 1)) 6 (5 + heap.size) := by
  have first : program[base]? = some (.constant 2 (word width pointer)) := by
    simpa [commitCode] using block 0 (by simp)
  have second : program[base + 1]? = some (.constant 0 (word width best)) := by
    simpa [commitCode] using block 1 (by simp)
  have third : program[base + 2]? = some (.store 0 2) := by
    simpa [commitCode] using block 2 (by simp)
  have fourth : program[base + 3]? = some (.constant 2 (word width 1)) := by
    simpa [commitCode] using block 3 (by simp)
  have fifth : program[base + 4]? = some (.constant 0 (word width found)) := by
    simpa [commitCode] using block 4 (by simp)
  have sixth : program[base + 5]? = some (.store 0 2) := by
    simpa [commitCode] using block 5 (by simp)
  have a := increment_transition program heap base pointer address loaded temporary (by omega) first
  have b := address_transition program heap (base + 1) best address loaded (word width pointer)
    (by omega) second
  have c := store_temporary_transition program heap (base + 2) best loaded (word width pointer)
    (by omega) bestFits bestValid third
  have d := increment_transition program (heap.set best (word width pointer)) (base + 3) 1
    (word width best) loaded (word width pointer) (by omega) fourth
  have e := address_transition program (heap.set best (word width pointer)) (base + 4) found
    (word width best) loaded (word width 1) (by omega) fifth
  have f := store_temporary_transition program (heap.set best (word width pointer)) (base + 5) found
    loaded (word width 1) (by omega) foundFits (by simpa using foundValid) sixth
  simp only [Nat.add_assoc] at b c d e f
  have heapEq : committedHeap width heap best found pointer =
      (heap.set best (word width pointer) bestValid).set found (word width 1) (by simpa using foundValid) := by
    simp [committedHeap, Array.setIfInBounds_def, bestValid, foundValid]
  have trace := Execution.cons a (Execution.cons b (Execution.cons c (Execution.cons d
    (Execution.cons e (Execution.cons f (Execution.refl
      (counterState ((heap.set best (word width pointer) bestValid).set found (word width 1)
        (by simpa using foundValid)) (base + 6)
        (word width found) loaded (word width 1))))))))
  simpa only [heapEq, counterState_liveWords, Array.size_set, Nat.zero_add, max_self] using trace

/-- Exact coverage of each emitted physical counter/metadata test. -/
def TestsAt (program : Program width 4) (base failure : ℕ) : List ℕ → Prop
  | [] => True
  | address :: rest => BlockAt program base (zeroTest width base address failure) ∧
      TestsAt program (base + 4) failure rest

def allZero (heap : Array (Word width)) (addresses : List ℕ) : Bool :=
  addresses.all (fun address => decide ((storedWord heap address).val = 0))

/-- The test sequence stops at the first nonzero stored word; its heap and
reserved zero register are unchanged. -/
theorem tests_execution (program : Program width 4) (heap : Array (Word width))
    (base failure : ℕ) (addresses : List ℕ) (oldAddress oldLoaded temporary : Word width)
    (fits : base + 4 * addresses.length < 2 ^ width) (failureFits : failure < 2 ^ width)
    (valid : ∀ address ∈ addresses, address < heap.size ∧ address < 2 ^ width)
    (blocks : TestsAt program base failure addresses) :
    ∃ finalAddress finalLoaded : Word width, ∃ ticks : ℕ,
      Execution program (counterState heap base oldAddress oldLoaded temporary)
        (counterState heap (if allZero heap addresses then base + 4 * addresses.length else failure)
          finalAddress finalLoaded temporary) ticks (5 + heap.size) ∧
      ticks ≤ 4 * addresses.length := by
  induction addresses generalizing base oldAddress oldLoaded with
  | nil =>
      refine ⟨oldAddress, oldLoaded, 0, ?_, by simp⟩
      simpa only [allZero, List.all_nil, ite_true, List.length_nil, Nat.mul_zero, Nat.add_zero,
        counterState_liveWords] using Execution.refl
          (counterState heap base oldAddress oldLoaded temporary)
  | cons address rest ih =>
      have addressValid := (valid address (by simp)).1
      have addressFits := (valid address (by simp)).2
      let value := heap[address]'addressValid
      have held : heap[address] = value := rfl
      have lookup : storedWord heap address = value := storedWord_eq heap address addressValid
      have first := zeroTest_execution program heap base address failure oldAddress oldLoaded temporary value
        (by simp only [List.length_cons] at fits; omega) failureFits addressFits addressValid held blocks.1
      by_cases zero : value.val = 0
      · rw [ite_eq_left zero] at first
        obtain ⟨finalAddress, finalLoaded, tailTicks, tail, tailBound⟩ :=
          ih (base + 4) (word width address) value (by
            simp only [List.length_cons] at fits; omega) (by
              intro current member; exact valid current (by simp [member])) blocks.2
        have joined := first.append tail
        refine ⟨finalAddress, finalLoaded, 3 + tailTicks, ?_, ?_⟩
        · simpa only [allZero, List.all_cons, lookup, zero, decide_true, Bool.true_and,
            List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            ite_true, max_self] using joined
        · simp only [List.length_cons]; omega
      · rw [ite_eq_right zero] at first
        refine ⟨word width address, value, 4, ?_, by simp only [List.length_cons]; omega⟩
        simpa only [allZero, List.all_cons, lookup, zero, decide_false, Bool.false_and, Bool.false_eq_true, ite_false] using first

/-- Every failed counter/metadata test bypasses the commit block. A successful
sequence stores the first route pointer. These are actual program branches. -/
theorem selector_execution (program : Program width 4) (heap : Array (Word width))
    (base best found pointer : ℕ) (addresses : List ℕ)
    (oldAddress oldLoaded temporary : Word width)
    (fits : base + 4 * addresses.length + 6 < 2 ^ width)
    (valid : ∀ address ∈ addresses, address < heap.size ∧ address < 2 ^ width)
    (bestFits : best < 2 ^ width) (foundFits : found < 2 ^ width)
    (bestValid : best < heap.size) (foundValid : found < heap.size)
    (tests : TestsAt program base (base + 4 * addresses.length + 6) addresses)
    (commit : BlockAt program (base + 4 * addresses.length) (commitCode width best found pointer)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks : ℕ,
      Execution program (counterState heap base oldAddress oldLoaded temporary)
        (counterState (if allZero heap addresses then committedHeap width heap best found pointer else heap)
          (base + 4 * addresses.length + 6) finalAddress finalLoaded finalTemporary)
        ticks (5 + heap.size) ∧ ticks ≤ 4 * addresses.length + 6 := by
  obtain ⟨testAddress, testLoaded, testTicks, trace, testBound⟩ :=
    tests_execution program heap base (base + 4 * addresses.length + 6) addresses
      oldAddress oldLoaded temporary (by omega) fits valid tests
  cases outcome : allZero heap addresses with
  | false =>
      simp only [outcome, Bool.false_eq_true, ite_false] at trace
      refine ⟨testAddress, testLoaded, temporary, testTicks, ?_, by omega⟩
      simpa only [outcome, Bool.false_eq_true, ite_false] using trace
  | true =>
      simp only [outcome, ite_eq_left rfl] at trace
      have later := commit_execution program heap (base + 4 * addresses.length) best found pointer
        testAddress testLoaded temporary fits bestFits foundFits bestValid foundValid commit
      have joined := trace.append later
      refine ⟨word width found, testLoaded, word width 1, testTicks + 6, ?_, by omega⟩
      simpa only [outcome, ite_eq_left rfl, ite_true, max_self] using joined

/-- The production unweighted selector is the zero-weight specialization of
keepBestRoute, preserving the first feasible route. -/
theorem keepBest_zero (b : ℕ) (target head : Channel n) (route : LeafRoute)
    (counters : GuardCounters n) (best : Option LeafRoute) :
    keepBestRoute b target 0 route head (counters, 0) (best.map fun path => (path, 0)) =
      (if counters head = 0 ∧ (b ≠ 1 ∨ counters target = 0) then
        match best with | none => some route | some previous => some previous
      else best).map (fun path => (path, 0)) := by
  unfold keepBestRoute
  by_cases feasible : counters head = 0 ∧ (b ≠ 1 ∨ counters target = 0)
  · simp only [feasible, ite_true, Nat.sub_zero]
    cases best <;> simp
  · simp only [feasible, ite_false]

/-- Positional descent retains the current reversed route on the actual stack. -/
def downCode (width position : ℕ) : ForestCounter.Code width :=
  [.constant 0 (word width position), .push 0]

def upCode : ForestCounter.Code width := [.pop 0]

@[simp] theorem downCode_length (width position : ℕ) : (downCode width position).length = 2 := rfl
@[simp] theorem upCode_length : (upCode (width := width)).length = 1 := rfl

theorem down_execution (program : Program width 4) (heap : Array (Word width))
    (base position : ℕ) (address loaded temporary : Word width)
    (fits : base + 2 < 2 ^ width) (block : BlockAt program base (downCode width position)) :
    Execution program (counterState heap base address loaded temporary)
      ((counterState heap (base + 2) (word width position) loaded temporary).frame [word width position] [])
      2 (6 + heap.size) := by
  have first : program[base]? = some (.constant 0 (word width position)) := by
    simpa [downCode] using block 0 (by simp)
  have second : program[base + 1]? = some (.push 0) := by
    simpa [downCode] using block 1 (by simp)
  have a := address_transition program heap base position address loaded temporary (by omega) first
  have b := push_transition program heap (base + 1) (word width position) loaded temporary (by omega) second
  have trace := Execution.cons a (Execution.cons b (Execution.refl
    ((counterState heap (base + 2) (word width position) loaded temporary).frame [word width position] [])))
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero] <;> omega

theorem up_execution (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address loaded temporary position : Word width)
    (fits : base + 1 < 2 ^ width) (block : BlockAt program base (upCode (width := width))) :
    Execution program ((counterState heap base address loaded temporary).frame [position] [])
      (counterState heap (base + 1) position loaded temporary) 1 (6 + heap.size) := by
  have fetched : program[base]? = some (.pop 0) := by
    simpa [upCode] using block 0 (by simp)
  have transition := pop_transition program heap base address loaded temporary position (by omega) fetched
  have trace := Execution.cons transition (Execution.refl
    (counterState heap (base + 1) position loaded temporary))
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero] <;> omega

/-- Selector metadata is separate from the path-counter region. -/
structure SelectorLayout (n : ℕ) where
  counterOffset : ℕ
  found : ℕ
  best : ℕ
  distinct : best ≠ found
  foundOutside : ForestGuardRestore.Outside counterOffset n found
  bestOutside : ForestGuardRestore.Outside counterOffset n best

/-- Pointer zero denotes the empty route, so selection is marked by a separate
found cell rather than by testing the stored route pointer. -/
structure SelectorStored (heap : Array (Word width)) (layout : SelectorLayout n)
    (selected : Option ℕ) : Prop where
  foundValid : layout.found < heap.size
  bestValid : layout.best < heap.size
  foundWord : heap[layout.found]'foundValid = word width (if selected.isSome then 1 else 0)
  bestWord : ∀ pointer, selected = some pointer → heap[layout.best]'bestValid = word width pointer

def leafTests (layout : SelectorLayout n) (b : ℕ) (target head : Channel n) : List ℕ :=
  [layout.counterOffset + head.val] ++
    (if b = 1 then [layout.counterOffset + target.val] else []) ++ [layout.found]

/-- Exact physical leaf feasibility, including the first-route test. -/
theorem leafTests_correct (heap : Array (Word width)) (layout : SelectorLayout n)
    (counters : GuardCounters n) (selected : Option ℕ) (b : ℕ) (target head : Channel n)
    (stored : CountersStored heap layout.counterOffset counters)
    (metadata : SelectorStored heap layout selected)
    (bounded : ∀ channel, counters channel < 2 ^ width) (oneFits : 1 < 2 ^ width) :
    allZero heap (leafTests layout b target head) =
      decide (counters head = 0 ∧ (b ≠ 1 ∨ counters target = 0) ∧ selected = none) := by
  have headRead : (storedWord heap (layout.counterOffset + head.val)).val = counters head := by
    rw [storedWord_eq heap _ (stored.valid head), stored.held head]
    exact Nat.mod_eq_of_lt (bounded head)
  have targetRead : (storedWord heap (layout.counterOffset + target.val)).val = counters target := by
    rw [storedWord_eq heap _ (stored.valid target), stored.held target]
    exact Nat.mod_eq_of_lt (bounded target)
  have foundRead : (storedWord heap layout.found).val = if selected.isSome then 1 else 0 := by
    rw [storedWord_eq heap _ metadata.foundValid, metadata.foundWord]
    cases selected <;> simp [word, Nat.mod_eq_of_lt oneFits]
  by_cases bus : b = 1
  · have shape : leafTests layout b target head =
        [layout.counterOffset + head.val, layout.counterOffset + target.val, layout.found] := by
      simp [leafTests, bus]
    rw [shape]
    change (decide ((storedWord heap (layout.counterOffset + head.val)).val = 0) &&
      (decide ((storedWord heap (layout.counterOffset + target.val)).val = 0) &&
        (decide ((storedWord heap layout.found).val = 0) && true))) = _
    rw [headRead, targetRead, foundRead]
    cases selected <;> simp [bus]
  · have shape : leafTests layout b target head =
        [layout.counterOffset + head.val, layout.found] := by simp [leafTests, bus]
    rw [shape]
    change (decide ((storedWord heap (layout.counterOffset + head.val)).val = 0) &&
      (decide ((storedWord heap layout.found).val = 0) && true)) = _
    rw [headRead, foundRead]
    cases selected <;> simp [bus]

@[simp] theorem leafTests_length (layout : SelectorLayout n) (b : ℕ) (target head : Channel n) :
    (leafTests layout b target head).length = if b = 1 then 3 else 2 := by
  by_cases bus : b = 1 <;> simp [leafTests, bus]

/-- A selector store cannot change any path counter. -/
theorem committed_counters (heap : Array (Word width)) (layout : SelectorLayout n)
    (counters : GuardCounters n) (pointer : ℕ)
    (stored : CountersStored heap layout.counterOffset counters)
    (foundValid : layout.found < heap.size) (bestValid : layout.best < heap.size) :
    CountersStored (committedHeap width heap layout.best layout.found pointer)
      layout.counterOffset counters := by
  have heapEq : committedHeap width heap layout.best layout.found pointer =
      (heap.set layout.best (word width pointer) bestValid).set layout.found (word width 1)
        (by simpa using foundValid) := by
    simp [committedHeap, Array.setIfInBounds_def, bestValid, foundValid]
  rw [heapEq]
  refine ⟨fun channel => by simpa using stored.valid channel, ?_⟩
  intro channel
  have foundDifferent : layout.found ≠ layout.counterOffset + channel.val := by
    have limit := channel.isLt
    have outside := layout.foundOutside
    unfold ForestGuardRestore.Outside at outside
    omega
  have bestDifferent : layout.best ≠ layout.counterOffset + channel.val := by
    have limit := channel.isLt
    have outside := layout.bestOutside
    unfold ForestGuardRestore.Outside at outside
    omega
  rw [Array.getElem_set_ne (by simpa using foundValid) (by simpa using stored.valid channel) foundDifferent,
    Array.getElem_set_ne bestValid (stored.valid channel) bestDifferent]
  exact stored.held channel

theorem committed_metadata (heap : Array (Word width)) (layout : SelectorLayout n)
    (selected : Option ℕ) (pointer : ℕ) (metadata : SelectorStored heap layout selected) :
    SelectorStored (committedHeap width heap layout.best layout.found pointer) layout (some pointer) := by
  have heapEq : committedHeap width heap layout.best layout.found pointer =
      (heap.set layout.best (word width pointer) metadata.bestValid).set layout.found (word width 1)
        (by simpa using metadata.foundValid) := by
    simp [committedHeap, Array.setIfInBounds_def, metadata.bestValid, metadata.foundValid]
  rw [heapEq]
  refine ⟨by simpa using metadata.foundValid, by simpa using metadata.bestValid, ?_, ?_⟩
  · rw [Array.getElem_set_self (by simpa using metadata.foundValid)]
    rfl
  · intro current equal
    have same : current = pointer := Option.some.inj equal.symm
    subst current
    rw [Array.getElem_set_ne (by simpa using metadata.foundValid) (by simpa using metadata.bestValid)
      (Ne.symm layout.distinct), Array.getElem_set_self metadata.bestValid]

/-- Descriptor cells retain a shared parent pointer and one child position.
Their representation is supplied here; constructing them is an operational
obligation before the complete forest resource theorem can use this contract. -/
structure RouteDescriptors (width : ℕ) (heap : Array (Word width)) where
  base : ℕ
  count : ℕ
  route : ℕ → LeafRoute
  sentinel : route 0 = []
  parentValid : ∀ pointer, 0 < pointer ∧ pointer ≤ count → base + 2 * (pointer - 1) < heap.size
  positionValid : ∀ pointer, 0 < pointer ∧ pointer ≤ count → base + 2 * (pointer - 1) + 1 < heap.size
  parentEarlier : ∀ pointer, ∀ valid : 0 < pointer ∧ pointer ≤ count,
    (heap[base + 2 * (pointer - 1)]'(parentValid pointer valid)).val < pointer
  cellRoute : ∀ pointer, ∀ valid : 0 < pointer ∧ pointer ≤ count,
    route pointer = (heap[base + 2 * (pointer - 1) + 1]'(positionValid pointer valid)).val ::
      route (heap[base + 2 * (pointer - 1)]'(parentValid pointer valid)).val

def leafChoice (b : ℕ) (target head : Channel n) (counters : GuardCounters n)
    (selected : Option ℕ) (pointer : ℕ) : Option ℕ :=
  if counters head = 0 ∧ (b ≠ 1 ∨ counters target = 0) ∧ selected = none then some pointer else selected

def leafHeap (width : ℕ) (heap : Array (Word width)) (layout : SelectorLayout n)
    (b : ℕ) (target head : Channel n) (counters : GuardCounters n)
    (selected : Option ℕ) (pointer : ℕ) : Array (Word width) :=
  if counters head = 0 ∧ (b ≠ 1 ∨ counters target = 0) ∧ selected = none then
    committedHeap width heap layout.best layout.found pointer else heap

/-- A complete physical leaf callback refines production keepBestRoute at zero
weights, retains the caller's route/navigation frame, and preserves counters. -/
theorem leaf_execution (program : Program width 4) (heap : Array (Word width))
    (layout : SelectorLayout n) (descriptors : RouteDescriptors width heap)
    (base b pointer : ℕ) (target head : Channel n) (route : LeafRoute)
    (counters : GuardCounters n) (selected : Option ℕ)
    (address loaded temporary : Word width) (stack output : List (Word width))
    (stored : CountersStored heap layout.counterOffset counters)
    (metadata : SelectorStored heap layout selected)
    (bounded : ∀ channel, counters channel < 2 ^ width)
    (oneFits : 1 < 2 ^ width) (counterFits : ∀ channel : Channel n, layout.counterOffset + channel.val < 2 ^ width)
    (bestFits : layout.best < 2 ^ width) (foundFits : layout.found < 2 ^ width)
    (pointerRoute : descriptors.route pointer = route)
    (fits : base + 4 * (leafTests layout b target head).length + 6 < 2 ^ width)
    (tests : TestsAt program base (base + 4 * (leafTests layout b target head).length + 6)
      (leafTests layout b target head))
    (commit : BlockAt program (base + 4 * (leafTests layout b target head).length)
      (commitCode width layout.best layout.found pointer)) :
    ∃ finalAddress finalLoaded finalTemporary : Word width, ∃ ticks : ℕ,
      Execution program ((counterState heap base address loaded temporary).frame stack output)
        ((counterState (leafHeap width heap layout b target head counters selected pointer)
          (base + 4 * (leafTests layout b target head).length + 6)
          finalAddress finalLoaded finalTemporary).frame stack output)
        ticks (5 + heap.size + (stack.length + output.length)) ∧
      ticks ≤ 18 ∧
      CountersStored (leafHeap width heap layout b target head counters selected pointer)
        layout.counterOffset counters ∧
      SelectorStored (leafHeap width heap layout b target head counters selected pointer) layout
        (leafChoice b target head counters selected pointer) ∧
      keepBestRoute b target 0 route head (counters, 0)
        ((selected.map descriptors.route).map fun route => (route, 0)) =
        ((leafChoice b target head counters selected pointer).map descriptors.route).map
          (fun route => (route, 0)) := by
  have valid : ∀ candidate ∈ leafTests layout b target head,
      candidate < heap.size ∧ candidate < 2 ^ width := by
    intro candidate present
    by_cases bus : b = 1
    · simp only [leafTests, ite_eq_left bus, List.mem_append, List.mem_cons, List.mem_nil_iff,
        or_false, or_assoc] at present
      rcases present with equal | equal | equal
      · subst candidate; exact ⟨stored.valid head, counterFits head⟩
      · subst candidate; exact ⟨stored.valid target, counterFits target⟩
      · subst candidate; exact ⟨metadata.foundValid, foundFits⟩
    · simp only [leafTests, ite_eq_right bus, List.mem_append, List.mem_cons, List.mem_nil_iff,
        or_false, false_or] at present
      rcases present with equal | equal
      · subst candidate; exact ⟨stored.valid head, counterFits head⟩
      · subst candidate; exact ⟨metadata.foundValid, foundFits⟩
  obtain ⟨fa, fl, ft, ticks, trace, tickBound⟩ := selector_execution program heap base layout.best
    layout.found pointer (leafTests layout b target head) address loaded temporary fits valid
    bestFits foundFits metadata.bestValid metadata.foundValid tests commit
  have correctness := leafTests_correct heap layout counters selected b target head stored metadata bounded oneFits
  have framed := trace.frame stack output
  have tickSmall : ticks ≤ 18 := by
    rw [leafTests_length] at tickBound
    split at tickBound <;> omega
  have traceHeap : (if allZero heap (leafTests layout b target head) then
      committedHeap width heap layout.best layout.found pointer else heap) =
      leafHeap width heap layout b target head counters selected pointer := by
    rw [correctness]
    by_cases condition : counters head = 0 ∧ (b ≠ 1 ∨ counters target = 0) ∧ selected = none <;>
      simp [leafHeap, condition]
  rw [traceHeap] at framed
  refine ⟨fa, fl, ft, ticks, framed, tickSmall, ?_, ?_, ?_⟩
  · unfold leafHeap
    split
    · exact committed_counters heap layout counters pointer stored metadata.foundValid metadata.bestValid
    · exact stored
  · unfold leafHeap leafChoice
    split
    · exact committed_metadata heap layout selected pointer metadata
    · exact metadata
  · rw [keepBest_zero]
    by_cases feasible : counters head = 0 ∧ (b ≠ 1 ∨ counters target = 0)
    · cases selected <;> simp [leafChoice, feasible, pointerRoute]
    · have impossible : ¬(counters head = 0 ∧ (b ≠ 1 ∨ counters target = 0) ∧ selected = none) := by
        tauto
      simp only [leafChoice, ite_eq_right feasible, ite_eq_right impossible]

end Controller.Cost.ForestCursorProgram
