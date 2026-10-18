module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroQuery
public import Controller.Cost.ForestInputStored
public import Controller.Cost.RegisterWiden

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Original literal coordinates are formed by fetched reads from the shared
source packet. Channel coordinates use their stored identifier directly;
activity coordinates add the actual channel-count header. Dictionary lookup
and output pair allocation consume those computed values. Source cells are
preserved across local first touches and emitted solver-source words.
-/
namespace Controller.Cost.ForestZeroEmit
open Controller.CNF Controller.Cost.GateProgram
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroTouch Controller.Cost.ForestZeroRows

/-- A source slot identifies an original channel or node occurrence. Bounds
and coordinate equations are derived from the typed packet correspondence. -/
structure Reference (ambient : ℕ) where
  slot : ℕ
  raw : ℕ
  activity : Bool
  coordinate : Fin ambient
  positive : Bool

/-- This contract identifies actual source cells, rather than a supplied
already-read register value. -/
structure StoredReference (heap : Array (Word width)) (channels sourceEnd : ℕ)
    (reference : Reference ambient) : Prop where
  sourceBound : sourceEnd ≤ heap.size
  slotBound : reference.slot < sourceEnd
  headerBound : 0 < sourceEnd
  slotWord : heap[reference.slot]? = some (word width reference.raw)
  channelWord : heap[0]? = some (word width channels)
  coordinateEq : reference.coordinate.val =
    reference.raw + (if reference.activity then channels else 0)

/-- Source addresses are instruction fields; source IDs and the channel count
are always loaded from heap cells by the executed code. -/
def readCode (width : ℕ) (reference : Reference ambient) : Code width :=
  [.constant 3 (word width reference.slot), .load 0 3] ++
    (if reference.activity then
      [.constant 3 (word width 0), .load 3 3, .add 0 0 3] else [])

@[simp] theorem readCode_length (reference : Reference ambient) :
    (readCode width reference).length = if reference.activity then 5 else 2 := by
  cases activity : reference.activity <;> simp [readCode, activity]

/-- Only the reserved dictionary cells change before the emitted pair is
appended. Every original source cell stays available for subsequent loads. -/
theorem literal_source_frame (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (literal : Literal (Fin ambient))
    (sourceEnd : ℕ) (beforeTable : sourceEnd ≤ layout.tableBase)
    (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (address : ℕ) (valid : address < sourceEnd) (sourceBound : sourceEnd ≤ heap.size) :
    (literalHeap heap layout state literal)[address]? = heap[address]? := by
  have heapValid : address < heap.size := by omega
  have touched : (touchedHeap heap layout state literal.1)[address]? = heap[address]? := by
    by_cases unseen : state.slots[literal.1.val] = 0
    · rw [show touchedHeap heap layout state literal.1 =
        freshHeap heap layout.tableBase layout.inverseBase state literal.1 by simp [touchedHeap, unseen]]
      exact fresh_outside heap layout.tableBase layout.inverseBase state literal.1 address (by omega) (by omega)
    · simp only [touchedHeap, ite_eq_right unseen]
  simp only [literalHeap, Array.getElem?_push, Array.size_push, touchedHeap_size,
    ite_eq_right (show address ≠ heap.size + 1 by omega), ite_eq_right (show address ≠ heap.size by omega)]
  exact touched

/-- Repeated source occurrences retain their original physical provenance
through every preceding emitted literal, including fresh dictionary entries. -/
theorem storedReference_retained (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (literal : Literal (Fin ambient))
    (channels sourceEnd : ℕ) (reference : Reference ambient)
    (stored : StoredReference heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase) :
    StoredReference (literalHeap heap layout state literal) channels sourceEnd reference := by
  constructor
  · rw [literalHeap_size]; have := stored.sourceBound; omega
  · exact stored.slotBound
  · exact stored.headerBound
  · exact (literal_source_frame heap layout state literal sourceEnd beforeTable beforeInverse
      reference.slot stored.slotBound stored.sourceBound).trans stored.slotWord
  · exact (literal_source_frame heap layout state literal sourceEnd beforeTable beforeInverse
      0 stored.headerBound stored.sourceBound).trans stored.channelWord
  · exact stored.coordinateEq

private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) (fits : cursor < 2 ^ width) :
    (atState heap cursor x0 x1 x2 x3 stack output).advance =
      atState heap (cursor + 1) x0 x1 x2 x3 stack output := by
  simp [atState, State.advance, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put0_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 0 (word width value) =
      atState heap cursor value x1 x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put3_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 3 (word width value) =
      atState heap cursor x0 x1 x2 value stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

/-- The common two fetched instructions load the actual source identifier.
Neither the original source cursor nor a precomputed ID is an oracle operand. -/
theorem read_prefix_execution (program : Program width 4) (heap : Array (Word width))
    (channels sourceEnd : ℕ) (reference : Reference ambient)
    (stored : StoredReference heap channels sourceEnd reference)
    (base input tableBase count scratch : ℕ) (stack output : List (Word width))
    (heapFits : heap.size ≤ 2 ^ width) (programFits : base + 2 < 2 ^ width)
    (block : BlockAt program base
      [.constant 3 (word width reference.slot), .load 0 3]) :
    Execution program (atState heap base input tableBase count scratch stack output)
      (atState heap (base + 2) reference.raw tableBase count reference.slot stack output)
      2 (5 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base input tableBase count scratch stack output
  let s1 := atState heap (base + 1) input tableBase count reference.slot stack output
  let s2 := atState heap (base + 2) reference.raw tableBase count reference.slot stack output
  have valid : reference.slot < heap.size := by have := stored.slotBound; have := stored.sourceBound; omega
  have slotValue : (word width reference.slot).val = reference.slot := Nat.mod_eq_of_lt (by omega)
  have value : heap[reference.slot]'valid = word width reference.raw := by
    have source := stored.slotWord
    rw [Array.getElem?_eq_getElem valid] at source
    exact Option.some.inj source
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 3 (word width reference.slot)) rfl (by omega)
      (by simpa using block 0 (by simp))]
    change some (s0.advance.put 3 (word width reference.slot)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.load 0 3) rfl (by omega)
      (by simpa using block 1 (by simp))]
    change (if bounded : (word width reference.slot).val < heap.size then
      some (s1.advance.put 0 (heap[(word width reference.slot).val]'bounded)) else none) = some s2
    simp only [slotValue, dite_eq_left valid, value]
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.refl s2))
  convert trace using 1 <;> simp only [s0, s1, s2, atState_liveWords] <;> omega

/-- Activity coordinates use the actual global channel-count header. -/
def activityCode (width : ℕ) : Code width :=
  [.constant 3 (word width 0), .load 3 3, .add 0 0 3]

theorem activity_execution (program : Program width 4) (heap : Array (Word width))
    (base raw channels tableBase count scratch : ℕ) (stack output : List (Word width))
    (headerValid : 0 < heap.size) (header : heap[0]? = some (word width channels))
    (coordinateFits : raw + channels < 2 ^ width) (programFits : base + 3 < 2 ^ width)
    (block : BlockAt program base (activityCode width)) :
    Execution program (atState heap base raw tableBase count scratch stack output)
      (atState heap (base + 3) (raw + channels) tableBase count channels stack output)
      3 (5 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base raw tableBase count scratch stack output
  let s1 := atState heap (base + 1) raw tableBase count 0 stack output
  let s2 := atState heap (base + 2) raw tableBase count channels stack output
  let s3 := atState heap (base + 3) (raw + channels) tableBase count channels stack output
  have rawValue : (word width raw).val = raw := Nat.mod_eq_of_lt (by omega)
  have channelsValue : (word width channels).val = channels := Nat.mod_eq_of_lt (by omega)
  have zeroValue : (word width 0).val = 0 := Nat.mod_eq_of_lt (Nat.two_pow_pos width)
  have headerWord : heap[0]'headerValid = word width channels := by
    rw [Array.getElem?_eq_getElem headerValid] at header
    exact Option.some.inj header
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [activityCode] using block 0 (by simp [activityCode]))]
    change some (s0.advance.put 3 (word width 0)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.load 3 3) rfl (by omega)
      (by simpa [activityCode] using block 1 (by simp [activityCode]))]
    change (if bounded : (word width 0).val < heap.size then
      some (s1.advance.put 3 (heap[(word width 0).val]'bounded)) else none) = some s2
    simp only [zeroValue, dite_eq_left headerValid, headerWord]
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.add 0 0 3) rfl (by omega)
      (by simpa [activityCode] using block 2 (by simp [activityCode]))]
    change some (s2.advance.put 0 (word width ((word width raw).val + (word width channels).val))) = some s3
    rw [rawValue, channelsValue, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3)))
  convert trace using 1 <;> simp only [s0, s1, s2, s3, atState_liveWords] <;> omega

/-- The complete coordinate read returns the finite original ID certified by
its actual stored occurrence and channel-count header. -/
theorem read_execution (program : Program width 4) (heap : Array (Word width))
    (channels sourceEnd : ℕ) (reference : Reference ambient)
    (stored : StoredReference heap channels sourceEnd reference)
    (base input tableBase count scratch : ℕ) (stack output : List (Word width))
    (heapFits : heap.size ≤ 2 ^ width) (ambientFits : ambient ≤ 2 ^ width)
    (programFits : base + (readCode width reference).length < 2 ^ width)
    (block : BlockAt program base (readCode width reference)) :
    Execution program (atState heap base input tableBase count scratch stack output)
      (atState heap (base + (readCode width reference).length) reference.coordinate.val
        tableBase count (if reference.activity then channels else reference.slot) stack output)
      (readCode width reference).length (5 + heap.size + stack.length + output.length) := by
  have firstBlock : BlockAt program base
      [.constant 3 (word width reference.slot), .load 0 3] :=
    BlockAt.prefix program base _ _ block
  have first := read_prefix_execution program heap channels sourceEnd reference stored
    base input tableBase count scratch stack output heapFits
    (by
      have lower : 2 ≤ (readCode width reference).length := by
        rw [readCode_length]; cases activity : reference.activity <;> simp [activity]
      omega) firstBlock
  cases activity : reference.activity
  · have coordinate : reference.coordinate.val = reference.raw := by
      simpa only [activity, Bool.false_eq_true, ite_false, Nat.add_zero] using stored.coordinateEq
    simpa only [readCode_length, activity, Bool.false_eq_true, ite_false, coordinate] using first
  · have coordinate : reference.coordinate.val = reference.raw + channels := by
      simpa only [activity, ite_eq_left trivial] using stored.coordinateEq
    have extra : BlockAt program (base + 2) (activityCode width) := by
      simpa only [readCode, activity, ite_eq_left trivial, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
        activityCode] using BlockAt.suffix program base _ _ block
    have tail := activity_execution program heap (base + 2) reference.raw channels tableBase count reference.slot
      stack output (by have := stored.headerBound; have := stored.sourceBound; omega) stored.channelWord
      (by have := reference.coordinate.isLt; omega)
      (by simpa only [readCode_length, activity, ite_eq_left trivial, Nat.add_assoc] using programFits) extra
    have joined := first.append tail
    convert joined using 1 <;>
      simp only [readCode_length, activity, ite_eq_left trivial, coordinate, Nat.add_assoc] <;> omega

/-- Each physical literal first loads an original source coordinate, then
executes the shared dictionary and actual signed-pair append code. -/
def literalCode (width base : ℕ) (reference : Reference ambient) : Code width :=
  readCode width reference ++
    Controller.Cost.ForestZeroTouch.code width (base + (readCode width reference).length) ++
    pairCode width reference.positive

@[simp] theorem literalCode_length (reference : Reference ambient) :
    (literalCode width base reference).length = (readCode width reference).length + 23 := by
  simp [literalCode]

theorem emit_literal_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (channels sourceEnd : ℕ)
    (reference : Reference ambient) (stored : StoredReference heap channels sourceEnd reference)
    (base input scratch : ℕ) (stack output : List (Word width))
    (room : heap.size + 2 < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (literalCode width base reference).length < 2 ^ width)
    (block : BlockAt program base (literalCode width base reference)) :
    ∃ ticks, ticks ≤ 23 ∧ Execution program
      (atState heap base input layout.tableBase state.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState (literalHeap heap layout state (reference.coordinate, reference.positive))
        (base + (literalCode width base reference).length)
        (touch state reference.coordinate).2.1 layout.tableBase
        (touch state reference.coordinate).1.coordinates.size
        (if reference.positive then 1 else 0) (word width layout.inverseBase :: stack) output)
      ticks (8 + heap.size + stack.length + output.length) := by
  have wholeBlock : BlockAt program base (readCode width reference ++
      (Controller.Cost.ForestZeroTouch.code width (base + (readCode width reference).length) ++
        pairCode width reference.positive)) := by
    simpa only [literalCode, List.append_assoc] using block
  have readBlock : BlockAt program base (readCode width reference) := BlockAt.prefix program base _ _ wholeBlock
  have restBlock : BlockAt program (base + (readCode width reference).length)
      (Controller.Cost.ForestZeroTouch.code width (base + (readCode width reference).length) ++
        pairCode width reference.positive) := BlockAt.suffix program base _ _ wholeBlock
  have touchBlock := BlockAt.prefix program _ _ _ restBlock
  have pairBlock := BlockAt.suffix program _ _ _ restBlock
  have first := read_execution program heap channels sourceEnd reference stored base input layout.tableBase
    state.coordinates.size scratch (word width layout.inverseBase :: stack) output
    (by omega) (by omega) (by simp only [literalCode_length] at programFits; omega) readBlock
  obtain ⟨ticks, bound, tail⟩ := literal_execution program heap layout state represented
    (reference.coordinate, reference.positive) (base + (readCode width reference).length)
    (if reference.activity then channels else reference.slot) stack output room ambientFits
    (by simp only [literalCode_length] at programFits; omega) touchBlock
    (by simpa only [Controller.Cost.ForestZeroTouch.code_length] using pairBlock)
  have joined := first.append tail
  have readBound : (readCode width reference).length ≤ 5 := by
    rw [readCode_length]; cases reference.activity <;> decide
  refine ⟨(readCode width reference).length + ticks, by omega, ?_⟩
  convert joined using 1 <;>
    simp only [literalCode_length, List.length_cons, Nat.add_assoc] <;> omega

/-- Concrete allocation state after an occurrence prefix. The layout carries
its actual heap-size bound; its shared bases never change. -/
structure Result (ambient width : ℕ) where
  heap : Array (Word width)
  layout : Layout ambient heap.size
  dictionary : Dictionary ambient
  input : ℕ
  scratch : ℕ

/-- This recurrence specifies the heap and registers of the fetched emitter.
Its source references retain occurrence positions; it does not deduplicate. -/
def emitReferences (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (input scratch : ℕ) : List (Reference ambient) → Result ambient width
  | [] => ⟨heap, layout, state, input, scratch⟩
  | reference :: rest =>
      emitReferences (literalHeap heap layout state (reference.coordinate, reference.positive))
        (literalLayout heap layout state (reference.coordinate, reference.positive))
        (touch state reference.coordinate).1 (touch state reference.coordinate).2.1
        (if reference.positive then 1 else 0) rest

/-- Generated code retains the original source slot for every occurrence. Its
field generation and final program allocation are charged by the caller. -/
def emitCode (width base : ℕ) : List (Reference ambient) → Code width
  | [] => []
  | reference :: rest => literalCode width base reference ++
      emitCode width (base + (literalCode width base reference).length) rest

theorem emitCode_length (width base : ℕ) (references : List (Reference ambient)) :
    (emitCode width base references).length ≤ 28 * references.length := by
  induction references generalizing base with
  | nil => simp [emitCode]
  | cons reference rest ih =>
      have first : (literalCode width base reference).length ≤ 28 := by
        rw [literalCode_length, readCode_length]; cases reference.activity <;> decide
      have tail := ih (base + (literalCode width base reference).length)
      simp only [emitCode, List.length_append, List.length_cons]
      omega

theorem emitReferences_size (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (input scratch : ℕ) (references : List (Reference ambient)) :
    (emitReferences heap layout state input scratch references).heap.size = heap.size + 2 * references.length := by
  induction references generalizing heap state input scratch with
  | nil => simp [emitReferences]
  | cons reference rest ih =>
      simp only [emitReferences]
      rw [ih, literalHeap_size]
      simp only [List.length_cons]
      omega

theorem emitReferences_bases (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (input scratch : ℕ) (references : List (Reference ambient)) :
    (emitReferences heap layout state input scratch references).layout.tableBase = layout.tableBase ∧
      (emitReferences heap layout state input scratch references).layout.inverseBase = layout.inverseBase := by
  induction references generalizing heap state input scratch with
  | nil => exact ⟨rfl, rfl⟩
  | cons reference rest ih =>
      exact ih _ _ _ _ _

theorem emitReferences_dictionary (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (input scratch : ℕ) (references : List (Reference ambient)) :
    (emitReferences heap layout state input scratch references).dictionary =
      (compileClause state (references.map (fun reference => (reference.coordinate, reference.positive)))).1 := by
  induction references generalizing heap state input scratch with
  | nil => rfl
  | cons reference rest ih =>
      simpa only [emitReferences, List.map_cons, compileClause] using ih
        (literalHeap heap layout state (reference.coordinate, reference.positive))
        (literalLayout heap layout state (reference.coordinate, reference.positive))
        (touch state reference.coordinate).1 (touch state reference.coordinate).2.1
        (if reference.positive then 1 else 0)

theorem emitReferences_represented (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (state : Dictionary ambient) (represented : Represented heap layout state)
    (input scratch : ℕ) (references : List (Reference ambient)) :
    let result := emitReferences heap layout state input scratch references
    Represented result.heap result.layout result.dictionary := by
  induction references generalizing heap state input scratch with
  | nil => exact represented
  | cons reference rest ih =>
      exact ih _ _ _ (literal_represented heap layout state represented
        (reference.coordinate, reference.positive)) _ _

/-- Whole occurrence execution reads actual retained source cells at each
iteration, updates the shared dictionary, and emits exactly one signed pair.
Every input occurrence contributes at most 23 fetched steps and two heap words. -/
theorem emitReferences_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (channels sourceEnd : ℕ)
    (references : List (Reference ambient))
    (stored : ∀ reference ∈ references, StoredReference heap channels sourceEnd reference)
    (beforeTable : sourceEnd ≤ layout.tableBase) (beforeInverse : sourceEnd ≤ layout.inverseBase)
    (base input scratch : ℕ) (stack output : List (Word width))
    (room : heap.size + 2 * references.length < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (emitCode width base references).length < 2 ^ width)
    (block : BlockAt program base (emitCode width base references)) :
    let result := emitReferences heap layout state input scratch references
    ∃ ticks peak, Execution program
      (atState heap base input layout.tableBase state.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState result.heap (base + (emitCode width base references).length) result.input
        layout.tableBase result.dictionary.coordinates.size result.scratch
        (word width layout.inverseBase :: stack) output)
      ticks peak ∧ ticks ≤ 23 * references.length ∧
      peak ≤ 8 + heap.size + 2 * references.length + stack.length + output.length := by
  induction references generalizing heap state base input scratch with
  | nil =>
      refine ⟨0, (atState heap base input layout.tableBase state.coordinates.size scratch
        (word width layout.inverseBase :: stack) output).liveWords, ?_, by simp, ?_⟩
      · simpa only [emitReferences, emitCode, List.length_nil, Nat.add_zero] using
          Execution.refl (p := program) (atState heap base input layout.tableBase state.coordinates.size scratch
            (word width layout.inverseBase :: stack) output)
      · simp only [atState_liveWords, List.length_cons, List.length_nil]; omega
  | cons reference rest ih =>
      have firstBlock : BlockAt program base (literalCode width base reference) := BlockAt.prefix program base _ _ block
      have tailBlock : BlockAt program (base + (literalCode width base reference).length)
          (emitCode width (base + (literalCode width base reference).length) rest) :=
        BlockAt.suffix program base _ _ block
      have firstStored := stored reference (by simp)
      obtain ⟨firstTicks, firstBound, first⟩ := emit_literal_execution program heap layout state represented
        channels sourceEnd reference firstStored base input scratch stack output
        (by simp only [List.length_cons] at room; omega) ambientFits
        (by simp only [emitCode, List.length_append] at programFits; omega) firstBlock
      have tailStored : ∀ other ∈ rest,
          StoredReference (literalHeap heap layout state (reference.coordinate, reference.positive))
            channels sourceEnd other := by
        intro other member
        exact storedReference_retained heap layout state (reference.coordinate, reference.positive)
          channels sourceEnd other (stored other (by simp [member])) beforeTable beforeInverse
      obtain ⟨tailTicks, tailPeak, tail, ticksBound, peakBound⟩ := ih
        (literalHeap heap layout state (reference.coordinate, reference.positive))
        (literalLayout heap layout state (reference.coordinate, reference.positive))
        (touch state reference.coordinate).1
        (literal_represented heap layout state represented (reference.coordinate, reference.positive))
        tailStored beforeTable beforeInverse
        (base + (literalCode width base reference).length)
        (touch state reference.coordinate).2.1 (if reference.positive then 1 else 0)
        (by simp only [literalHeap_size, List.length_cons] at room ⊢; omega)
        (by simp only [emitCode, List.length_append] at programFits; omega) tailBlock
      have joined := first.append tail
      refine ⟨firstTicks + tailTicks, max (8 + heap.size + stack.length + output.length) tailPeak, ?_, ?_, ?_⟩
      · convert joined using 1 <;> simp only [emitReferences, emitCode, List.length_append, Nat.add_assoc, literalLayout]
      · simp only [List.length_cons]; omega
      · simp only [literalHeap_size] at peakBound
        simp only [List.length_cons]
        omega

end Controller.Cost.ForestZeroEmit
