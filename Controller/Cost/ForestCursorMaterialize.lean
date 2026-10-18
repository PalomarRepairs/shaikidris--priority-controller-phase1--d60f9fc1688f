module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCursorCompiler
public import Controller.Cost.InstructionRecordStore

@[expose] public section

/-!
# Physical allocation of captured parent descriptors

Descriptors are emitted in chronological allocation order. Each record stores
its parent ID and child position with two constant/allocate pairs. The fetched
execution extends an actual finite heap and retains its old prefix. Dense IDs
are derived from the source builder, not supplied by a route dictionary.
Sentinel zero has no allocated record.
-/
namespace Controller.Cost.ForestCursorMaterialize

open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestCursorProgram
open Controller.Cost.ForestCursorTraversal Controller.Cost.ForestCursorDescriptors

/-- Chronological records have exactly IDs 1 through the maintained count. -/
def Dense (state : Builder) : Prop :=
  state.entries.reverse.map ParentEntry.identifier = List.range' 1 state.count

theorem initial_dense : Dense initial := by simp [Dense, initial]

theorem beginRoot_dense (state : Builder) (dense : Dense state) : Dense (beginRoot state) := dense

theorem step_dense (root : ℕ) (state : Builder) (dense : Dense state)
    (operation : CursorOp n) : Dense (ForestCursorDescriptors.step root state operation) := by
  cases operation with
  | down owner position child =>
      simpa [Dense, ForestCursorDescriptors.step, List.reverse_cons, List.map_append,
        List.range'_1_concat, Nat.add_comm] using congrArg (fun ids => ids ++ [state.count + 1]) dense
  | node owner => exact dense
  | up => exact dense
  | enter owner position channel => exact dense
  | leave owner position channel => exact dense
  | leaf owner route head => exact dense

theorem scan_dense (root : ℕ) (state : Builder) (dense : Dense state)
    (operations : List (CursorOp n)) : Dense (scan root state operations) := by
  induction operations generalizing state with
  | nil => exact dense
  | cons operation rest ih => exact ih _ (step_dense root state dense operation)

theorem scanRoot_dense (graph : DAG n) (state : Builder) (dense : Dense state)
    (position : Fin graph.roots.length) : Dense (scanRoot graph state position) :=
  scan_dense _ _ (beginRoot_dense state dense) _

def fields : List ParentEntry → List ℕ
  | [] => []
  | entry :: rest => entry.parent :: entry.position :: fields rest

@[simp] theorem fields_length (entries : List ParentEntry) :
    (fields entries).length = 2 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [fields, ih]; omega

theorem fields_parent (entries : List ParentEntry) (index : ℕ) (bound : index < entries.length) :
    (fields entries)[2 * index]'(by rw [fields_length]; omega) = (entries[index]'bound).parent := by
  induction entries generalizing index with
  | nil => simp at bound
  | cons entry rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have next : index < rest.length := by simpa using bound
          simpa only [fields, Nat.mul_succ, List.getElem_cons_succ] using ih index next

theorem fields_position (entries : List ParentEntry) (index : ℕ) (bound : index < entries.length) :
    (fields entries)[2 * index + 1]'(by rw [fields_length]; omega) = (entries[index]'bound).position := by
  induction entries generalizing index with
  | nil => simp at bound
  | cons entry rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          have next : index < rest.length := by simpa using bound
          simpa only [fields, Nat.mul_succ, List.getElem_cons_succ] using ih index next

def cellCode (width value : ℕ) : ForestCounter.Code width :=
  [.constant 2 (word width value), .allocate 2]

@[simp] theorem cellCode_length (width value : ℕ) : (cellCode width value).length = 2 := rfl

/-- One allocation stores the temporary register into a new finite heap cell. -/
theorem allocate_transition (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address loaded temporary : Word width) (fits : base < 2 ^ width)
    (room : heap.size < 2 ^ width) (fetched : program[base]? = some (.allocate 2)) :
    programStep program (counterState heap base address loaded temporary) =
      some (counterState (heap.push temporary) (base + 1) address loaded temporary) := by
  unfold programStep
  rw [show (counterState heap base address loaded temporary).pc.val = base from
    Nat.mod_eq_of_lt fits, fetched]
  simp [step, counterState, State.advance, room]
  rw [show (word width base).val = base from Nat.mod_eq_of_lt fits]

/-- A value is computed by a fetched constant and stored by a fetched allocate.
No backing-array allocation is assumed. -/
theorem cell_execution (program : Program width 4) (heap : Array (Word width))
    (base value : ℕ) (address loaded temporary : Word width)
    (fits : base + 2 < 2 ^ width) (room : heap.size < 2 ^ width)
    (block : BlockAt program base (cellCode width value)) :
    Execution program (counterState heap base address loaded temporary)
      (counterState (heap.push (word width value)) (base + 2) address loaded (word width value))
      2 (6 + heap.size) := by
  have first := increment_transition program heap base value address loaded temporary (by omega)
    (by simpa [cellCode] using block 0 (by simp))
  have second := allocate_transition program heap (base + 1) address loaded (word width value)
    (by omega) room (by simpa [cellCode] using block 1 (by simp))
  have trace := Execution.cons first (Execution.cons second (Execution.refl
    (counterState (heap.push (word width value)) (base + 2) address loaded (word width value))))
  convert trace using 1 <;> simp only [Nat.add_assoc, counterState_liveWords, Array.size_push, Nat.zero_add] <;> omega

def writeCode (width : ℕ) : List ℕ → ForestCounter.Code width
  | [] => []
  | value :: rest => cellCode width value ++ writeCode width rest

@[simp] theorem writeCode_length (width : ℕ) (values : List ℕ) :
    (writeCode width values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [writeCode, ih]; omega

def allocatedHeap (width : ℕ) (heap : Array (Word width)) (values : List ℕ) : Array (Word width) :=
  heap ++ (values.map (word width)).toArray

@[simp] theorem allocatedHeap_size (width : ℕ) (heap : Array (Word width)) (values : List ℕ) :
    (allocatedHeap width heap values).size = heap.size + values.length := by simp [allocatedHeap]

theorem write_execution (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (values : List ℕ) (address loaded temporary : Word width)
    (fits : base + 2 * values.length < 2 ^ width)
    (room : heap.size + values.length ≤ 2 ^ width)
    (block : BlockAt program base (writeCode width values)) :
    ∃ finalTemporary : Word width,
      Execution program (counterState heap base address loaded temporary)
        (counterState (allocatedHeap width heap values) (base + 2 * values.length)
          address loaded finalTemporary)
        (2 * values.length) (5 + heap.size + values.length) := by
  induction values generalizing heap base temporary with
  | nil => refine ⟨temporary, ?_⟩; simpa [allocatedHeap] using Execution.refl (p := program) (counterState heap base address loaded temporary)
  | cons value rest ih =>
      have head : BlockAt program base (cellCode width value) :=
        BlockAt.prefix program base _ _ block
      have tail : BlockAt program (base + 2) (writeCode width rest) := by
        simpa using BlockAt.suffix program base _ _ block
      have first := cell_execution program heap base value address loaded temporary (by simp at fits; omega)
        (by simp at room; omega) head
      obtain ⟨last, second⟩ := ih (heap.push (word width value)) (base + 2) (word width value)
        (by simp only [List.length_cons] at fits; omega)
        (by simp only [Array.size_push, List.length_cons] at *; omega) tail
      have trace := first.append second
      have heaps : allocatedHeap width (heap.push (word width value)) rest =
          allocatedHeap width heap (value :: rest) := by
        apply Array.toList_inj.mp
        simp [allocatedHeap, List.append_assoc]
      refine ⟨last, ?_⟩
      have cursorEq : base + 2 + 2 * rest.length = base + 2 * (value :: rest).length := by
        simp only [List.length_cons]; omega
      have tickEq : 2 + 2 * rest.length = 2 * (value :: rest).length := by
        simp only [List.length_cons]; omega
      have peakEq : max (6 + heap.size) (5 + (heap.push (word width value)).size + rest.length) =
          5 + heap.size + (value :: rest).length := by
        simp only [Array.size_push, List.length_cons]; omega
      rw [heaps, cursorEq, tickEq, peakEq] at trace
      exact trace

/-- Every pre-existing finite cell survives physical descriptor allocation. -/
theorem allocatedHeap_prefix (width : ℕ) (heap : Array (Word width)) (values : List ℕ)
    (address : ℕ) (valid : address < heap.size) :
    (allocatedHeap width heap values)[address]? = heap[address]? := by
  simp [allocatedHeap, Array.getElem?_append_left valid]

def descriptorHeap (width : ℕ) (heap : Array (Word width)) (state : Builder) : Array (Word width) :=
  allocatedHeap width heap (fields state.entries.reverse)

def descriptorCode (width : ℕ) (state : Builder) : ForestCounter.Code width :=
  writeCode width (fields state.entries.reverse)

@[simp] theorem descriptorHeap_size (width : ℕ) (heap : Array (Word width)) (state : Builder)
    (valid : Valid state) : (descriptorHeap width heap state).size = heap.size + 2 * state.count := by
  simp [descriptorHeap, valid.count]

/-- Four actual ticks and two actual allocated words per captured parent record.
Sentinel zero is represented without a record. -/
theorem descriptor_execution (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (state : Builder) (valid : Valid state) (address loaded temporary : Word width)
    (fits : base + 4 * state.count < 2 ^ width)
    (room : heap.size + 2 * state.count ≤ 2 ^ width)
    (block : BlockAt program base (descriptorCode width state)) :
    ∃ finalTemporary : Word width,
      Execution program (counterState heap base address loaded temporary)
        (counterState (descriptorHeap width heap state) (base + 4 * state.count)
          address loaded finalTemporary) (4 * state.count) (5 + heap.size + 2 * state.count) := by
  have length : (fields state.entries.reverse).length = 2 * state.count := by
    simp only [fields_length, List.length_reverse, valid.count]
  have twice : 2 * (2 * state.count) = 4 * state.count := by omega
  have trace := write_execution program heap base (fields state.entries.reverse)
    address loaded temporary (by rw [length, twice]; exact fits) (by rw [length]; exact room) block
  simpa only [descriptorHeap, length, twice] using trace

/-- Actual allocation retains the caller's stack/output suffix and charges
both suffix lengths in the peak. Registers keep their explicitly stated roles. -/
theorem descriptor_execution_frame (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (state : Builder) (valid : Valid state) (address loaded temporary : Word width)
    (stack output : List (Word width)) (fits : base + 4 * state.count < 2 ^ width)
    (room : heap.size + 2 * state.count ≤ 2 ^ width)
    (block : BlockAt program base (descriptorCode width state)) :
    ∃ finalTemporary : Word width,
      Execution program ((counterState heap base address loaded temporary).frame stack output)
        ((counterState (descriptorHeap width heap state) (base + 4 * state.count)
          address loaded finalTemporary).frame stack output)
        (4 * state.count) (5 + heap.size + 2 * state.count + stack.length + output.length) := by
  obtain ⟨last, trace⟩ := descriptor_execution program heap base state valid address loaded temporary fits room block
  exact ⟨last, by simpa only [Nat.add_assoc] using trace.frame stack output⟩

/-- Direct chronological lookup for a positive represented identifier. -/
def entryAt (state : Builder) (valid : Valid state) (pointer : ℕ)
    (bounded : 0 < pointer ∧ pointer ≤ state.count) : ParentEntry :=
  state.entries.reverse[pointer - 1]'(by simpa only [List.length_reverse, valid.count] using
    (show pointer - 1 < state.count by omega))

theorem entryAt_mem (state : Builder) (valid : Valid state) (pointer : ℕ)
    (bounded : 0 < pointer ∧ pointer ≤ state.count) : entryAt state valid pointer bounded ∈ state.entries := by
  rw [← List.mem_reverse]
  exact List.getElem_mem _

theorem entryAt_id (state : Builder) (valid : Valid state) (dense : Dense state)
    (pointer : ℕ) (bounded : 0 < pointer ∧ pointer ≤ state.count) :
    (entryAt state valid pointer bounded).identifier = pointer := by
  have mappedBound : pointer - 1 < (state.entries.reverse.map ParentEntry.identifier).length := by
    simp only [List.length_map, List.length_reverse, valid.count]
    omega
  calc
    _ = (state.entries.reverse.map ParentEntry.identifier)[pointer - 1]'mappedBound := by
      simp only [List.getElem_map, entryAt]
    _ = (List.range' 1 state.count)[pointer - 1]'(by simp; omega) := List.getElem_of_eq dense mappedBound
    _ = pointer := by simp only [List.getElem_range', Nat.one_mul]; omega

/-- Every newly allocated field has its exact value at a direct physical cell. -/
theorem allocatedHeap_cell (width : ℕ) (heap : Array (Word width)) (values : List ℕ)
    (index : ℕ) (bound : index < values.length) :
    (allocatedHeap width heap values)[heap.size + index]'(by simp; omega) = word width (values[index]'bound) := by
  have cell := Array.getElem_append_right (xs := heap)
    (ys := (values.map (word width)).toArray) (i := heap.size + index)
    (h := by simp; omega) (by omega)
  simpa only [allocatedHeap, Nat.add_sub_cancel_left, List.getElem_toArray, List.getElem_map] using cell

theorem descriptor_parent_word (width : ℕ) (heap : Array (Word width))
    (state : Builder) (valid : Valid state) (pointer : ℕ)
    (bounded : 0 < pointer ∧ pointer ≤ state.count) :
    (descriptorHeap width heap state)[heap.size + 2 * (pointer - 1)]'
      (by rw [descriptorHeap_size width heap state valid]; omega) =
      word width (entryAt state valid pointer bounded).parent := by
  have bound : pointer - 1 < state.entries.reverse.length := by
    simp only [List.length_reverse, valid.count]; omega
  have field := fields_parent state.entries.reverse (pointer - 1) bound
  simpa only [descriptorHeap, field, entryAt] using allocatedHeap_cell width heap
    (fields state.entries.reverse) (2 * (pointer - 1)) (by rw [fields_length]; omega)

theorem descriptor_position_word (width : ℕ) (heap : Array (Word width))
    (state : Builder) (valid : Valid state) (pointer : ℕ)
    (bounded : 0 < pointer ∧ pointer ≤ state.count) :
    (descriptorHeap width heap state)[heap.size + 2 * (pointer - 1) + 1]'
      (by rw [descriptorHeap_size width heap state valid]; omega) =
      word width (entryAt state valid pointer bounded).position := by
  have bound : pointer - 1 < state.entries.reverse.length := by
    simp only [List.length_reverse, valid.count]; omega
  have field := fields_position state.entries.reverse (pointer - 1) bound
  simpa only [descriptorHeap, field, entryAt, Nat.add_assoc] using allocatedHeap_cell width heap
    (fields state.entries.reverse) (2 * (pointer - 1) + 1) (by rw [fields_length]; omega)

/-- This representation is built from the physically allocated heap. The route
function is the proof-only decoder of captured parent records, not runtime data. -/
def represented (width : ℕ) (heap : Array (Word width)) (state : Builder)
    (valid : Valid state) (dense : Dense state) (route : ℕ → LeafRoute)
    (decoded : Decodes state route) (countFits : state.count < 2 ^ width)
    (positionFits : ∀ entry ∈ state.entries, entry.position < 2 ^ width) :
    RouteDescriptors width (descriptorHeap width heap state) where
  base := heap.size
  count := state.count
  route := route
  sentinel := decoded.sentinel
  parentValid := by
    intro pointer bounded
    rw [descriptorHeap_size width heap state valid]
    omega
  positionValid := by
    intro pointer bounded
    rw [descriptorHeap_size width heap state valid]
    omega
  parentEarlier := by
    intro pointer bounded
    rw [descriptor_parent_word width heap state valid pointer bounded]
    have member := entryAt_mem state valid pointer bounded
    obtain ⟨positive, earlier, bound⟩ := valid.entries _ member
    rw [entryAt_id state valid dense pointer bounded] at earlier bound
    have parentFits : (entryAt state valid pointer bounded).parent < 2 ^ width := by omega
    simpa only [word, Nat.mod_eq_of_lt parentFits] using earlier
  cellRoute := by
    intro pointer bounded
    rw [descriptor_parent_word width heap state valid pointer bounded,
      descriptor_position_word width heap state valid pointer bounded]
    have member := entryAt_mem state valid pointer bounded
    obtain ⟨positive, earlier, bound⟩ := valid.entries _ member
    rw [entryAt_id state valid dense pointer bounded] at earlier bound
    have parentFits : (entryAt state valid pointer bounded).parent < 2 ^ width := by omega
    have posFits := positionFits _ member
    have identity := decoded.entries _ member
    rw [entryAt_id state valid dense pointer bounded] at identity
    simpa only [word, Nat.mod_eq_of_lt parentFits, Nat.mod_eq_of_lt posFits] using identity

/-- The representation keeps sentinel zero and the exact captured decoder. -/
theorem represented_route (width : ℕ) (heap : Array (Word width)) (state : Builder)
    (valid : Valid state) (dense : Dense state) (route : ℕ → LeafRoute)
    (decoded : Decodes state route) (countFits : state.count < 2 ^ width)
    (positionFits : ∀ entry ∈ state.entries, entry.position < 2 ^ width) :
    (represented width heap state valid dense route decoded countFits positionFits).route = route := rfl

/-- A single actual root scan supplies all descriptor premises; there is no
caller-supplied backing array or arbitrary identifier dictionary. -/
def sourceRepresented (width : ℕ) (heap : Array (Word width)) (graph : DAG n)
    (state : Builder) (valid : Valid state) (dense : Dense state)
    (route : ℕ → LeafRoute) (decoded : Decodes state route)
    (position : Fin graph.roots.length)
    (countFits : (scanRoot graph state position).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (scanRoot graph state position).entries, entry.position < 2 ^ width) :
    RouteDescriptors width (descriptorHeap width heap (scanRoot graph state position)) :=
  represented width heap (scanRoot graph state position)
    (scan_valid _ _ (beginRoot_valid state valid) _)
    (scanRoot_dense graph state dense position)
    (routeScan position.val (beginRoot state) route (cursorOps graph (graph.roots.get position) []))
    (scan_decodes _ _ (beginRoot_valid state valid) route ⟨decoded.sentinel, decoded.entries⟩ _)
    countFits positionFits

end Controller.Cost.ForestCursorMaterialize
