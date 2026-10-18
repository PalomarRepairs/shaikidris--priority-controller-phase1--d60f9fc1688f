module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroRootSelect

@[expose] public section

/-! Coordinate identifiers are appended once by fetched constant/allocate pairs and reused by every zero query. -/
namespace Controller.Cost.SharedCoordinateTable
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width : Nat) : List (Word width) → List (Instruction width 8)
  | [] => []
  | value :: rest => [.constant 1 value, .allocate 1] ++ code width rest

@[simp] theorem code_length (values : List (Word width)) : (code width values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [code, ih]; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (values : List (Word width)) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * values.length < 2 ^ width)
    (capacity : state.heap.size + values.length < 2 ^ width)
    (physical : SharedRootRead.BlockAt resident entry (code width values)) :
    ∃ final, Execution resident state final (2 * values.length) (state.liveWords + values.length) ∧
      final.heap = state.heap ++ values.toArray ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2 * values.length) ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  induction values generalizing state entry with
  | nil =>
    refine ⟨state, ?_, by simp, rfl, rfl, by simpa using position, running, rfl⟩
    simpa using Execution.refl (p := resident) state
  | cons value rest ih =>
    let first := state.advance.put 1 value
    let middle := { first.advance with heap := state.heap.push value }
    have constantFetch : resident[entry]? = some (.constant 1 value) := by simpa [code] using physical 0 (by simp [code])
    have allocateFetch : resident[entry + 1]? = some (.allocate 1) := by simpa [code] using physical 1 (by simp [code])
    have constantStep : programStep resident state = some first := by
      rw [fetched resident state entry _ position (by simp only [List.length_cons] at room; omega) constantFetch]
      simp [step, running, first]
    have firstPC : first.pc = word width (entry + 1) := by
      simpa [first, State.put] using advance_position state position (by simp only [List.length_cons] at room; omega)
    have allocateStep : programStep resident first = some middle := by
      rw [fetched resident first (entry + 1) _ firstPC (by simp only [List.length_cons] at room; omega) allocateFetch]
      simp [step, first, middle, State.put, State.advance, running,
        show state.heap.size < 2 ^ width from by simp only [List.length_cons] at capacity; omega]
    have middlePC : middle.pc = word width (entry + 2) := by
      simpa [middle, Nat.add_assoc] using advance_position first firstPC (by simp only [List.length_cons] at room; omega)
    have firstLive : first.liveWords = state.liveWords := rfl
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp [middle, first, State.advance, State.put, State.liveWords]; omega
    have pairTrace : Execution resident state middle 2 (state.liveWords + 1) := by
      have trace := Execution.cons constantStep (Execution.cons allocateStep (Execution.refl middle))
      simpa only [firstLive, middleLive, Nat.reduceAdd,
        Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + 1)] using trace
    have restBlock : SharedRootRead.BlockAt resident (entry + 2) (code width rest) := by
      intro offset valid
      have bound : offset < 2 * rest.length := by simpa using valid
      have fetchedRest := physical (2 + offset) (by simp [code]; omega)
      simpa [code, List.getElem_append_right, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fetchedRest
    obtain ⟨final, restTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalHead⟩ :=
      ih middle (entry + 2) middlePC running (by simp only [List.length_cons] at room; omega)
        (by simp only [middle, Array.size_push]; simp only [List.length_cons] at capacity; omega) restBlock
    have joined := pairTrace.append restTrace
    rw [middleLive, Nat.max_eq_right (by omega : state.liveWords + 1 ≤ state.liveWords + 1 + rest.length)] at joined
    refine ⟨final, ?_, ?_, finalStack, finalOutput, ?_, finalRunning, ?_⟩
    · convert joined using 1 <;> simp only [List.length_cons] <;> omega
    · rw [finalHeap]
      change state.heap.push value ++ rest.toArray = state.heap ++ (value :: rest).toArray
      rw [List.toArray_cons, Array.push_eq_append, Array.append_assoc]
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC
    · simpa [middle, first, State.advance, State.put] using finalHead

def words (width ambient : Nat) : List (Word width) := (List.finRange ambient).map (fun coordinate => word width coordinate.val)

@[simp] theorem words_length (width ambient : Nat) : (words width ambient).length = ambient := by simp [words]

theorem cell (heap : Array (Word width)) (coordinate : Fin ambient) :
    (heap ++ (words width ambient).toArray)[heap.size + coordinate.val]? = some (word width coordinate.val) := by
  simp [Array.getElem?_append, words]

open Controller.CNF Controller.Cost.ForestZeroEmit

def reference (base : Nat) (literal : Literal (Fin ambient)) : Reference ambient where
  slot := base + literal.1.val
  raw := literal.1.val
  activity := false
  coordinate := literal.1
  positive := literal.2

def rows (base : Nat) (clauses : List (List (Literal (Fin ambient)))) :
    List (List (Reference ambient)) := clauses.map (fun clause => clause.map (reference base))

theorem reference_stored (heap : Array (Word width)) (channels : Nat)
    (header : heap[0]? = some (word width channels)) (nonempty : 0 < heap.size)
    (literal : Literal (Fin ambient)) :
    StoredReference (heap ++ (words width ambient).toArray) channels (heap.size + ambient)
      (reference heap.size literal) := by
  constructor
  · simp
  · simp only [reference]; have := literal.1.isLt; omega
  · omega
  · exact cell heap literal.1
  · simpa [Array.getElem?_append, nonempty] using header
  · simp [reference]

theorem rows_stored (heap : Array (Word width)) (channels : Nat)
    (header : heap[0]? = some (word width channels)) (nonempty : 0 < heap.size)
    (clauses : List (List (Literal (Fin ambient)))) :
    ∀ item ∈ (rows heap.size clauses).flatten,
      StoredReference (heap ++ (words width ambient).toArray) channels (heap.size + ambient) item := by
  intro item member
  obtain ⟨row, rowMember, itemMember⟩ := List.mem_flatten.mp member
  obtain ⟨clause, clauseMember, rowEq⟩ := List.mem_map.mp rowMember
  rw [← rowEq] at itemMember
  obtain ⟨literal, literalMember, itemEq⟩ := List.mem_map.mp itemMember
  rw [← itemEq]
  exact reference_stored heap channels header nonempty literal

@[simp] theorem rows_coordinates (base : Nat) (clauses : List (List (Literal (Fin ambient)))) :
    (rows base clauses).map (fun row => row.map (fun item => (item.coordinate, item.positive))) = clauses := by
  simp [rows, reference, List.map_map, Function.comp_def]

@[simp] theorem originalRows_eq (base : Nat) (clauses : List (List (Literal (Fin ambient)))) :
    ForestZeroAssembly.originalRows (rows base clauses) = clauses := rows_coordinates base clauses

@[simp] theorem rows_length (base : Nat) (clauses : List (List (Literal (Fin ambient)))) :
    (rows base clauses).length = clauses.length := by simp [rows]

@[simp] theorem rows_literals (base : Nat) (clauses : List (List (Literal (Fin ambient)))) :
    (rows base clauses).flatten.length = clauses.flatten.length := by
  simp [rows, List.length_flatten, List.map_map, Function.comp_def]

theorem rows_stored_after_root (heap : Array (Word width)) (channels slot : Nat)
    (header : heap[0]? = some (word width channels)) (positive : 0 < slot)
    (slotValid : slot < heap.size) (value : Word width)
    (clauses : List (List (Literal (Fin ambient)))) :
    ∀ item ∈ (rows heap.size clauses).flatten,
      StoredReference ((heap ++ (words width ambient).toArray).set slot value (by simp; omega))
        channels (heap.size + ambient) item := by
  intro item member
  have stored := rows_stored heap channels header (by omega) clauses item member
  apply SharedZeroRootSelect.reference_preserved _ channels slot _ value item stored (by simp; omega) positive
  obtain ⟨row, rowMember, itemMember⟩ := List.mem_flatten.mp member
  obtain ⟨clause, clauseMember, rowEq⟩ := List.mem_map.mp rowMember
  rw [← rowEq] at itemMember
  obtain ⟨literal, literalMember, itemEq⟩ := List.mem_map.mp itemMember
  rw [← itemEq]
  simp only [reference]
  omega

end Controller.Cost.SharedCoordinateTable
