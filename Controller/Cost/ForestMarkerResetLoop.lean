module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestMarkerMachine

@[expose] public section

/-!
# Reusable touched-marker reset loop

Touched channel IDs are encoded as channel+1; zero is a terminal sentinel.
One fixed instruction block pops the next ID, tests the sentinel, computes its
marker address using a positive fixed offset, clears it, and branches back.
Register three stays zero, so loop termination uses no hidden count register.
Program construction, sentinel installation and the preceding touch phase are
separate operations. Encoded IDs and marker addresses must fit the word width.
-/
namespace Controller.Cost.ForestMarkerResetLoop

open Controller.Decoder Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestMarkerMachine

/-- Shared code independent of the number and values of touched IDs. -/
def resetLoopCode (width base offset : ℕ) : ForestCounter.Code width :=
  [.pop 0, .branchZero 0 (word width (base + 7)),
    .constant 1 (word width (offset - 1)), .add 0 0 1,
    .constant 2 (word width 0), .store 0 2, .branchZero 2 (word width base)]

@[simp] theorem resetLoopCode_length (width base offset : ℕ) :
    (resetLoopCode width base offset).length = 7 := rfl

/-- The sentinel is consumed by two genuine fetched instructions. -/
theorem sentinel_execution (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (oldAddress oldLoaded oldTemporary : Word width)
    (programFits : base + 7 < 2 ^ width)
    (block : BlockAt program base (resetLoopCode width base offset)) :
    Execution program
      ((counterState heap base oldAddress oldLoaded oldTemporary).frame [word width 0] [])
      (counterState heap (base + 7) (word width 0) oldLoaded oldTemporary)
      2 (6 + heap.size) := by
  have first : program[base]? = some (.pop 0) := by
    simpa [resetLoopCode] using block 0 (by simp)
  have second : program[base + 1]? = some (.branchZero 0 (word width (base + 7))) := by
    simpa [resetLoopCode] using block 1 (by simp)
  have firstStep := pop_transition program heap base oldAddress oldLoaded oldTemporary
    (word width 0) (by omega) first
  have secondStep := branch_transition program heap (base + 1) (base + 7) 0
    (word width 0) oldLoaded oldTemporary (by omega) second
  have zero : ((counterState heap (base + 1) (word width 0) oldLoaded oldTemporary).reg
      (0 : Fin 4)).val = 0 := by simp [counterState, word]
  rw [zero, ite_eq_left rfl] at secondStep
  have trace := Execution.cons firstStep (Execution.cons secondStep
    (Execution.refl (counterState heap (base + 7) (word width 0) oldLoaded oldTemporary)))
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero, Array.size_set] <;> omega

/-- One non-sentinel ID is cleared and control returns to the same shared code. -/
theorem entry_execution (program : Program width 4) (heap : Array (Word width))
    (base offset channel : ℕ) (oldAddress oldLoaded oldTemporary : Word width)
    (positiveOffset : 0 < offset) (programFits : base + 7 < 2 ^ width)
    (addressFits : offset + channel < 2 ^ width) (valid : offset + channel < heap.size)
    (block : BlockAt program base (resetLoopCode width base offset)) :
    Execution program
      ((counterState heap base oldAddress oldLoaded oldTemporary).frame [word width (channel + 1)] [])
      (counterState (heap.set (offset + channel) (word width 0)) base
        (word width (offset + channel)) (word width (offset - 1)) (word width 0))
      7 (6 + heap.size) := by
  have first : program[base]? = some (.pop 0) := by
    simpa [resetLoopCode] using block 0 (by simp)
  have second : program[base + 1]? = some (.branchZero 0 (word width (base + 7))) := by
    simpa [resetLoopCode] using block 1 (by simp)
  have third : program[base + 2]? = some (.constant 1 (word width (offset - 1))) := by
    simpa [resetLoopCode] using block 2 (by simp)
  have fourth : program[base + 3]? = some (.add 0 0 1) := by
    simpa [resetLoopCode] using block 3 (by simp)
  have fifth : program[base + 4]? = some (.constant 2 (word width 0)) := by
    simpa [resetLoopCode] using block 4 (by simp)
  have sixth : program[base + 5]? = some (.store 0 2) := by
    simpa [resetLoopCode] using block 5 (by simp)
  have seventh : program[base + 6]? = some (.branchZero 2 (word width base)) := by
    simpa [resetLoopCode] using block 6 (by simp)
  have idFits : channel + 1 < 2 ^ width := by omega
  have offsetFits : offset - 1 < 2 ^ width := by omega
  have firstStep := pop_transition program heap base oldAddress oldLoaded oldTemporary
    (word width (channel + 1)) (by omega) first
  have secondStep := branch_transition program heap (base + 1) (base + 7) 0
    (word width (channel + 1)) oldLoaded oldTemporary (by omega) second
  have idValue : ((counterState heap (base + 1) (word width (channel + 1))
      oldLoaded oldTemporary).reg (0 : Fin 4)).val = channel + 1 := by
    simp only [counterState]
    exact Nat.mod_eq_of_lt idFits
  rw [idValue, ite_eq_right (by omega : channel + 1 ≠ 0)] at secondStep
  have thirdStep := constant_loaded_transition program heap (base + 2) (word width (channel + 1))
    oldLoaded oldTemporary (word width (offset - 1)) (by omega) third
  have fourthStep := add_address_transition program heap (base + 3) (word width (channel + 1))
    (word width (offset - 1)) oldTemporary (by omega) fourth
  have sumWord : word width ((word width (channel + 1)).val + (word width (offset - 1)).val) =
      word width (offset + channel) := by
    rw [show (word width (channel + 1)).val = channel + 1 from Nat.mod_eq_of_lt idFits,
      show (word width (offset - 1)).val = offset - 1 from Nat.mod_eq_of_lt offsetFits]
    congr 1
    omega
  rw [sumWord] at fourthStep
  have fifthStep := increment_transition program heap (base + 4) 0 (word width (offset + channel))
    (word width (offset - 1)) oldTemporary (by omega) fifth
  have sixthStep := store_temporary_transition program heap (base + 5) (offset + channel)
    (word width (offset - 1)) (word width 0) (by omega) addressFits valid sixth
  have seventhStep := branch_transition program (heap.set (offset + channel) (word width 0))
    (base + 6) base 2 (word width (offset + channel)) (word width (offset - 1))
    (word width 0) (by omega) seventh
  have zero : ((counterState (heap.set (offset + channel) (word width 0)) (base + 6)
      (word width (offset + channel)) (word width (offset - 1)) (word width 0)).reg (2 : Fin 4)).val = 0 := by
    simp [counterState, word]
  rw [zero, ite_eq_left rfl] at seventhStep
  simp only [Nat.add_assoc] at secondStep thirdStep fourthStep fifthStep sixthStep seventhStep
  have trace := Execution.cons firstStep (Execution.cons secondStep (Execution.cons thirdStep
    (Execution.cons fourthStep (Execution.cons fifthStep (Execution.cons sixthStep
      (Execution.cons seventhStep (Execution.refl
        (counterState (heap.set (offset + channel) (word width 0)) base
          (word width (offset + channel)) (word width (offset - 1)) (word width 0)))))))))
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero, Array.size_set] <;> omega

def clearCell (width offset : ℕ) (heap : Array (Word width)) (coordinate : Channel n) : Array (Word width) :=
  if valid : offset + coordinate.val < heap.size then
    heap.set (offset + coordinate.val) (word width 0) valid else heap

@[simp] theorem clearCell_size (width offset : ℕ) (heap : Array (Word width))
    (coordinate : Channel n) : (clearCell width offset heap coordinate).size = heap.size := by
  unfold clearCell
  split <;> simp

def clearList (width offset : ℕ) (heap : Array (Word width)) (coordinates : List (Channel n)) :
    Array (Word width) := coordinates.foldl (clearCell width offset) heap

def encodedStack (width : ℕ) (coordinates : List (Channel n)) : List (Word width) :=
  coordinates.map (fun coordinate => word width (coordinate.val + 1)) ++ [word width 0]

/-- One fixed fetched loop processes every supplied runtime ID, then consumes its
sentinel. No instruction generation depends on the number of entries. -/
theorem list_execution (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (coordinates : List (Channel n))
    (oldAddress oldLoaded oldTemporary : Word width)
    (positiveOffset : 0 < offset) (programFits : base + 7 < 2 ^ width)
    (addresses : ∀ coordinate ∈ coordinates,
      offset + coordinate.val < heap.size ∧ offset + coordinate.val < 2 ^ width)
    (block : BlockAt program base (resetLoopCode width base offset)) :
    ∃ loaded temporary : Word width,
      Execution program
        ((counterState heap base oldAddress oldLoaded oldTemporary).frame (encodedStack width coordinates) [])
        (counterState (clearList width offset heap coordinates) (base + 7) (word width 0) loaded temporary)
        (7 * coordinates.length + 2) (6 + heap.size + coordinates.length) := by
  induction coordinates generalizing heap oldAddress oldLoaded oldTemporary with
  | nil =>
      refine ⟨oldLoaded, oldTemporary, ?_⟩
      simpa only [encodedStack, List.map_nil, List.nil_append, clearList, List.foldl_nil,
        List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
        sentinel_execution program heap base offset oldAddress oldLoaded oldTemporary programFits block
  | cons coordinate rest ih =>
      have valid := (addresses coordinate (by simp)).1
      have fits := (addresses coordinate (by simp)).2
      have first := (entry_execution program heap base offset coordinate.val oldAddress oldLoaded
        oldTemporary positiveOffset programFits fits valid block).frame (encodedStack width rest) []
      have later : ∀ current ∈ rest,
          offset + current.val < (clearCell width offset heap coordinate).size ∧
            offset + current.val < 2 ^ width := by
        intro current member
        simpa only [clearCell_size] using addresses current (by simp [member])
      obtain ⟨loaded, temporary, tail⟩ := ih (clearCell width offset heap coordinate)
        (word width (offset + coordinate.val)) (word width (offset - 1)) (word width 0) later
      have stepHeap : clearCell width offset heap coordinate =
          heap.set (offset + coordinate.val) (word width 0) valid := by
        simp only [clearCell, dite_eq_left valid]
      rw [stepHeap] at tail
      have joined := first.append tail
      refine ⟨loaded, temporary, ?_⟩
      have peakEq : max (6 + heap.size + ((encodedStack width rest).length + 0))
          (6 + (heap.set (offset + coordinate.val) (word width 0) valid).size + rest.length) =
          6 + heap.size + (coordinate :: rest).length := by
        simp only [encodedStack, List.length_append, List.length_map, List.length_cons,
          List.length_nil, Nat.add_zero, Array.size_set]
        omega
      simp only [List.length_nil] at joined
      rw [peakEq] at joined
      simpa only [State.frame, counterState, encodedStack, List.map_cons, List.cons_append, List.nil_append,
        List.singleton_append, clearList, List.foldl_cons, stepHeap, List.length_cons,
        Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using joined

/-- The reusable loop preserves an arbitrary trailing stack/output frame. -/
theorem list_execution_framed (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (coordinates : List (Channel n))
    (oldAddress oldLoaded oldTemporary : Word width) (stack output : List (Word width))
    (positiveOffset : 0 < offset) (programFits : base + 7 < 2 ^ width)
    (addresses : ∀ coordinate ∈ coordinates,
      offset + coordinate.val < heap.size ∧ offset + coordinate.val < 2 ^ width)
    (block : BlockAt program base (resetLoopCode width base offset)) :
    ∃ loaded temporary : Word width,
      Execution program
        ((counterState heap base oldAddress oldLoaded oldTemporary).frame
          (encodedStack width coordinates ++ stack) output)
        ((counterState (clearList width offset heap coordinates) (base + 7)
          (word width 0) loaded temporary).frame stack output)
        (7 * coordinates.length + 2)
        (6 + heap.size + coordinates.length + (stack.length + output.length)) := by
  obtain ⟨loaded, temporary, trace⟩ := list_execution program heap base offset coordinates
    oldAddress oldLoaded oldTemporary positiveOffset programFits addresses block
  refine ⟨loaded, temporary, ?_⟩
  simpa only [State.frame, List.nil_append, List.append_assoc] using trace.frame stack output

/-- Logical touched-list soundness implies zero markers after the actual indexed
stores. No channel-wide clear is needed. -/
theorem clearList_empty_stored (width offset : ℕ) (heap : Array (Word width))
    (state : ForestScopeMarkers.MarkState n)
    (well : ForestScopeMarkers.WellFormed state)
    (stored : ForestScopeMarkers.MarkersStored heap offset state) :
    ForestScopeMarkers.MarkersStored (clearList width offset heap state.touched) offset
      (ForestScopeMarkers.empty : ForestScopeMarkers.MarkState n) := by
  have claim : ∀ coordinates : List (Channel n), ∀ heap : Array (Word width),
      ∀ state : ForestScopeMarkers.MarkState n, state.touched = coordinates →
      ForestScopeMarkers.WellFormed state → ForestScopeMarkers.MarkersStored heap offset state →
      ForestScopeMarkers.MarkersStored (clearList width offset heap coordinates) offset
        (ForestScopeMarkers.empty : ForestScopeMarkers.MarkState n) := by
    intro coordinates
    induction coordinates with
    | nil =>
        intro heap state head well stored
        have stateEq : state = ForestScopeMarkers.empty := by
          apply ForestScopeMarkers.MarkState.ext
          · funext current
            apply Bool.eq_false_iff.mpr
            intro marked
            have present := (well.2 current).mp marked
            simpa [head] using present
          · exact head
        simpa only [clearList, List.foldl_nil, stateEq] using stored
    | cons coordinate rest ih =>
        intro heap state head well stored
        have nextWell := clearHead_wellFormed state coordinate rest head well
        have nextStored := clearHead_stored width offset heap state coordinate rest stored
        have valid := stored.valid coordinate
        have result := ih (heap.set (offset + coordinate.val) (word width 0) valid)
          (clearHead state coordinate rest) rfl nextWell nextStored
        simpa only [clearList, List.foldl_cons, clearCell, dite_eq_left valid] using result
  exact claim state.touched heap state rfl well stored

/-- Actual shared-code reset consumes exactly the logical touched IDs and its
sentinel, restores zero marker representation, and preserves trailing frames. -/
theorem loop_refines (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (state : ForestScopeMarkers.MarkState n)
    (oldAddress oldLoaded oldTemporary : Word width) (stack output : List (Word width))
    (well : ForestScopeMarkers.WellFormed state)
    (stored : ForestScopeMarkers.MarkersStored heap offset state)
    (positiveOffset : 0 < offset) (programFits : base + 7 < 2 ^ width)
    (addressFits : ∀ coordinate ∈ state.touched, offset + coordinate.val < 2 ^ width)
    (block : BlockAt program base (resetLoopCode width base offset)) :
    (∃ loaded temporary : Word width,
      Execution program
        ((counterState heap base oldAddress oldLoaded oldTemporary).frame
          (encodedStack width state.touched ++ stack) output)
        ((counterState (clearList width offset heap state.touched) (base + 7)
          (word width 0) loaded temporary).frame stack output)
        (7 * state.touched.length + 2)
        (6 + heap.size + state.touched.length + (stack.length + output.length))) ∧
    ForestScopeMarkers.MarkersStored (clearList width offset heap state.touched) offset
      (ForestScopeMarkers.empty : ForestScopeMarkers.MarkState n) := by
  exact ⟨list_execution_framed program heap base offset state.touched oldAddress oldLoaded oldTemporary
    stack output positiveOffset programFits (by
      intro coordinate present
      exact ⟨stored.valid coordinate, addressFits coordinate present⟩) block,
    clearList_empty_stored width offset heap state well stored⟩

theorem clearCell_outside (width offset : ℕ) (heap : Array (Word width))
    (coordinate : Channel n) (address : ℕ)
    (outside : ForestGuardRestore.Outside offset n address) :
    (clearCell width offset heap coordinate)[address]? = heap[address]? := by
  have different : offset + coordinate.val ≠ address := by
    have bounded := coordinate.isLt
    unfold ForestGuardRestore.Outside at outside
    omega
  by_cases valid : offset + coordinate.val < heap.size
  · simpa only [clearCell, dite_eq_left valid] using
      (Array.getElem?_set_ne (xs := heap) (v := word width 0) valid different)
  · simp only [clearCell, dite_eq_right valid]

theorem clearList_outside (width offset : ℕ) (heap : Array (Word width))
    (coordinates : List (Channel n)) (address : ℕ)
    (outside : ForestGuardRestore.Outside offset n address) :
    (clearList width offset heap coordinates)[address]? = heap[address]? := by
  induction coordinates generalizing heap with
  | nil => rfl
  | cons coordinate rest ih =>
      change (clearList width offset (clearCell width offset heap coordinate) rest)[address]? = _
      exact (ih (clearCell width offset heap coordinate)).trans
        (clearCell_outside width offset heap coordinate address outside)

/-- Zero marker representation and outside-cell equality determine the whole
heap, so disjoint persistent caller metadata can be reused. -/
theorem empty_region_heap_eq (width offset : ℕ) (initial final : Array (Word width))
    (initialStored : ForestScopeMarkers.MarkersStored initial offset (ForestScopeMarkers.empty : ForestScopeMarkers.MarkState n))
    (finalStored : ForestScopeMarkers.MarkersStored final offset (ForestScopeMarkers.empty : ForestScopeMarkers.MarkState n))
    (outside : ∀ address, ForestGuardRestore.Outside offset n address → final[address]? = initial[address]?) :
    final = initial := by
  apply Array.ext_getElem?
  intro address
  by_cases external : ForestGuardRestore.Outside offset n address
  · exact outside address external
  · have lower : offset ≤ address := by unfold ForestGuardRestore.Outside at external; omega
    have upper : address < offset + n := by unfold ForestGuardRestore.Outside at external; omega
    let coordinate : Channel n := ⟨address - offset, by omega⟩
    have location : offset + coordinate.val = address := by dsimp only [coordinate]; omega
    have first : initial[address]? = some (word width 0) := by
      rw [← location, Array.getElem?_eq_getElem (initialStored.valid coordinate), initialStored.held coordinate]
      rfl
    have last : final[address]? = some (word width 0) := by
      rw [← location, Array.getElem?_eq_getElem (finalStored.valid coordinate), finalStored.held coordinate]
      rfl
    exact last.trans first.symm

theorem clearList_heap_restore (width offset : ℕ) (initial heap : Array (Word width))
    (state : ForestScopeMarkers.MarkState n) (well : ForestScopeMarkers.WellFormed state)
    (initialStored : ForestScopeMarkers.MarkersStored initial offset (ForestScopeMarkers.empty : ForestScopeMarkers.MarkState n))
    (stored : ForestScopeMarkers.MarkersStored heap offset state)
    (outside : ∀ address, ForestGuardRestore.Outside offset n address → heap[address]? = initial[address]?) :
    clearList width offset heap state.touched = initial := by
  exact empty_region_heap_eq width offset initial (clearList width offset heap state.touched)
    initialStored (clearList_empty_stored width offset heap state well stored) (by
      intro address external
      exact (clearList_outside width offset heap state.touched address external).trans (outside address external))

end Controller.Cost.ForestMarkerResetLoop
